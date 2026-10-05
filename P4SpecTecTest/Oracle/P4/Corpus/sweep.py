#!/usr/bin/env python3
"""Differential sweep of the pinned full-P4 corpus through both Lean legs, in parallel.

Every canonical candidate of the committed inventory is observed with the corpus-v2 probe
(two independent upstream sessions), then checked by the reference-interpreter worker and
the generated-library worker. A capture or worker that times out, crashes or exceeds a
bound is recorded as that, never as a verdict.

This is the fast feedback loop, not the durable campaign: observations (and failed captures)
are cached under an identity of pins, probe, harness sources and limits, but nothing is fsynced, locked or resumable mid-case,
and upstream's CLI is not cross-checked. `shard.py` keeps those guarantees for one leg.
"""

import argparse
import collections
import concurrent.futures
import gzip
import json
import os
from pathlib import Path
import queue
import select
import subprocess
import tempfile
import threading
import time

import campaign
import contract
import inventory


ROOT = inventory.ROOT
CORPUS = ROOT / "P4SpecTecTest/Oracle/P4/Corpus"
LEGS = {"interpreter": ["p4-corpus-worker", str(ROOT / "exports/p4.al.json")],
        "generated": ["p4-corpus-worker-gen"]}
AGREEING = {"matched", "matched-public-failure", "syntax-only"}
# Capture failures that only say a stated bound was reached; any other kind is a defect.
BOUNDS = {"oversized", "timeout"}
# What a cached observation's bytes depend on, besides pins, probe and limits.
HARNESS = ("P4SpecTecTest/Oracle/P4/Corpus/sweep.py", "P4SpecTecTest/Oracle/P4/Corpus/campaign.py",
           "P4SpecTecTest/Oracle/P4/Corpus/contract.py",
           "P4SpecTecTest/Oracle/P4/Corpus/inventory.py",
           "P4SpecTecTest/Oracle/P4/Replay/capture.py", "scripts/oracle_build.py")


class Worker:
    """The corpus-v2 worker protocol for a chosen executable and response deadline."""

    def __init__(self, command, timeout):
        self.timeout = timeout
        self.stderr = tempfile.TemporaryFile()
        self.process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=self.stderr,
                                        start_new_session=True)
        self.buffer = b""
        self.cases = 0
        try:
            if self.line() != {"ready": 2}:
                raise campaign.HarnessFailure("worker-protocol", "worker readiness differs")
        except BaseException:
            self.kill()
            raise

    def line(self):
        deadline = time.monotonic() + self.timeout
        while b"\n" not in self.buffer:
            if time.monotonic() > deadline:
                raise campaign.HarnessFailure("worker-timeout", "worker exceeded deadline")
            if os.fstat(self.stderr.fileno()).st_size > 65536:
                raise campaign.HarnessFailure("worker-oversized", "worker stderr exceeded bound")
            ready, _, _ = select.select([self.process.stdout], [], [], 0.1)
            if ready:
                chunk = os.read(self.process.stdout.fileno(), 8192)
                if not chunk:
                    raise campaign.HarnessFailure(
                        "worker-crash", f"worker stdout closed: {self.process.poll()}")
                self.buffer += chunk
                if len(self.buffer) > 8192:
                    raise campaign.HarnessFailure(
                        "worker-oversized", "worker response exceeded bound")
        line, self.buffer = self.buffer.split(b"\n", 1)
        return contract.strict_json(line)

    def case(self, path):
        self.process.stdin.write(str(path).encode("utf-8") + b"\n")
        self.process.stdin.flush()
        self.cases += 1
        return self.line()

    def kill(self):
        campaign.terminate(self.process)
        for stream in (self.process.stdin, self.process.stdout, self.stderr):
            try:
                stream.close()
            except OSError:
                pass


def observe(case, adapter, executable, upstream, p4c, limit, timeout):
    """Two independent upstream sessions of one candidate, validated, as encoded bytes."""
    program = p4c / case["path"].removeprefix("p4c/")
    if campaign.file_digest(program) != case["sha256"]:
        raise ValueError("case source differs from the inventory")
    runs = {}
    for relation in contract.RELATIONS:
        code, out, _, _ = campaign.bounded(
            [str(executable), str(upstream / "spec"), str(p4c / "p4include"), str(program),
             relation], timeout=timeout, limit=limit)
        if code:
            raise campaign.HarnessFailure("oracle-crash", f"oracle exited {code}")
        runs[relation] = contract.strict_json(out)
    value = {"schemaVersion": contract.SCHEMA, "name": case["path"],
             **contract.observation(runs, adapter)}
    data = inventory.encode(value)
    if len(data) > limit:
        raise campaign.HarnessFailure("oversized", "encoded case exceeds byte bound")
    return data


def capture(candidates, directory, adapter, executable, upstream, p4c, limit, timeout, jobs):
    """Observe every candidate not already cached; a failure is a record, not a case."""
    def one(item):
        index, case = item
        stem = directory / f"{index:04d}"
        done, failed = stem.with_suffix(".json.gz"), stem.with_suffix(".err.json")
        if done.exists() or failed.exists():
            return None
        try:
            data = observe(case, adapter, executable, upstream, p4c, limit, timeout)
            partial = stem.with_suffix(".tmp")
            partial.write_bytes(gzip.compress(data, mtime=0))
            partial.rename(done)
            return None
        except Exception as error:  # every failure is a record; only bounds are excusable
            kind = getattr(error, "kind", "invalid-artifact" if isinstance(error, ValueError)
                           else "harness-error")
            record = {"name": case["path"], "kind": kind,
                      "message": (str(error) or type(error).__name__)[:2000]}
            failed.write_text(json.dumps(record, sort_keys=True) + "\n")
            return f"{case['path']}: capture {record['kind']}"

    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        for message in pool.map(one, enumerate(candidates)):
            if message:
                print(f"[p4-sweep] {message}", flush=True)


def run_leg(label, command, directory, timeout, jobs, recycle=campaign.MAX_WORKER_CASES):
    """One verdict or failure record per cached observation, by candidate index."""
    pending = queue.Queue()
    for path in sorted(directory.glob("*.json.gz")):
        pending.put((int(path.name.split(".")[0]), path))
    records = {}
    lock = threading.Lock()

    def loop():
        worker = None
        try:
            with tempfile.TemporaryDirectory(prefix="p4-sweep-") as scratch:
                case_path = Path(scratch) / "case.json"
                while True:
                    try:
                        index, path = pending.get_nowait()
                    except queue.Empty:
                        break
                    record = {"name": path.name}
                    started = time.monotonic()
                    try:
                        data = gzip.decompress(path.read_bytes())
                        name = json.loads(data)["name"]
                        record["name"] = name
                        case_path.write_bytes(data)
                        if worker is None or worker.cases >= recycle:
                            if worker is not None:
                                worker.kill()
                                worker = None
                            worker = Worker(command, timeout)
                        answer = worker.case(case_path)
                        if isinstance(answer, dict) and set(answer) == {"error"}:
                            record["failure"] = {"kind": "worker-error",
                                                 "message": str(answer["error"])}
                        else:
                            record["relations"] = campaign.verdict(answer, name)["relations"]
                    except Exception as error:  # a lost record would hide the case
                        kind = getattr(error, "kind", "invalid-artifact"
                                       if isinstance(error, ValueError) else "harness-error")
                        record["failure"] = {"kind": kind,
                                             "message": str(error) or type(error).__name__}
                        if worker is not None:
                            worker.kill()
                            worker = None
                    record["seconds"] = round(time.monotonic() - started, 3)
                    with lock:
                        records[index] = record
                        if not agrees(record):
                            print(f"[p4-sweep] {label}: {record['name']}: {describe(record)}",
                                  flush=True)
        finally:
            if worker is not None:
                worker.kill()

    threads = [threading.Thread(target=loop) for _ in range(jobs)]
    for thread in threads:
        thread.start()
    for thread in threads:
        thread.join()
    return records


def statuses(record):
    """The relation statuses of a verdict record, in relation order; None for a failure."""
    if "relations" not in record:
        return None
    return tuple(record["relations"][name]["status"] for name in contract.RELATIONS)


def agrees(record):
    """Agreement with upstream on both relations; unsupported and failed cases do not."""
    found = statuses(record)
    return found is not None and all(status in AGREEING for status in found)


def describe(record):
    if "failure" in record:
        return f"{record['failure']['kind']}: {record['failure']['message'][:200]}"
    return ", ".join(f"{name} {relation['status']} ({relation['leanClass']}) "
                     f"{relation['message'][:80]}".strip()
                     for name, relation in record["relations"].items())


def summarize(candidates, unobserved, legs):
    """Account for every candidate exactly once per leg; nothing is dropped as unsupported."""
    result = {"candidates": len(candidates), "unobserved": unobserved, "legs": {}}
    observed = len(candidates) - len(unobserved)
    for label, records in legs.items():
        tally = collections.Counter()
        other = []
        for index in sorted(records):
            record = records[index]
            found = statuses(record)
            key = "failure:" + record["failure"]["kind"] if found is None else ",".join(found)
            tally[key] += 1
            if not agrees(record):
                other.append({"name": record["name"], "outcome": describe(record)})
        if len(records) != observed:
            raise ValueError(f"{label}: {len(records)} records for {observed} observations")
        result["legs"][label] = {"statuses": dict(sorted(tally.items())),
                                 "agreeing": observed - len(other), "other": other,
                                 "seconds": round(sum(r["seconds"] for r in records.values()))}
    return result


def verdict(summary, require_all):
    """Zero only when at least one case was evaluated, every evaluated case agrees on every
    leg, and every unobserved candidate merely reached a stated bound; with `require_all`,
    also only when every candidate was observed."""
    unobserved = summary["unobserved"]
    clean = all(not leg["other"] for leg in summary["legs"].values())
    evaluated = summary["candidates"] > len(unobserved)
    bounded = all(item["kind"] in BOUNDS for item in unobserved)
    return 0 if clean and evaluated and bounded and not (require_all and unobserved) else 1


def identity(upstream, p4c, executable, limit, timeout):
    """What a cached observation depends on; a change discards the cache."""
    manifest = contract.strict_json(inventory.MANIFEST.read_bytes())
    return {"schemaVersion": 1, "inventorySha256": manifest["inventorySha256"],
            "upstreamRevision": manifest["upstreamRevision"],
            "p4cRevision": manifest["p4cRevision"],
            "probeSha256": campaign.file_digest(executable),
            "probeSourceSha256": campaign.file_digest(CORPUS / "probe.ml"),
            "harnessSha256": {path: campaign.file_digest(ROOT / path) for path in HARNESS},
            "roots": {"upstream": str(upstream), "p4c": str(p4c)},
            "maxCaseBytes": limit, "captureTimeoutSeconds": timeout}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--p4c", type=Path, required=True)
    parser.add_argument("--out", type=Path, default=ROOT / ".artifacts/p4-corpus-sweep")
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--max-case-bytes", type=int, default=1024 * 1024 * 1024)
    parser.add_argument("--capture-timeout", type=int, default=600)
    parser.add_argument("--worker-timeout", type=int, default=1800)
    parser.add_argument("--require-all", action="store_true",
                        help="fail when a candidate could not be observed within the bounds")
    parser.add_argument("--retry-unobserved", action="store_true",
                        help="capture again the candidates whose earlier capture failed")
    args = parser.parse_args()
    if not args.upstream.is_absolute() or not args.p4c.is_absolute():
        parser.error("--upstream and --p4c must be absolute")
    upstream, p4c = args.upstream.resolve(), args.p4c.resolve()
    check = campaign.load("p4_check", ROOT / "P4SpecTecTest/Oracle/P4/Replay/check.py")
    adapter = check.load_export()
    adapter.revision_guard(upstream)
    check.p4c_pin_guard(upstream, p4c)
    manifest = inventory.build(p4c, upstream)
    if manifest != contract.strict_json(inventory.MANIFEST.read_bytes()):
        raise SystemExit("[p4-sweep] inventory differs from the pinned corpus")
    candidates = inventory.shard(manifest, 0, 1)
    for command in (
            ["python3", str(ROOT / "scripts/spec-snapshot.py"), "unpack",
             str(ROOT / "exports/p4.al.json")],
            ["lake", "exe", "p4spectec-gen", "exports/p4.al.json", "--lib", "P4Spec", "--update"],
            ["python3", str(ROOT / "scripts/generated-manifest.py"), "--check", "P4Spec",
             str(ROOT / "P4Spec.manifest.json")],
            ["lake", "build", "--wfail", "p4-corpus-worker", "p4-corpus-worker-gen"]):
        subprocess.run(command, cwd=ROOT, check=True)
    executable = adapter.compile_probe(upstream, probe=CORPUS / "probe.ml",
                                       scratch=ROOT / ".artifacts/p4-corpus-probe")
    observations = args.out / "observations"
    observations.mkdir(parents=True, exist_ok=True)
    expected = identity(upstream, p4c, executable, args.max_case_bytes, args.capture_timeout)
    recorded = args.out / "identity.json"
    if not recorded.exists() or json.loads(recorded.read_text()) != expected:
        for stale in observations.iterdir():
            stale.unlink()
        recorded.write_text(json.dumps(expected, indent=1, sort_keys=True) + "\n")
    if args.retry_unobserved:
        for failed in observations.glob("*.err.json"):
            failed.unlink()
    started = time.monotonic()
    capture(candidates, observations, adapter, executable, upstream, p4c,
            args.max_case_bytes, args.capture_timeout, args.jobs)
    unobserved = [json.loads(path.read_text())
                  for path in sorted(observations.glob("*.err.json"))]
    def workers():
        return {label: campaign.file_digest(ROOT / ".lake/build/bin" / command[0])
                for label, command in LEGS.items()}

    digests = workers()
    legs = {}
    for label, command in LEGS.items():
        command = [str(ROOT / ".lake/build/bin" / command[0]), *command[1:],
                   "--max-case-bytes", str(args.max_case_bytes)]
        legs[label] = run_leg(label, command, observations, args.worker_timeout, args.jobs)
    if workers() != digests:
        raise SystemExit("[p4-sweep] a worker executable changed during the sweep")
    summary = summarize(candidates, unobserved, legs)
    summary["identity"] = {**expected, "workerTimeoutSeconds": args.worker_timeout,
                           "workers": digests, "jobs": args.jobs,
                           "maxWorkerCases": campaign.MAX_WORKER_CASES}
    summary["elapsedSeconds"] = round(time.monotonic() - started)
    (args.out / "summary.json").write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
    for label, leg in summary["legs"].items():
        print(f"[p4-sweep] {label}: {leg['agreeing']} of {summary['candidates']} candidates "
              f"agree with upstream; {leg['statuses']}")
    print(f"[p4-sweep] unobserved: {len(unobserved)} "
          f"{[(item['name'], item['kind']) for item in unobserved]}")
    return verdict(summary, args.require_all)


if __name__ == "__main__":
    raise SystemExit(main())
