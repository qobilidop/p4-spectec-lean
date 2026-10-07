#!/usr/bin/env python3
"""Replay every pinned STF session of a target through both Lean legs, against upstream.

The candidates are the P4-STF pairs upstream's own simulator test collects for the target
(`Util.Test.collect_test_pairs`: every p4c sample including the target's model, paired with
the STF files of the same base name in the same directory, less the pairs its static and
dynamic exclusion manifests name) and, for v1model, upstream's regression simulator
programs. Each is observed once by the session probe (upstream's own `run_stf_test` with an
observing pipe of the target) and cached under an identity of pins, probe, harness and
bounds; the session worker then replays the cached observations on the reference
interpreter and the generated library.

The sweep passes only when every candidate was observed, upstream passed every session (as
its expectation files record), and both legs match every event of every session: the
initialization, every packet's transmissions, contexts, architecture states and
fresh-identifier counters, and every control-plane change.
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
import sys
import tempfile
import threading
import time

sys.path.insert(0, str(Path(__file__).resolve().parent.parent / "Corpus"))
import campaign  # noqa: E402
import contract  # noqa: E402
import inventory  # noqa: E402


ROOT = inventory.ROOT
SESSIONS = ROOT / "P4SpecTecTest/Oracle/P4/Sessions"
CORPUS = ROOT / "P4SpecTecTest/Oracle/P4/Corpus"
SAMPLES = "testdata/p4_16_samples"
REGRESSION = "testdata/regression/sim"
# The targets, each with the include lines `collect_test_pairs` selects its programs by
# and the directory of patched sources upstream's simulator test passes for it, if any
# (`p4spec/test/sim/dune`: v1model has one, eBPF none).
ARCHES = {
    "v1model": {"includes": (b"#include <v1model.p4>", b'#include "v1model.p4"'),
                "patches": "patches/v1model"},
    "ebpf": {"includes": (b"#include <ebpf_model.p4>", b'#include "ebpf_model.p4"'),
             "patches": None},
}
HARNESS = ("P4SpecTecTest/Oracle/P4/Sessions/sessions.py",
           "P4SpecTecTest/Oracle/P4/Corpus/campaign.py",
           "P4SpecTecTest/Oracle/P4/Corpus/contract.py",
           "P4SpecTecTest/Oracle/P4/Corpus/inventory.py",
           "P4SpecTecTest/Oracle/P4/Replay/capture.py", "scripts/oracle_build.py")
LEGS = ("interpreter", "generated")
BOUNDS = {"oversized", "timeout"}


def collect_with_basedir(directory, suffix):
    """Mirror `Util.Filesys.collect_files_with_basedir`: sorted, recursive, skipping
    `include` directories, as paths relative to the directory."""
    result = []

    def walk(reldir):
        base = directory / reldir if reldir else directory
        for name in sorted(os.listdir(base)):
            path = base / name
            relpath = f"{reldir}/{name}" if reldir else name
            if path.is_dir() and name != "include":
                walk(relpath)
            elif relpath.endswith(suffix):
                result.append(relpath)

    walk("")
    return result


def base(path, suffix):
    """Mirror `Util.Filesys.base`."""
    name = path.rsplit("/", 1)[-1]
    return name[:-len(suffix)] if name.endswith(suffix) else name


def dirname(path):
    """Mirror OCaml's `Filename.dirname` on a relative path."""
    return path.rsplit("/", 1)[0] if "/" in path else "."


def p4_matches_stf(p4, stf):
    """Mirror `Util.Test.p4_matches_stf`."""
    return base(p4, ".p4") == dirname(stf) or (
        dirname(p4) == dirname(stf) and base(p4, ".p4") == base(stf, ".stf"))


def includes_arch(path, arch):
    """Whether the program includes the target's model, as upstream selects its tests."""
    text = path.read_bytes()
    return any(line in text for line in ARCHES[arch]["includes"])


def excluded_paths(upstream):
    """Every static and dynamic exclusion reference, as `collect_excludes` reads them."""
    references = set()
    for kind in ("static", "dynamic"):
        for path in inventory.collect_files(upstream / "excludes" / kind, ".exclude"):
            for _, entry in inventory.exclude_lines(path.read_bytes()):
                references.add(entry)
    return references


def p4c_pairs(p4c, upstream, arch):
    """Mirror `collect_test_pairs ARCH` over the p4c samples: pairs with their exclusion,
    in upstream's order. A patch whose base name matches a sample is an error: none applies
    at this pin, and a patched source would need its own identity."""
    samples = p4c / SAMPLES
    p4s = [p for p in collect_with_basedir(samples, ".p4") if includes_arch(samples / p, arch)]
    stfs = collect_with_basedir(samples, ".stf")
    patched = set()
    if ARCHES[arch]["patches"]:
        patches = upstream / ARCHES[arch]["patches"]
        patched = {base(p, ".p4") for p in collect_with_basedir(patches, ".p4")} | {
            base(s, ".stf") for s in collect_with_basedir(patches, ".stf")}
    excluded = excluded_paths(upstream)
    pairs = []
    for p4 in p4s:
        for stf in stfs:
            if not p4_matches_stf(p4, stf):
                continue
            if base(p4, ".p4") in patched or base(stf, ".stf") in patched:
                raise ValueError(f"a {arch} patch applies to {p4}; patched sources are not supported")
            program, test = f"p4c/{SAMPLES}/{p4}", f"p4c/{SAMPLES}/{stf}"
            pairs.append({"program": program, "stf": test,
                          "programSha256": campaign.file_digest(samples / p4),
                          "stfSha256": campaign.file_digest(samples / stf),
                          "excluded": program in excluded or test in excluded})
    if not pairs:
        raise ValueError(f"no {arch} sample pairs")
    return pairs


def regression_pairs(upstream, arch):
    """Upstream's regression simulator programs with their STF files, by name, which its
    simulator test runs for v1model only, with the v1model patch directory; every program
    must have an STF file, and none may be patched."""
    if arch != "v1model":
        return []
    directory = upstream / REGRESSION
    if directory.is_symlink() or not directory.is_dir():
        raise ValueError("missing regression simulator directory")
    patches = upstream / ARCHES[arch]["patches"]
    patched = {base(p, ".p4") for p in collect_with_basedir(patches, ".p4")} | {
        base(s, ".stf") for s in collect_with_basedir(patches, ".stf")}
    pairs = []
    for p4 in sorted(directory.glob("*.p4")):
        stf = p4.with_suffix(".stf")
        if p4.is_symlink() or not p4.is_file() or stf.is_symlink() or not stf.is_file():
            raise ValueError(f"regression program without a regular STF file: {p4.name}")
        if p4.stem in patched:
            raise ValueError(f"a {arch} patch applies to {p4.name}; patched sources are not supported")
        pairs.append({"program": f"upstream/{REGRESSION}/{p4.name}",
                      "stf": f"upstream/{REGRESSION}/{stf.name}",
                      "programSha256": campaign.file_digest(p4),
                      "stfSha256": campaign.file_digest(stf), "excluded": False})
    if not pairs:
        raise ValueError("no regression simulator programs")
    return pairs


def source(path, upstream, p4c):
    """A candidate file under the p4c or the upstream checkout."""
    root, _, relative = path.partition("/")
    roots = {"p4c": p4c, "upstream": upstream}
    if root not in roots or any(part in ("", ".", "..") for part in relative.split("/")):
        raise ValueError(f"candidate outside the known roots: {path}")
    return roots[root] / relative


def observe(case, executable, upstream, p4c, limit, timeout, arch):
    """One upstream session, as the probe's encoded observation."""
    program, stf = source(case["program"], upstream, p4c), source(case["stf"], upstream, p4c)
    if (campaign.file_digest(program) != case["programSha256"]
            or campaign.file_digest(stf) != case["stfSha256"]):
        raise ValueError("case source differs from its recorded digest")
    code, out, _, _ = campaign.bounded(
        [str(executable), arch, str(upstream / "spec"), str(p4c / "p4include"), str(program),
         str(stf)],
        timeout=timeout, limit=limit)
    if code:
        raise campaign.HarnessFailure("oracle-crash", f"oracle exited {code}")
    lines = [line for line in out.split(b"\n") if line.startswith(b"OBSERVATION ")]
    if len(lines) != 1:
        raise campaign.HarnessFailure("oracle-crash", "missing or repeated observation")
    observed = contract.strict_json(lines[0][len(b"OBSERVATION "):])
    data = inventory.encode({"name": case["stf"], "program": case["program"], **observed})
    if len(data) > limit:
        raise campaign.HarnessFailure("oversized", "encoded session exceeds byte bound")
    return data


def capture(candidates, directory, executable, upstream, p4c, limit, timeout, jobs, arch):
    """Observe every candidate not already cached; a failure is a record, not a case."""
    def one(item):
        index, case = item
        stem = directory / f"{index:04d}"
        done, failed = stem.with_suffix(".json.gz"), stem.with_suffix(".err.json")
        if done.exists() or failed.exists():
            return None
        try:
            data = observe(case, executable, upstream, p4c, limit, timeout, arch)
            partial = stem.with_suffix(".tmp")
            partial.write_bytes(gzip.compress(data, mtime=0))
            partial.rename(done)
            return None
        except Exception as error:  # every failure is a record; only bounds are excusable
            kind = getattr(error, "kind", "invalid-artifact" if isinstance(error, ValueError)
                           else "harness-error")
            record = {"name": case["stf"], "kind": kind,
                      "message": (str(error) or type(error).__name__)[:2000]}
            failed.write_text(json.dumps(record, sort_keys=True) + "\n")
            return f"{case['stf']}: capture {record['kind']}"

    with concurrent.futures.ThreadPoolExecutor(jobs) as pool:
        for message in pool.map(one, enumerate(candidates)):
            if message:
                print(f"[p4-sessions] {message}", flush=True)


class Worker:
    """The session worker protocol: both legs' verdicts per cached observation."""

    def __init__(self, command, timeout):
        self.timeout = timeout
        self.stderr = tempfile.TemporaryFile()
        self.process = subprocess.Popen(command, cwd=ROOT, stdin=subprocess.PIPE,
                                        stdout=subprocess.PIPE, stderr=self.stderr,
                                        start_new_session=True)
        self.buffer = b""
        self.cases = 0
        try:
            if self.line() != {"ready": 1}:
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
                if len(self.buffer) > 65536:
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


STATUSES = {"matched", "upstream-runtimeFail", "upstream-syntaxFail", "unrepresentable-input",
            "exhausted", "invalid-artifact", "counter-disagreement", "state-disagreement",
            "packet-disagreement", "outcome-disagreement"}


def verdict_record(answer, name):
    """A worker answer, validated: both legs with a known status."""
    if (not isinstance(answer, dict) or set(answer) != {"legs"}
            or not isinstance(answer["legs"], dict) or set(answer["legs"]) != set(LEGS)):
        raise ValueError(f"malformed worker answer for {name}")
    for leg in answer["legs"].values():
        if (not isinstance(leg, dict) or set(leg) != {"status", "message"}
                or leg["status"] not in STATUSES or not isinstance(leg["message"], str)):
            raise ValueError(f"malformed leg verdict for {name}")
    return answer["legs"]


def run_workers(command, directory, timeout, jobs, recycle=campaign.MAX_WORKER_CASES):
    """One record per cached observation, by candidate index."""
    pending = queue.Queue()
    for path in sorted(directory.glob("*.json.gz")):
        pending.put((int(path.name.split(".")[0]), path))
    records = {}
    lock = threading.Lock()

    def loop():
        worker = None
        try:
            with tempfile.TemporaryDirectory(prefix="p4-sessions-") as scratch:
                case_path = Path(scratch) / "session.json"
                while True:
                    try:
                        index, path = pending.get_nowait()
                    except queue.Empty:
                        break
                    record = {"name": path.name}
                    started = time.monotonic()
                    try:
                        data = gzip.decompress(path.read_bytes())
                        record["name"] = json.loads(data)["name"]
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
                            record["legs"] = verdict_record(answer, record["name"])
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
                        if not all_matched(record):
                            print(f"[p4-sessions] {record['name']}: {describe(record)}",
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


def all_matched(record):
    return "legs" in record and all(leg["status"] == "matched" for leg in record["legs"].values())


def describe(record):
    if "failure" in record:
        return f"{record['failure']['kind']}: {record['failure']['message'][:200]}"
    return "; ".join(f"{label} {leg['status']} {leg['message'][:120]}".strip()
                     for label, leg in record["legs"].items())


def summarize(candidates, unobserved, records):
    """Account for every candidate exactly once; nothing is dropped as unsupported."""
    observed = len(candidates) - len(unobserved)
    if len(records) != observed:
        raise ValueError(f"{len(records)} records for {observed} observations")
    tally = {label: collections.Counter() for label in LEGS}
    other = []
    for index in sorted(records):
        record = records[index]
        if "failure" in record:
            for label in LEGS:
                tally[label]["failure:" + record["failure"]["kind"]] += 1
        else:
            for label in LEGS:
                tally[label][record["legs"][label]["status"]] += 1
        if not all_matched(record):
            other.append({"name": record["name"], "outcome": describe(record)})
    return {"candidates": len(candidates), "unobserved": unobserved,
            "statuses": {label: dict(sorted(counts.items())) for label, counts in tally.items()},
            "matched": observed - len(other), "other": other,
            "seconds": round(sum(r["seconds"] for r in records.values()))}


def verdict(summary):
    """Zero only when every candidate was observed and matched on both legs."""
    return 0 if not summary["unobserved"] and not summary["other"] and summary["candidates"] else 1


def identity(upstream, p4c, executable, limit, timeout, candidates, arch):
    manifest = contract.strict_json(inventory.MANIFEST.read_bytes())
    return {"schemaVersion": 1, "set": f"{arch}-sessions", "arch": arch,
            "candidatesSha256": inventory.digest(inventory.encode(candidates)),
            "upstreamRevision": manifest["upstreamRevision"], "p4cRevision": manifest["p4cRevision"],
            "probeSha256": campaign.file_digest(executable),
            "probeSourceSha256": campaign.file_digest(SESSIONS / "probe.ml"),
            "harnessSha256": {path: campaign.file_digest(ROOT / path) for path in HARNESS},
            "roots": {"upstream": str(upstream), "p4c": str(p4c)},
            "maxCaseBytes": limit, "captureTimeoutSeconds": timeout}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--p4c", type=Path, required=True)
    parser.add_argument("--arch", choices=sorted(ARCHES), default="v1model")
    parser.add_argument("--out", type=Path, default=ROOT / ".artifacts/p4-sessions-sweep",
                        help="observations and the summary go under its ARCH subdirectory")
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--max-case-bytes", type=int, default=1024 * 1024 * 1024)
    parser.add_argument("--capture-timeout", type=int, default=1800)
    parser.add_argument("--worker-timeout", type=int, default=3600)
    parser.add_argument("--retry-unobserved", action="store_true")
    parser.add_argument("--only", help="a substring of candidate STF paths to restrict the sweep to")
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
        raise SystemExit("[p4-sessions] inventory differs from the pinned corpus")
    arch = args.arch
    out = args.out / arch
    pairs = p4c_pairs(p4c, upstream, arch)
    excluded = [pair for pair in pairs if pair["excluded"]]
    regression = regression_pairs(upstream, arch)
    candidates = [pair for pair in pairs if not pair["excluded"]] + regression
    if args.only:
        candidates = [c for c in candidates if args.only in c["stf"]]
    for command in (
            ["python3", str(ROOT / "scripts/spec-snapshot.py"), "unpack",
             str(ROOT / "exports/p4.al.json")],
            ["lake", "exe", "p4spectec-gen", "exports/p4.al.json", "--lib", "P4Spec", "--update"],
            ["python3", str(ROOT / "scripts/generated-manifest.py"), "--check", "P4Spec",
             str(ROOT / "P4Spec.manifest.json")],
            ["lake", "build", "--wfail", "p4-sessions-check"]):
        subprocess.run(command, cwd=ROOT, check=True)
    executable = adapter.compile_probe(upstream, probe=SESSIONS / "probe.ml",
                                       scratch=ROOT / ".artifacts/p4-sessions-probe")
    observations = out / "observations"
    observations.mkdir(parents=True, exist_ok=True)
    expected = identity(upstream, p4c, executable, args.max_case_bytes, args.capture_timeout,
                        candidates, arch)
    recorded = out / "identity.json"
    if not recorded.exists() or json.loads(recorded.read_text()) != expected:
        for stale in observations.iterdir():
            stale.unlink()
        recorded.write_text(json.dumps(expected, indent=1, sort_keys=True) + "\n")
    if args.retry_unobserved:
        for failed in observations.glob("*.err.json"):
            failed.unlink()
    started = time.monotonic()
    capture(candidates, observations, executable, upstream, p4c, args.max_case_bytes,
            args.capture_timeout, args.jobs, arch)
    unobserved = [json.loads(path.read_text()) for path in sorted(observations.glob("*.err.json"))]
    worker = ROOT / ".lake/build/bin/p4-sessions-check"
    digest = campaign.file_digest(worker)
    records = run_workers([str(worker), str(ROOT / "exports/p4.al.json"), "--arch", arch],
                          observations, args.worker_timeout, args.jobs)
    if campaign.file_digest(worker) != digest:
        raise SystemExit("[p4-sessions] the worker executable changed during the sweep")
    summary = summarize(candidates, unobserved, records)
    summary["excluded"] = [pair["stf"] for pair in excluded]
    summary["pairs"] = {"p4c": len(pairs), "p4cExcluded": len(excluded),
                        "regression": len(regression)}
    summary["identity"] = {**expected, "workerTimeoutSeconds": args.worker_timeout,
                           "workerSha256": digest, "jobs": args.jobs,
                           "maxWorkerCases": campaign.MAX_WORKER_CASES}
    summary["elapsedSeconds"] = round(time.monotonic() - started)
    (out / "summary.json").write_text(json.dumps(summary, indent=1, sort_keys=True) + "\n")
    print(f"[p4-sessions] {arch}: {summary['matched']} of {summary['candidates']} sessions "
          f"match on both legs; {summary['statuses']}")
    print(f"[p4-sessions] unobserved: {len(unobserved)} "
          f"{[(item['name'], item['kind']) for item in unobserved]}")
    return verdict(summary)


if __name__ == "__main__":
    raise SystemExit(main())
