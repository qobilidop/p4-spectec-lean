#!/usr/bin/env python3
"""Bounded corpus-v2 pilot: original fixtures, spec-once worker and real mutations."""

import argparse
import copy
import gzip
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import resource
import select
import signal
import subprocess
import tempfile
import time

import contract
import inventory


ROOT = inventory.ROOT
MAX_BYTES = 32 * 1024 * 1024
TIMEOUT = 120
MAX_WORKER_CASES = 32


class HarnessFailure(ValueError):
    def __init__(self, kind, message):
        super().__init__(message)
        self.kind = kind


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def terminate(process):
    if process.poll() is None:
        os.killpg(process.pid, signal.SIGKILL)
    process.wait(timeout=10)


def bounded(command, timeout=TIMEOUT, limit=MAX_BYTES):
    """File-backed bounded subprocess output; crashes/timeouts are never verdicts."""
    start = time.monotonic()
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        process = subprocess.Popen(command, cwd=ROOT, stdout=out, stderr=err,
                                   start_new_session=True)
        try:
            while process.poll() is None:
                if time.monotonic() - start > timeout:
                    raise HarnessFailure("timeout", "subprocess exceeded deadline")
                if os.fstat(out.fileno()).st_size > limit or os.fstat(err.fileno()).st_size > 65536:
                    raise HarnessFailure("oversized", "subprocess output exceeded bound")
                time.sleep(0.05)
            if os.fstat(out.fileno()).st_size > limit or os.fstat(err.fileno()).st_size > 65536:
                raise HarnessFailure("oversized", "subprocess output exceeded bound")
            out.seek(0)
            err.seek(0)
            return process.returncode, out.read(), err.read(), time.monotonic() - start
        finally:
            if process.poll() is None:
                terminate(process)


def atomic(path, data):
    temporary = path.with_name(path.name + f".{os.getpid()}.tmp")
    temporary.write_bytes(data)
    temporary.replace(path)


def file_digest(path):
    result = hashlib.sha256()
    with path.open("rb") as source:
        while chunk := source.read(1024 * 1024):
            result.update(chunk)
    return result.hexdigest()


class Worker:
    def __init__(self, spec, fuel=10000000):
        self.stderr = tempfile.TemporaryFile()
        self.process = subprocess.Popen(
            [str(ROOT / ".lake/build/bin/p4-corpus-worker"), str(spec), "--fuel", str(fuel)],
            cwd=ROOT, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=self.stderr,
            start_new_session=True,
        )
        self.buffer = b""
        self.cases = 0
        started = time.monotonic()
        try:
            if self.line() != {"ready": 2}:
                raise HarnessFailure("worker-protocol", "worker readiness differs")
        except BaseException:
            self.close(kill=True)
            raise
        self.initialization_seconds = time.monotonic() - started

    def line(self):
        deadline = time.monotonic() + TIMEOUT
        while b"\n" not in self.buffer:
            if time.monotonic() > deadline:
                raise HarnessFailure("worker-timeout", "worker exceeded response deadline")
            if os.fstat(self.stderr.fileno()).st_size > 65536:
                raise HarnessFailure("worker-oversized", "worker stderr exceeded bound")
            ready, _, _ = select.select([self.process.stdout], [], [], 0.1)
            if ready:
                chunk = os.read(self.process.stdout.fileno(), 8192)
                if not chunk:
                    raise HarnessFailure("worker-crash", f"worker stdout closed: {self.process.poll()}")
                self.buffer += chunk
                if len(self.buffer) > 8192:
                    raise HarnessFailure("worker-oversized", "worker response exceeded bound")
        line, self.buffer = self.buffer.split(b"\n", 1)
        return contract.strict_json(line)

    def case(self, path):
        if self.cases >= MAX_WORKER_CASES:
            raise HarnessFailure("worker-limit", "worker recycle bound reached")
        if "\n" in str(path) or "\r" in str(path):
            raise ValueError("case path cannot contain newline")
        self.process.stdin.write(str(path).encode("utf-8") + b"\n")
        self.process.stdin.flush()
        self.cases += 1
        return self.line()

    def close(self, kill=False):
        if kill:
            terminate(self.process)
        else:
            self.process.stdin.close()
            try:
                code = self.process.wait(timeout=10)
            except subprocess.TimeoutExpired:
                terminate(self.process)
                raise HarnessFailure("worker-timeout", "worker failed to exit after EOF")
            if code:
                raise HarnessFailure("worker-crash", f"worker exited {code}")
        self.stderr.close()


def verdict(value, name):
    if (not isinstance(value, dict) or set(value) != {"name", "relations"}
            or value["name"] != name or not isinstance(value["relations"], dict)
            or set(value["relations"]) != set(contract.RELATIONS)):
        raise ValueError("malformed worker verdict")
    allowed = {"matched", "matched-public-failure", "syntax-only", "unsupported-type-fresh",
               "unsupported-upstream-abort", "exhausted", "counter-disagreement",
               "output-disagreement", "outcome-disagreement"}
    for relation in value["relations"].values():
        if (not isinstance(relation, dict) or set(relation) != {"status", "leanClass", "message"}
                or relation["status"] not in allowed
                or relation["leanClass"] not in {"not-evaluated", "pass", "hard-error", "unmatch", "exhausted"}
                or not isinstance(relation["message"], str)):
            raise ValueError("malformed relation verdict")
        consistent = {
            "matched": {"pass"}, "matched-public-failure": {"hard-error", "unmatch"},
            "syntax-only": {"not-evaluated"}, "unsupported-type-fresh": {"not-evaluated"},
            "unsupported-upstream-abort": {"not-evaluated"}, "exhausted": {"exhausted"},
            "output-disagreement": {"pass"},
            "counter-disagreement": {"pass", "hard-error", "unmatch"},
            "outcome-disagreement": {"pass", "hard-error", "unmatch"},
        }
        if relation["leanClass"] not in consistent[relation["status"]]:
            raise ValueError("worker status and actual Lean class disagree")
    return value


def cli_parity(upstream, p4c, program, case):
    results = {}
    for name in contract.RELATIONS:
        code, out, err, duration = bounded([str(upstream / "_build/default/p4spec/bin/main.exe"),
            "run", str(upstream / "spec"), "-rel", name, "-i", str(p4c / "p4include"),
            "-p", str(program), "-al"], limit=65536)
        passed = case["relations"][name]["result"]["class"] == "pass"
        if not ((passed and code == 0 and out == b"passed\n")
                or (not passed and code == 1 and not out and err)):
            raise HarnessFailure("cli-parity", f"unexpected CLI exit/output {code}")
        results[name] = {"exit": code, "stdoutSha256": inventory.digest(out),
                         "stderrSha256": inventory.digest(err), "seconds": duration}
    return results


def sensitivity(worker, positive, syntax, directory):
    """Send malformed inputs directly to actual Lean, bypassing Python validation."""
    target = "Program_ok"
    changes = [
        ("counter", positive, lambda c: c["relations"][target].update(counterAfter=1), "counter-disagreement"),
        ("output", positive, lambda c: c["relations"][target]["result"].update(outputs=[]), "output-disagreement"),
        ("boot", positive, lambda c: c.update(boot={}), "error"),
        ("nested-output", positive, lambda c: c["relations"][target]["result"].update(outputs=[{}]), "error"),
        ("class", positive, lambda c: c["relations"][target]["result"].update({"class": "unexpected"}), "error"),
        ("syntax-mode", syntax, lambda c: c["relations"][target].update(mode="SL"), "error"),
        ("syntax-guard", syntax, lambda c: c["relations"][target].update(guard=True), "error"),
        ("range", positive, lambda c: c["relations"][target].update(counterAfter=1 << 62), "error"),
        ("missing-phase", positive, lambda c: c["relations"][target]["typeFresh"].pop("after"), "error"),
        ("changed-type", positive, lambda c: c["relations"][target]["typeFresh"].update(after=1), "unsupported-type-fresh"),
        ("initial-type", positive, lambda c: c["relations"][target]["typeFresh"].update(beforeSpec=1), "unsupported-type-fresh"),
        ("type-range", positive, lambda c: c["relations"][target]["typeFresh"].update(after=1 << 62), "error"),
        ("type-constructor", positive, lambda c: c["boot"]["note"].update(typ=["BoolT", "extra"]), "error"),
        ("extra-field", positive, lambda c: c.update(unexpected=True), "error"),
    ]
    results = []
    for name, original, mutate, expected in changes:
        value = copy.deepcopy(original)
        mutate(value)
        path = directory / "mutation.json"
        path.write_bytes(inventory.encode(value))
        observed = worker.case(path)
        if expected == "error":
            if not isinstance(observed, dict) or set(observed) != {"error"} or not isinstance(observed["error"], str):
                raise ValueError(f"Lean accepted malformed mutation {name}")
        elif verdict(observed, value["name"])["relations"][target]["status"] != expected:
            raise ValueError(f"Lean mutation {name} was misclassified")
        results.append(name)
    path = directory / "mutation.json"
    path.write_bytes(inventory.encode(positive).replace(b'"schemaVersion":2',
                     b'"schemaVersion":1,"schemaVersion":2', 1))
    observed = worker.case(path)
    if set(observed) != {"error"} or "duplicate" not in observed["error"]:
        raise ValueError("Lean accepted duplicate-key mutation")
    results.append("duplicate-key")
    # A valid observation after all mutations must still produce its original verdict.
    path.write_bytes(inventory.encode(positive))
    observed = verdict(worker.case(path), positive["name"])
    if any(r["status"] != "matched" for r in observed["relations"].values()):
        raise ValueError("worker state leaked across mutation sessions")
    return results


def pilot(upstream, p4c, directory):
    check = load("p4_check", ROOT / "test/p4-oracle/check.py")
    adapter = check.load_export()
    revision = adapter.revision_guard(upstream)
    check.p4c_pin_guard(upstream, p4c)
    expected_manifest = inventory.build(p4c, upstream)
    committed_manifest = contract.strict_json(inventory.MANIFEST.read_bytes())
    inventory.validate_manifest(committed_manifest)
    if committed_manifest != expected_manifest:
        raise ValueError("inventory differs from pinned source")
    subprocess.run(["python3", str(ROOT / "scripts/spec-snapshot.py"), "unpack",
                    str(ROOT / "exports/p4.al.json")], cwd=ROOT, check=True)
    adapter.PROBE = ROOT / "test/p4-corpus/probe.ml"
    adapter.SCRATCH = ROOT / ".artifacts/p4-corpus-probe"
    executable = adapter.compile_probe(upstream)
    replay = load("p4_replay", ROOT / "test/p4-oracle/replay.py")
    fixture = contract.strict_json((ROOT / "test/p4-oracle/observed.json").read_bytes())
    cases = replay.validate_fixture(fixture, revision, check.EXPECTED_CASES)
    roots = [(upstream, "$UPSTREAM"), (p4c, "$P4C"), (ROOT, "$REPO")]
    sources = {"upstream": upstream, "p4c": p4c, "repo": ROOT}
    identity = {"schemaVersion": 2, "inventorySha256": expected_manifest["inventorySha256"],
                "upstreamRevision": revision, "p4cRevision": expected_manifest["p4cRevision"],
                "snapshotSha256": expected_manifest["snapshotSha256"],
                "maxCaseBytes": MAX_BYTES, "timeoutSeconds": TIMEOUT,
                "fuel": 10000000, "maxWorkerCases": MAX_WORKER_CASES,
                "workerSha256": file_digest(ROOT / ".lake/build/bin/p4-corpus-worker"),
                "exportPatchSha256": file_digest(ROOT / "upstream/patches/0001-json-export.patch"),
                "leanToolchainSha256": file_digest(ROOT / "lean-toolchain"),
                "lakeManifestSha256": file_digest(ROOT / "lake-manifest.json"),
                "selection": [{**{key: c[key] for key in ("name", "source", "path")},
                    "sha256": file_digest(sources[c["source"]] / c["path"])} for c in cases],
                "sourceDigests": {path: inventory.digest((ROOT / path).read_bytes()) for path in (
                    "test/p4-corpus/probe.ml", "test/p4-corpus/contract.py", "test/p4-corpus/run.py",
                    "P4SpecTecTest/Diff/P4Corpus/Main.lean", "scripts/export-p4-oracle.py")}}
    report = {"identity": identity, "cases": [], "sensitivity": [], "complete": False}
    worker = None
    try:
        worker = Worker(ROOT / "exports/p4.al.json")
        report["workerInitializationSeconds"] = worker.initialization_seconds
        positive = syntax = None
        for case in cases:
            start = time.monotonic()
            program = sources[case["source"]] / case["path"]
            runs = {}
            for name in contract.RELATIONS:
                code, out, _, duration = bounded([str(executable), str(upstream / "spec"),
                    str(p4c / "p4include"), str(program), name])
                if code:
                    raise HarnessFailure("oracle-crash", f"oracle exited {code}")
                runs[name] = contract.strict_json(out)
            observation = contract.observation(runs, adapter)
            value = {"schemaVersion": 2, "name": case["name"], **observation}
            contract.validate_case(value, adapter)
            v1 = {"boot": observation["boot"], "relations": {
                name: {key: item for key, item in run.items() if key != "typeFresh"}
                for name, run in observation["relations"].items()}}
            if check.summarize(v1, roots) != case["expected"]:
                raise ValueError("v2 changed original fixture observation")
            cli = cli_parity(upstream, p4c, program, value)
            data = inventory.encode(value)
            if len(data) > MAX_BYTES:
                raise HarnessFailure("oversized", "encoded case exceeds worker byte bound")
            path = directory / "case.json"
            atomic(path, data)
            packed = gzip.compress(data, mtime=0)
            atomic(directory / f"{case['name']}.json.gz", packed)
            observed = verdict(worker.case(path), case["name"])
            expected = "syntax-only" if observation["boot"] is None else (
                "matched" if case["expected"]["relations"]["Program_ok"]["class"] == "pass"
                else "matched-public-failure")
            if any(result["status"] != expected for result in observed["relations"].values()):
                raise ValueError(f"{case['name']}: worker did not reproduce fixture: {observed}")
            report["cases"].append({"name": case["name"], "bytes": len(data),
                "gzipBytes": len(packed), "sha256": inventory.digest(data),
                "seconds": time.monotonic() - start, "verdict": observed, "cliParity": cli,
                "typeFresh": {name: run["typeFresh"] for name, run in observation["relations"].items()}})
            print(f"[p4-corpus] {case['name']}: {expected}, {len(data)} bytes", flush=True)
            if case["name"] == "positive-regression":
                positive = value
            if case["name"] == "syntax-error":
                syntax = value
        report["sensitivity"] = sensitivity(worker, positive, syntax, directory)
        worker.close()
        worker = None
        zero = Worker(ROOT / "exports/p4.al.json", fuel=0)
        try:
            path = directory / "case.json"
            atomic(path, inventory.encode(positive))
            observed = verdict(zero.case(path), positive["name"])
            if any(r["status"] != "exhausted" for r in observed["relations"].values()):
                raise ValueError("zero-fuel worker did not distinguish exhaustion")
        finally:
            zero.close()
        report["sensitivity"].append("zero-fuel")
        report["complete"] = True
        print(f"[p4-corpus] {len(report['sensitivity'])} actual Lean mutations checked", flush=True)
    except BaseException as error:
        report["failure"] = {"kind": getattr(error, "kind", "validation"), "message": str(error)}
        raise
    finally:
        if worker is not None:
            worker.close(kill=True)
        report["childrenMaxRssPlatformUnits"] = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        atomic(directory / "report.json", inventory.encode(report) + b"\n")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", type=Path, required=True)
    parser.add_argument("--p4c", type=Path, required=True)
    args = parser.parse_args()
    if not args.upstream.is_absolute() or not args.p4c.is_absolute():
        parser.error("checkout paths must be absolute")
    if not (ROOT / ".lake/build/bin/p4-corpus-worker").is_file():
        parser.error("build p4-corpus-worker in the pinned Lean shell first")
    subprocess.run(["lake", "build", "--wfail", "p4-corpus-worker"], cwd=ROOT, check=True)
    directory = ROOT / ".artifacts/p4-corpus-pilot" / str(os.getpid())
    directory.mkdir(parents=True)
    try:
        pilot(args.upstream.resolve(), args.p4c.resolve(), directory)
    except (ValueError, json.JSONDecodeError, subprocess.SubprocessError) as error:
        raise SystemExit(f"[p4-corpus] {error}; partial artifacts: {directory}") from error
    print(f"[p4-corpus] bounded pilot report: {directory / 'report.json'}")


if __name__ == "__main__":
    main()
