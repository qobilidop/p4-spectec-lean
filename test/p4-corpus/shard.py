#!/usr/bin/env python3
"""Bounded, fail-closed corpus shards with durable per-case resume records."""

import argparse
import contextlib
import fcntl
import gzip
import hashlib
import io
import math
import os
from pathlib import Path
import re
import resource
import shutil
import stat
import subprocess
import time
import uuid

import contract
import inventory
import run


ROOT = inventory.ROOT
SCHEMA = 1
RECORD_LIMIT = 1024 * 1024
SOURCE_PATHS = (
    "test/p4-corpus/shard.py", "test/p4-corpus/run.py", "test/p4-corpus/contract.py",
    "test/p4-corpus/inventory.py", "test/p4-corpus/probe.ml",
    "P4SpecTecTest/Diff/P4Corpus/Main.lean", "scripts/export-p4-oracle.py",
    "test/p4-oracle/check.py", "test/p4-oracle/replay.py", "scripts/spec-snapshot.py",
    "upstream/patches/0001-json-export.patch", "lean-toolchain", "lake-manifest.json",
    "lakefile.toml", "flake.lock",
)
FAILURES = {
    "timeout", "oversized", "oracle-crash", "cli-parity", "worker-timeout",
    "worker-oversized", "worker-crash", "worker-protocol", "worker-limit",
    "invalid-artifact", "harness-error",
}
PHASES = {"start", "Program_ok", "Program_inst", "cli", "artifact", "worker-start",
          "worker", "terminal"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(value):
    return inventory.digest(inventory.encode(value))


def seal(value):
    return {**value, "recordSha256": digest(value)}


def unseal(value):
    require(isinstance(value, dict) and "recordSha256" in value, "missing record digest")
    body = {key: item for key, item in value.items() if key != "recordSha256"}
    require(value["recordSha256"] == digest(body), "record digest mismatch")
    return body


def secure_directory(path):
    """Open every absolute directory component without following symlinks."""
    require(path.is_absolute(), "artifact directory must be absolute")
    descriptor = os.open("/", os.O_RDONLY | os.O_DIRECTORY)
    try:
        for name in path.parts[1:]:
            require(name not in ("", ".", ".."), "unsafe directory component")
            try:
                os.mkdir(name, mode=0o700, dir_fd=descriptor)
                os.fsync(descriptor)
            except FileExistsError:
                pass
            following = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW,
                                dir_fd=descriptor)
            os.close(descriptor)
            descriptor = following
        return descriptor
    except BaseException:
        os.close(descriptor)
        raise


@contextlib.contextmanager
def lock(descriptor, name):
    fd = os.open(name, os.O_RDWR | os.O_CREAT | os.O_NOFOLLOW, 0o600, dir_fd=descriptor)
    try:
        require(stat.S_ISREG(os.fstat(fd).st_mode), "lock is not a regular file")
        try:
            fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise ValueError("another writer holds the lock") from error
        yield
    finally:
        os.close(fd)


class Store:
    """All cache IO is descriptor-relative and accepts only known single names."""

    def __init__(self, parent, identity, adapter):
        self.identity = identity
        self.sha = digest(identity)
        self.path = parent / self.sha
        self.fd = secure_directory(self.path)
        self.adapter = adapter
        self.selection = {case["path"]: case for case in identity["selection"]}
        require(len(self.selection) == len(identity["selection"]), "duplicate selected case")
        self.keys = {name: hashlib.sha256(name.encode("utf-8")).hexdigest()
                     for name in self.selection}
        self._lock = lock(self.fd, "lock")
        try:
            self._lock.__enter__()
            self.scan()
            if "run.json" in self.names():
                require(self.json("run.json") == identity, "run identity differs")
            else:
                require(all(name == "lock" or re.fullmatch(
                    r"(?:\.tmp\.|q\.tmp\.)[0-9a-f]{32}\.run\.json", name)
                    for name in self.names()), "identity absent in nonempty run directory")
                for name in self.names():
                    if name.startswith(".tmp."):
                        destination = "q.tmp." + name.removeprefix(".tmp.")
                        require(destination not in self.names(), "identity quarantine exists")
                        os.rename(name, destination, src_dir_fd=self.fd, dst_dir_fd=self.fd)
                os.fsync(self.fd)
                self.write("run.json", inventory.encode(identity))
        except BaseException:
            self._lock.__exit__(None, None, None)
            os.close(self.fd)
            raise

    def close(self):
        self._lock.__exit__(None, None, None)
        os.close(self.fd)

    def names(self):
        return set(os.listdir(self.fd))

    def known(self, name):
        if name in {"run.json", "lock", "summary.json", "failure.json", "worker-input.json"}:
            return True
        for key in self.keys.values():
            base = rf"{key}\.(?:started\.json|result\.json|obs\.json\.gz)"
            if re.fullmatch(base, name):
                return True
            if re.fullmatch(rf"q\.[1-9][0-9]*\.{base}", name):
                return True
        # Only our unique temporary names can be recovered after an interrupted write.
        match = re.fullmatch(r"\.tmp\.([0-9a-f]{32})\.(.+)", name)
        if match:
            return self.known_final(match.group(2))
        match = re.fullmatch(r"q\.tmp\.([0-9a-f]{32})\.(.+)", name)
        return bool(match and self.known_final(match.group(2)))

    def known_final(self, name):
        return not name.startswith((".tmp.", "q.")) and self.known(name) and name != "lock"

    def scan(self):
        for name in self.names():
            require(self.known(name), f"unknown artifact path: {name}")
            info = os.stat(name, dir_fd=self.fd, follow_symlinks=False)
            require(stat.S_ISREG(info.st_mode), f"artifact is not a regular file: {name}")
            require(info.st_nlink == 1, f"artifact has multiple hard links: {name}")

    def read(self, name, limit):
        require(self.known(name), "unknown artifact reference")
        fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW, dir_fd=self.fd)
        try:
            info = os.fstat(fd)
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1, "nonregular artifact")
            require(info.st_size <= limit, "artifact exceeds byte bound")
            with os.fdopen(fd, "rb", closefd=False) as stream:
                data = stream.read(limit + 1)
            require(len(data) == info.st_size and len(data) <= limit, "artifact changed while reading")
            return data
        finally:
            os.close(fd)

    def json(self, name):
        return contract.strict_json(self.read(name, RECORD_LIMIT))

    def write(self, name, data):
        require(self.known_final(name), "unknown artifact destination")
        if name in self.names():
            info = os.stat(name, dir_fd=self.fd, follow_symlinks=False)
            require(stat.S_ISREG(info.st_mode) and info.st_nlink == 1,
                    "destination is not an unlinked regular file")
        temporary = f".tmp.{uuid.uuid4().hex}.{name}"
        fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW,
                     0o600, dir_fd=self.fd)
        try:
            with os.fdopen(fd, "wb", closefd=False) as stream:
                stream.write(data)
                stream.flush()
                os.fsync(fd)
            os.rename(temporary, name, src_dir_fd=self.fd, dst_dir_fd=self.fd)
            os.fsync(self.fd)
        finally:
            os.close(fd)

    def case_name(self, name, suffix):
        return self.keys[name] + "." + suffix

    def marker(self, name, attempt, phase):
        require(type(attempt) is int and attempt > 0 and phase in PHASES, "invalid attempt marker")
        self.write(self.case_name(name, "started.json"), inventory.encode(seal({
            "schemaVersion": SCHEMA, "identitySha256": self.sha, "case": name,
            "sourceSha256": self.selection[name]["sha256"], "attempt": attempt, "phase": phase})))

    def validate_marker(self, value, name):
        value = unseal(value)
        require(set(value) == {"schemaVersion", "identitySha256", "case", "sourceSha256",
                               "attempt", "phase"}, "malformed attempt marker")
        self.common(value, name)
        require(value["phase"] in PHASES, "unknown attempt phase")
        return value

    def common(self, value, name):
        require(type(value["schemaVersion"]) is int and value["schemaVersion"] == SCHEMA
                and value["identitySha256"] == self.sha and value["case"] == name
                and value["sourceSha256"] == self.selection[name]["sha256"]
                and type(value["attempt"]) is int and value["attempt"] > 0,
                "case identity/attempt mismatch")

    def observation(self, name, reference=None):
        filename = self.case_name(name, "obs.json.gz")
        packed = self.read(filename, run.MAX_BYTES + 65536)
        try:
            with gzip.GzipFile(fileobj=io.BytesIO(packed)) as stream:
                data = stream.read(run.MAX_BYTES + 1)
        except (OSError, EOFError) as error:
            raise ValueError("corrupt gzip observation") from error
        require(len(data) <= run.MAX_BYTES, "expanded observation exceeds byte bound")
        value = contract.strict_json(data)
        contract.validate_case(value, self.adapter)
        require(value["name"] == name, "observation case differs")
        actual = {"path": filename, "rawBytes": len(data), "gzipBytes": len(packed),
                  "rawSha256": inventory.digest(data), "gzipSha256": inventory.digest(packed)}
        if reference is not None:
            require(reference == actual, "observation reference/hash/size differs")
        return value, actual

    def save_observation(self, name, value):
        contract.validate_case(value, self.adapter)
        require(value["name"] == name, "observation case differs")
        data = inventory.encode(value)
        if len(data) > run.MAX_BYTES:
            raise run.HarnessFailure("oversized", "encoded observation exceeds worker bound")
        self.write(self.case_name(name, "obs.json.gz"), gzip.compress(data, mtime=0))
        return self.observation(name)[1]

    def terminal(self, name, value):
        self.validate_terminal(seal(value), name)
        self.write(self.case_name(name, "result.json"), inventory.encode(seal(value)))

    def validate_terminal(self, sealed, name):
        value = unseal(sealed)
        require(set(value) == {"schemaVersion", "identitySha256", "case", "sourceSha256",
                               "attempt", "kind", "observation", "verdict", "cliParity",
                               "failure", "resources"}, "malformed terminal record")
        self.common(value, name)
        require(value["kind"] in {"semantic", "harness"}, "unknown terminal kind")
        validate_resources(value["resources"])
        if value["observation"] is not None:
            observation, _ = self.observation(name, value["observation"])
        else:
            require(self.case_name(name, "obs.json.gz") not in self.names(),
                    "unreferenced observation in terminal record")
            observation = None
        if value["kind"] == "semantic":
            require(observation is not None and value["failure"] is None, "semantic record lacks observation")
            run.verdict(value["verdict"], name)
            validate_cli(value["cliParity"], observation)
            validate_statuses(value["verdict"], observation)
        else:
            require(value["verdict"] is None, "harness failure advertises semantic verdict")
            failure = value["failure"]
            require(isinstance(failure, dict) and set(failure) == {"kind", "phase", "message"}
                    and failure["kind"] in FAILURES and failure["phase"] in PHASES
                    and isinstance(failure["message"], str) and bool(failure["message"]),
                    "malformed harness failure")
            if value["cliParity"] is not None:
                require(observation is not None, "CLI record lacks completed observation")
                validate_cli(value["cliParity"], observation)
        return value

    def recover(self):
        """Validate terminal records; quarantine only known interrupted files."""
        self.scan()
        records = {}
        attempts = {}
        # A partial temporary write is not a committed artifact. Preserve it under a
        # known quarantine name, never decode or count it as an observation.
        for entry in self.names():
            if entry.startswith(".tmp."):
                destination = "q.tmp." + entry.removeprefix(".tmp.")
                require(destination not in self.names(), "temporary quarantine destination exists")
                os.rename(entry, destination, src_dir_fd=self.fd, dst_dir_fd=self.fd)
        os.fsync(self.fd)
        for name in self.selection:
            result = self.case_name(name, "result.json")
            marker = self.case_name(name, "started.json")
            artifact = self.case_name(name, "obs.json.gz")
            names = self.names()
            history = [entry for entry in names if re.fullmatch(
                rf"q\.[1-9][0-9]*\.{re.escape(marker)}", entry)]
            prior = 0
            for entry in history:
                previous = self.validate_marker(self.json(entry), name)
                require(entry == f"q.{previous['attempt']}.{marker}", "quarantine attempt differs")
                prior = max(prior, previous["attempt"])
            if result in names:
                value = self.validate_terminal(self.json(result), name)
                require(marker in names, "terminal record lacks durable attempt marker")
                marked = self.validate_marker(self.json(marker), name)
                require(marked["attempt"] == value["attempt"] > prior
                        and marked["phase"] == "terminal", "terminal attempt differs")
                records[name] = value
                attempts[name] = value["attempt"]
                continue
            marked = self.validate_marker(self.json(marker), name) if marker in names else None
            require(marked is not None or artifact not in names, "orphan observation lacks marker")
            if marked is not None:
                require(marked["attempt"] > prior, "interrupted attempt is not increasing")
                if artifact in names:
                    self.observation(name)  # Malformed final artifacts are never silently retried.
                prior = marked["attempt"]
                # Preserve the marker until the artifact move is durable. A crash
                # between moves must still identify the final-name orphan's attempt.
                for original in (artifact, marker):
                    if original in names:
                        destination = f"q.{prior}.{original}"
                        require(destination not in names, "quarantine destination exists")
                        os.rename(original, destination, src_dir_fd=self.fd, dst_dir_fd=self.fd)
                        os.fsync(self.fd)
            attempts[name] = prior + 1
        return records, attempts


def validate_resources(value):
    require(isinstance(value, dict) and set(value) == {"phases", "childrenMaxRssPlatformUnits"}
            and type(value["childrenMaxRssPlatformUnits"]) is int
            and value["childrenMaxRssPlatformUnits"] >= 0
            and isinstance(value["phases"], dict), "malformed resource record")
    for phase, metric in value["phases"].items():
        require(phase in PHASES and isinstance(metric, dict)
                and set(metric) == {"seconds", "stdoutBytes", "stderrBytes"}
                and type(metric["seconds"]) in (int, float) and math.isfinite(metric["seconds"])
                and metric["seconds"] >= 0
                and all(metric[key] is None or (type(metric[key]) is int and metric[key] >= 0)
                        for key in ("stdoutBytes", "stderrBytes")), "malformed phase resource metric")


def validate_cli(value, observation):
    require(isinstance(value, dict) and set(value) == set(contract.RELATIONS), "missing CLI parity")
    for relation in contract.RELATIONS:
        item = value[relation]
        expected = 0 if observation["relations"][relation]["result"]["class"] == "pass" else 1
        require(isinstance(item, dict)
                and set(item) == {"exit", "stdoutSha256", "stderrSha256", "seconds"}
                and type(item["exit"]) is int and item["exit"] == expected
                and all(isinstance(item[key], str) and re.fullmatch("[0-9a-f]{64}", item[key])
                        for key in ("stdoutSha256", "stderrSha256"))
                and type(item["seconds"]) in (int, float)
                and math.isfinite(item["seconds"]) and item["seconds"] >= 0,
                "malformed CLI parity record")
        require(item["stdoutSha256"] == inventory.digest(b"passed\n" if expected == 0 else b""),
                "CLI stdout contract differs")
        require(expected == 0 or item["stderrSha256"] != inventory.digest(b""),
                "CLI failure lacks diagnostic")


def validate_statuses(verdict, observation):
    for relation in contract.RELATIONS:
        status = verdict["relations"][relation]["status"]
        upstream = observation["relations"][relation]["result"]["class"]
        if contract.unsupported_type_fresh(observation):
            # Lean checks relation-local counters, not both sessions together.
            nonzero = any(observation["relations"][relation]["typeFresh"].values())
            if nonzero:
                require(status == "unsupported-type-fresh", "nonzero Type.Fresh evaluated")
                continue
        if upstream == "syntax":
            require(status == "syntax-only", "syntax record advertises AL execution")
        elif upstream == "abort":
            require(status == "unsupported-upstream-abort", "abort record advertises supported execution")
        else:
            require(status not in {"syntax-only", "unsupported-upstream-abort", "unsupported-type-fresh"},
                    "unexpected unsupported/syntax status")
            require(status != "matched" or upstream == "pass", "failure advertises pass agreement")
            require(status != "matched-public-failure" or upstream == "unmatch",
                    "pass advertises failure agreement")


def summary(store, records):
    statuses = {}
    upstream = {}
    tags = {}
    failures = {}
    for name, record in records.items():
        if record["kind"] == "harness":
            kind = record["failure"]["kind"]
            failures[kind] = failures.get(kind, 0) + 1
        if record["observation"] is not None:
            observation, _ = store.observation(name, record["observation"])
            for relation in observation["relations"].values():
                key = relation["result"]["class"]
                upstream[key] = upstream.get(key, 0) + 1
        if record["kind"] == "semantic":
            for relation in record["verdict"]["relations"].values():
                status, tag = relation["status"], relation["leanClass"]
                statuses[status] = statuses.get(status, 0) + 1
                tags[tag] = tags.get(tag, 0) + 1
    complete = len(records) == len(store.selection)
    run_failure = None
    if "failure.json" in store.names():
        run_failure = store.json("failure.json")
        require(isinstance(run_failure, dict) and set(run_failure) == {
            "schemaVersion", "identitySha256", "kind", "message", "complete"}
            and type(run_failure["schemaVersion"]) is int and run_failure["schemaVersion"] == SCHEMA
            and run_failure["identitySha256"] == store.sha and run_failure["kind"] in FAILURES
            and isinstance(run_failure["message"], str) and bool(run_failure["message"])
            and run_failure["complete"] is False, "malformed run failure")
    okay = complete and not failures and run_failure is None and not (set(statuses) - {
        "matched", "matched-public-failure", "syntax-only"})
    return {"schemaVersion": SCHEMA, "identitySha256": store.sha,
            "canonicalCounts": store.identity["canonicalCounts"],
            "selectedCandidates": len(store.selection), "terminalAttempts": len(records),
            "complete": complete, "okay": okay, "relationStatuses": statuses,
            "upstreamClasses": upstream, "actualLeanClasses": tags, "harnessFailures": failures,
            "runFailure": run_failure,
            "alExecutedRelations": sum(tags.get(key, 0) for key in ("pass", "hard-error", "unmatch", "exhausted")),
            "rssMeaning": "cumulative child high-water mark in platform units; not per-case or a hard limit"}


def run_cases(store, executable, upstream, p4c, spec, worker_factory=run.Worker):
    def run_failure(error):
        kind = getattr(error, "kind", "invalid-artifact")
        store.write("failure.json", inventory.encode({"schemaVersion": SCHEMA,
            "identitySha256": store.sha, "kind": kind if kind in FAILURES else "harness-error",
            "message": str(error) or type(error).__name__, "complete": False}))

    try:
        records, attempts = store.recover()
    except Exception as error:
        run_failure(error)
        raise
    if "failure.json" in store.names():
        result = summary(store, records)
        store.write("summary.json", inventory.encode(result))
        return result
    if any(record["kind"] == "harness" and record["failure"]["kind"] in {
            "invalid-artifact", "harness-error", "worker-protocol", "cli-parity"}
           for record in records.values()):
        result = summary(store, records)
        store.write("summary.json", inventory.encode(result))
        return result
    worker = None
    try:
        for name, selected in store.selection.items():
            if name in records:
                continue
            attempt = attempts[name]
            phase = "start"
            metrics = {}
            reference = cli = observed = None
            store.marker(name, attempt, phase)
            fatal = False
            phase_started = time.monotonic()
            try:
                program = p4c / selected["path"].removeprefix("p4c/")
                require(run.file_digest(program) == selected["sha256"], "case source changed after preflight")
                sessions = {}
                for phase in contract.RELATIONS:
                    store.marker(name, attempt, phase)
                    phase_started = time.monotonic()
                    code, out, err, seconds = run.bounded([str(executable), str(upstream / "spec"),
                        str(p4c / "p4include"), str(program), phase])
                    metrics[phase] = {"seconds": seconds, "stdoutBytes": len(out), "stderrBytes": len(err)}
                    if code:
                        raise run.HarnessFailure("oracle-crash", f"oracle exited {code}")
                    sessions[phase] = contract.strict_json(out)
                observation = contract.observation(sessions, store.adapter)
                value = {"schemaVersion": 2, "name": name, **observation}
                phase = "artifact"
                phase_started = time.monotonic()
                store.marker(name, attempt, phase)
                reference = store.save_observation(name, value)
                metrics[phase] = {"seconds": time.monotonic() - phase_started,
                                  "stdoutBytes": None, "stderrBytes": None}
                phase = "cli"
                phase_started = time.monotonic()
                store.marker(name, attempt, phase)
                cli = run.cli_parity(upstream, p4c, program, value)
                metrics[phase] = {"seconds": sum(item["seconds"] for item in cli.values()),
                                  "stdoutBytes": sum(7 for item in cli.values() if item["exit"] == 0),
                                  "stderrBytes": None}
                if worker is None or worker.cases >= run.MAX_WORKER_CASES:
                    if worker is not None:
                        worker.close()
                        worker = None
                    phase = "worker-start"
                    phase_started = time.monotonic()
                    store.marker(name, attempt, phase)
                    worker = worker_factory(spec)
                    metrics[phase] = {"seconds": worker.initialization_seconds,
                                      "stdoutBytes": None, "stderrBytes": None}
                phase = "worker"
                phase_started = time.monotonic()
                store.marker(name, attempt, phase)
                store.write("worker-input.json", inventory.encode(value))
                started = time.monotonic()
                observed = run.verdict(worker.case(store.path / "worker-input.json"), name)
                metrics[phase] = {"seconds": time.monotonic() - started,
                                  "stdoutBytes": None, "stderrBytes": None}
                validate_statuses(observed, value)
                failure = None
                kind = "semantic"
            except (Exception, SystemExit) as error:
                metrics.setdefault(phase, {"seconds": time.monotonic() - phase_started,
                                           "stdoutBytes": None, "stderrBytes": None})
                kind = "harness"
                failure_kind = getattr(error, "kind", "invalid-artifact")
                if failure_kind not in FAILURES:
                    failure_kind = "harness-error"
                failure = {"kind": failure_kind, "phase": phase, "message": str(error) or type(error).__name__}
                observed = None
                fatal = failure_kind in {"invalid-artifact", "harness-error", "worker-protocol", "cli-parity"}
                if worker is not None:
                    worker.close(kill=True)
                    worker = None
            record = {"schemaVersion": SCHEMA, "identitySha256": store.sha, "case": name,
                      "sourceSha256": selected["sha256"], "attempt": attempt, "kind": kind,
                      "observation": reference, "verdict": observed, "cliParity": cli,
                      "failure": failure, "resources": {"phases": metrics,
                          "childrenMaxRssPlatformUnits": resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss}}
            # A terminal-phase marker precedes commit. A crash here leaves an interrupted
            # attempt; only result.json commits completion.
            store.marker(name, attempt, "terminal")
            store.terminal(name, record)
            records[name] = record
            store.write("summary.json", inventory.encode(summary(store, records)))
            print(f"[p4-shard] {name}: {kind} " + (failure["kind"] if failure else
                  ",".join(item["status"] for item in observed["relations"].values())), flush=True)
            if fatal:
                break
        if worker is not None:
            worker.close()
            worker = None
    except Exception as error:
        run_failure(error)
        raise
    finally:
        if worker is not None:
            worker.close(kill=True)
    result = summary(store, records)
    store.write("summary.json", inventory.encode(result))
    return result


def preflight(upstream, p4c, index, total):
    """Rebuild pinned sources; content-key the compile workspace under a lock."""
    check = run.load("shard_check", ROOT / "test/p4-oracle/check.py")
    adapter = check.load_export()
    revision = adapter.revision_guard(upstream)
    check.p4c_pin_guard(upstream, p4c)
    manifest = inventory.build(p4c, upstream)
    committed = contract.strict_json(inventory.MANIFEST.read_bytes())
    inventory.validate_manifest(committed)
    require(committed == manifest, "inventory differs from exact pinned corpus")
    selected = inventory.shard(manifest, index, total)
    require(bool(selected), "empty shard selection")
    subprocess.run(["python3", str(ROOT / "scripts/spec-snapshot.py"), "unpack",
                    str(ROOT / "exports/p4.al.json")], cwd=ROOT, check=True)
    subprocess.run(["lake", "build", "--wfail", "p4-corpus-worker"], cwd=ROOT, check=True)
    build_fd = secure_directory(ROOT / ".artifacts/p4-corpus-probe")
    try:
        with lock(build_fd, "build.lock"):
            subprocess.run(["dune", "build", "p4spec/bin/main.exe"], cwd=upstream, check=True)
            build = upstream / "_build/default/p4spec/lib"
            archives = {str(build / directory / f"{name}{suffix}"):
                        run.file_digest(build / directory / f"{name}{suffix}")
                        for directory, name in adapter.LIBRARIES for suffix in (".cmxa", ".a")}
            compiler = Path(shutil.which("ocamlopt") or "missing")
            recipe = {"schemaVersion": 1, "upstreamRoot": str(upstream), "repoRoot": str(ROOT),
                      "probeSha256": run.file_digest(ROOT / "test/p4-corpus/probe.ml"),
                      "helperSha256": run.file_digest(ROOT / "scripts/export-p4-oracle.py"),
                      "compilerPath": str(compiler), "compilerSha256": run.file_digest(compiler),
                      "compilerVersion": subprocess.check_output(["ocamlopt", "-version"], text=True).strip(),
                      "archives": archives, "flakeLockSha256": run.file_digest(ROOT / "flake.lock")}
            workspace_key = digest(recipe)
            adapter.PROBE = ROOT / "test/p4-corpus/probe.ml"
            adapter.SCRATCH = ROOT / ".artifacts/p4-corpus-probe"
            executable = adapter.compile_probe(upstream, workspace_key=workspace_key)
            require(archives == {path: run.file_digest(Path(path)) for path in archives},
                    "linked archive changed during probe compilation")
    finally:
        os.close(build_fd)
    adapter.revision_guard(upstream)
    identity = {"schemaVersion": SCHEMA, "observationSchemaVersion": 2,
                "upstreamRevision": revision, "p4cRevision": manifest["p4cRevision"],
                "inventorySha256": manifest["inventorySha256"], "snapshotSha256": manifest["snapshotSha256"],
                "canonicalCounts": manifest["counts"], "shardIndex": index, "shardCount": total,
                "selection": [{"path": case["path"], "sha256": case["sha256"], "symlink": case["symlink"]}
                              for case in selected],
                "roots": {"repo": str(ROOT), "upstream": str(upstream), "p4c": str(p4c),
                          "snapshot": str(ROOT / "exports/p4.al.json")},
                "limits": {"timeoutSeconds": run.TIMEOUT, "maxCaseBytes": run.MAX_BYTES,
                           "stderrBytes": 65536, "workerResponseBytes": 8192,
                           "fuel": 10000000, "maxWorkerCases": run.MAX_WORKER_CASES, "concurrency": 1},
                "configuration": {"mode": "AL", "cache": True, "det": False, "guard": False,
                                  "relations": list(contract.RELATIONS), "typeFreshPolicy": "zero-only"},
                "sourceDigests": {path: run.file_digest(ROOT / path) for path in SOURCE_PATHS},
                "workerSha256": run.file_digest(ROOT / ".lake/build/bin/p4-corpus-worker"),
                "probeSha256": run.file_digest(executable), "probeRecipe": recipe,
                "probeWorkspaceKey": workspace_key}
    return identity, adapter, executable


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--upstream", required=True, type=Path)
    parser.add_argument("--p4c", required=True, type=Path)
    parser.add_argument("--shard", type=int, default=0)
    parser.add_argument("--shards", type=int, default=317)
    args = parser.parse_args()
    require(args.upstream.is_absolute() and args.p4c.is_absolute(), "checkout roots must be absolute")
    upstream, p4c = args.upstream.resolve(), args.p4c.resolve()
    identity, adapter, executable = preflight(upstream, p4c, args.shard, args.shards)
    store = Store(ROOT / ".artifacts/p4-corpus-shards", identity, adapter)
    try:
        result = run_cases(store, executable, upstream, p4c, ROOT / "exports/p4.al.json")
        print(f"[p4-shard] summary: {store.path / 'summary.json'}", flush=True)
        raise SystemExit(0 if result["okay"] else 1)
    finally:
        store.close()


if __name__ == "__main__":
    main()
