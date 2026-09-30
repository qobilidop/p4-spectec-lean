#!/usr/bin/env python3
"""Distinguishing mutations of the source-address filter certificate.

Run inside nix develop after `lake build ExampleProofs check-consumer nano-program-quote`; the
pinned session recording is verified and decompressed first. Each mutation must be
rejected at its intended checking boundary, and the unmutated baseline of every probe must
pass first; any other outcome, including a timeout or an unrelated diagnostic, is a harness
failure. These observations exercise checking boundaries; they are not additional proofs.

* identity: a changed table entry in the quoted program differs from the decoded export and
  from a fresh quotation (`check-consumer`'s comparison, `nano-program-quote --check`);
* branch: a deny-entry packet claimed forwarded is rejected by evaluation;
* extern: an extract that writes the header bits reversed, in an otherwise identical copy of
  the target, makes the source-1 forward claim fail;
* output: a forwarded packet claimed on another port is rejected by evaluation;
* state: a recorded final context replaced by the initial one is rejected by `check-consumer`.
"""

from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[3]
CASES = ("baseline", "identity", "branch", "extern", "output", "state")
EXPORT = "exports/programs/nano-p4/positive/src-addr-filter.json"
BUNDLE = ROOT / ".artifacts/nano-sessions/sessions-observed.json"
SESSION = "corpus:packet:positive/src-addr-filter"
TIMEOUT_SECONDS = 900


class HarnessError(RuntimeError):
    """An execution failure, never an accepted semantic rejection."""


def replace_once(text, anchor, replacement):
    if text.count(anchor) != 1 or anchor == replacement:
        raise HarnessError(f"mutation anchor must occur exactly once: {anchor!r}")
    return text.replace(anchor, replacement, 1)


def extract(text, start, end):
    if text.count(start) != 1 or text.count(end) != 1:
        raise HarnessError(f"missing or ambiguous extraction boundary: {start!r}")
    return start + text.split(start, 1)[1].split(end, 1)[0]


PRELUDE = """import ExampleProofs.NanoP4SrcAddrFilter.Evaluation
set_option linter.missingDocs false
set_option maxHeartbeats 4000000
open P4SpecTec P4SpecTec.Prelude P4SpecTec.BackendSim P4SpecTec.BackendSim.NanoSwitch
open NanoP4Target ExampleProofs.NanoP4SrcAddrFilter
"""

RULES = "[initialized, packetStateText h, string_to_bits_hexText]"


def claim(name, packet, txs, session="session"):
    """A transmission claim proved by evaluation, as the certificate's theorems are."""
    return f"""
theorem Probe.{name} (h : PacketStateText) :
    ∃ ctx, ({session} program [(0, hexText {packet})]).run = some (.ok (ctx, {txs})) := by
  apply Exists.intro
  lazy_eval {RULES}
"""


def target_copy(mutated):
    """The target's extern instance, driver and sessions, copied into `Probe`; the extern
    optionally writes the header bits reversed."""
    externs = (ROOT / "NanoP4Target/Externs.lean").read_text()
    body = extract(externs, "/-- A generated callee through the registered trampoline",
                   "end NanoP4Target")
    if mutated:
        body = replace_once(body, "value_hdr bits.toList)", "value_hdr bits.toList.reverse)")
    session = (ROOT / "NanoP4Target/Session.lean").read_text()
    drive = extract(session, "/-- Drive one received packet through the generated model",
                    "/-- A generated session: `NanoSwitch_init` on the program, then the packets. -/")
    drive = replace_once(drive, "ExceptT.mk (NanoP4Spec.NanoSwitch_drive.run ctx",
                         "ExceptT.mk (@NanoP4Spec.NanoSwitch_drive.run Probe.externs ctx")
    runner = extract(session, "/-- A generated session: `NanoSwitch_init` on the program",
                     "/-! ## Composition -/")
    return "namespace Probe\n" + body + drive + runner + "end Probe\n"


def lean_probe(case, nonce):
    """Scratch Lean source for a proof probe; baseline proves every claim that the mutation
    cases change."""
    source = PRELUDE
    if case in ("baseline", "extern"):
        source += target_copy(mutated=case == "extern")
    if case == "baseline":
        source += claim("branch", "[0, 3, 0]", "[[]]")
        source += claim("extern", "[0, 1, 0]", "[[(0, hexText [0, 1, 0])]]", "Probe.session")
        source += claim("output", "[0, 1, 0]", "[[(0, hexText [0, 1, 0])]]")
    if case == "branch":
        source += claim("branch", "[0, 3, 0]", "[[(0, hexText [0, 3, 0])]]")
    if case == "extern":
        source += claim("extern", "[0, 1, 0]", "[[(0, hexText [0, 1, 0])]]", "Probe.session")
    if case == "output":
        source += claim("output", "[0, 1, 0]", "[[(1, hexText [0, 1, 0])]]")
    return source + f'#eval IO.println "PROBE_DONE:{nonce}"\n'


def validate_lean(case, nonce, result, path):
    if case == "baseline":
        if result.returncode or result.stderr.strip() or result.stdout.strip() != (
                "PROBE_DONE:" + nonce):
            raise HarnessError(f"baseline proof failed\n{result.stdout}{result.stderr}")
        return
    diagnostics = re.findall(re.escape(str(path)) + r":\d+:\d+: error: ([^\n]+)", result.stdout)
    if (result.returncode != 1 or result.stderr.strip() or len(diagnostics) != 1 or
            not diagnostics[0].startswith("lazy_eval: evaluated to") or
            result.stdout.count("error:") != 1 or "warning:" in result.stdout or
            result.stdout.count("PROBE_DONE:" + nonce) != 1):
        raise HarnessError(f"{case}: unrelated proof outcome\n{result.stdout}{result.stderr}")


def identity_probe(nonce, program):
    """Compare a (mutated) quotation with the decoded export in compiled code."""
    namespaced = replace_once(program, "namespace ExampleProofs.NanoP4SrcAddrFilter",
                              "namespace ProbeIdentity")
    namespaced = replace_once(namespaced, "end ExampleProofs.NanoP4SrcAddrFilter",
                              "end ProbeIdentity")
    namespaced = namespaced.split("import NanoP4Spec\n", 1)[1]
    return f"""import NanoP4Spec
import P4SpecTec.Lang.Il.Json
import P4SpecTec.Util.Yojson
{namespaced}
def main : IO UInt32 := do
  let bytes ← IO.FS.readBinFile {json.dumps(EXPORT)}
  let v ← IO.ofExcept (P4SpecTec.Util.Yojson.parseBytes bytes >>= P4SpecTec.Lang.Il.Json.value)
  let same := P4SpecTec.Runtime.Value.eq v (P4SpecTec.Prelude.toValue ProbeIdentity.program)
  IO.println s!"IDENTITY:{nonce}:{{same}}"
  return 0
"""


ENTRY = "(NanoP4Spec.expression.W 8 1)"


def run_identity(nonce, execute, scratch):
    program = (ROOT / "ExampleProofs/NanoP4SrcAddrFilter/Program.lean").read_text()
    outcomes = []
    for label, text in (("baseline", program), ("mutant", replace_once(program, ENTRY,
                        ENTRY.replace("W 8 1", "W 8 5")))):
        path = scratch / f"Identity{label}.lean"
        path.write_text(identity_probe(nonce, text))
        result = execute(["lake", "env", "lean", "--run", str(path)], cwd=ROOT, text=True,
                         capture_output=True, timeout=TIMEOUT_SECONDS)
        expected = f"IDENTITY:{nonce}:{'true' if label == 'baseline' else 'false'}"
        if result.returncode or result.stderr.strip() or result.stdout.strip() != expected:
            raise HarnessError(f"identity {label}: invalid outcome\n{result.stdout}{result.stderr}")
        quoted = scratch / f"Program{label}.lean"
        quoted.write_text(text)
        result = execute(["lake", "exe", "nano-program-quote", EXPORT,
                          "ExampleProofs.NanoP4SrcAddrFilter", str(quoted), "--check"],
                         cwd=ROOT, text=True, capture_output=True, timeout=TIMEOUT_SECONDS)
        fresh = result.returncode == 0 and "is current" in result.stdout
        stale = result.returncode == 1 and "is stale" in result.stderr
        if not (fresh if label == "baseline" else stale):
            raise HarnessError(f"identity {label}: quotation check\n{result.stdout}{result.stderr}")
        outcomes.append(label)
    return "check-consumer identity comparison and nano-program-quote --check"


def run_state(execute, scratch):
    bundle = json.loads(BUNDLE.read_text())
    session = next(s for s in bundle["sessions"] if s["id"] == SESSION)
    for label in ("baseline", "mutant"):
        mutated = json.loads(json.dumps(bundle))
        target = next(s for s in mutated["sessions"] if s["id"] == SESSION)
        if label == "mutant":
            target["drives"][-1]["ctx"] = session["init"]["ctx"]
        path = scratch / f"sessions-{label}.json"
        path.write_text(json.dumps(mutated))
        result = execute(["lake", "exe", "check-consumer", str(path)], cwd=ROOT, text=True,
                         capture_output=True, timeout=TIMEOUT_SECONDS)
        if label == "baseline":
            if result.returncode or "[consumer] 7 claims checked" not in result.stdout:
                raise HarnessError(f"state baseline failed\n{result.stdout}{result.stderr}")
        elif (result.returncode != 1 or "the proven final STF context differs from upstream's"
              not in result.stderr):
            raise HarnessError(f"state mutation not rejected\n{result.stdout}{result.stderr}")
    return "check-consumer upstream observation"


def run_case(case, execute=subprocess.run):
    nonce = uuid.uuid4().hex
    with tempfile.TemporaryDirectory(prefix="src-addr-filter-") as scratch:
        scratch = Path(scratch)
        try:
            if case == "identity":
                return case, run_identity(nonce, execute, scratch)
            if case == "state":
                return case, run_state(execute, scratch)
            path = scratch / "Probe.lean"
            path.write_text(lean_probe(case, nonce))
            result = execute(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                             capture_output=True, timeout=TIMEOUT_SECONDS)
            validate_lean(case, nonce, result, path)
        except subprocess.TimeoutExpired as error:
            raise HarnessError(f"{case}: timed out after {TIMEOUT_SECONDS}s") from error
    return case, "all probes" if case == "baseline" else f"lazy_eval in Probe.{case}"


def write_bundle():
    """Verify the pinned session recording and decompress it for check-consumer."""
    sys.path.insert(0, str(ROOT / "P4SpecTecTest/Oracle/NanoSwitch/Sessions"))
    import fixture  # noqa: E402
    _, data = fixture.read()
    BUNDLE.parent.mkdir(parents=True, exist_ok=True)
    BUNDLE.write_bytes(data)


def main():
    write_bundle()
    # The baseline must pass before any rejection counts.
    print("[src-addr-filter] baseline: " + run_case("baseline")[1])
    with ThreadPoolExecutor(max_workers=3) as pool:
        for case, boundary in pool.map(run_case, CASES[1:]):
            print(f"[src-addr-filter] {case} mutation rejected at {boundary}")
    print(f"[src-addr-filter] {len(CASES) - 1} mutations rejected")


if __name__ == "__main__":
    try:
        main()
    except HarnessError as error:
        print(f"[src-addr-filter] harness failure: {error}", file=sys.stderr)
        sys.exit(1)
