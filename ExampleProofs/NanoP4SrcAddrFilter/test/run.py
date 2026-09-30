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
* receiver: an extract that returns the packet state with its cursor unadvanced. The parser
  discards the receiver (`packet_in` is copied in, never out), so the forward claim and the STF
  trace still prove; the extern contract, which relates every returned receiver, rejects it;
* output: a forwarded packet claimed on another port is rejected by evaluation;
* state: the recorded context after the first packet replaced by the initial one is rejected by
  `check-consumer`'s trace comparison.

The identity case runs the quotation freshness check itself and a copy of `check-consumer`'s
identity comparison on a patched program; the state case runs `check-consumer` itself.
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
CASES = ("baseline", "identity", "branch", "extern", "receiver", "output", "state")
EXPORT = "exports/programs/nano-p4/positive/src-addr-filter.json"
BUNDLE = ROOT / ".artifacts/nano-sessions/sessions-observed.json"
# Built binaries, run through `lake env` (their Lean frontend needs the module path) so that
# parallel cases never build or contend for Lake's build lock.
CHECK_CONSUMER = ROOT / ".lake/build/bin/check-consumer"
QUOTE_PROGRAM = ROOT / ".lake/build/bin/nano-program-quote"
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
set_option maxHeartbeats 8000000
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


def target_copy(mutation=None):
    """The target's extern instance, driver and sessions, copied into `Probe`. The extern
    optionally writes the header bits reversed or returns the packet state unadvanced."""
    externs = (ROOT / "NanoP4Target/Externs.lean").read_text()
    body = extract(externs, "/-- A generated callee through the registered trampoline",
                   "end NanoP4Target")
    if mutation == "extern":
        body = replace_once(body, "value_hdr bits.toList)", "value_hdr bits.toList.reverse)")
    if mutation == "receiver":
        body = replace_once(body, "let (pkt, ctx) ← extract ctx pkt", "let (_, ctx) ← extract ctx pkt")
    # the copy takes precedence over the library instance wherever an instance is resolved
    body = replace_once(body, "instance externs : NanoP4Spec.Externs where",
                        "instance (priority := high) externs : NanoP4Spec.Externs where")
    session = (ROOT / "NanoP4Target/Session.lean").read_text()
    drive = extract(session, "/-- Drive one received packet through the generated model",
                    "/-- A generated session: `NanoSwitch_init` on the program, then the packets. -/")
    drive = replace_once(drive, "ExceptT.mk (NanoP4Spec.NanoSwitch_drive.run ctx",
                         "ExceptT.mk (@NanoP4Spec.NanoSwitch_drive.run Probe.externs ctx")
    runner = extract(session, "/-- A generated session: `NanoSwitch_init` on the program",
                     "/-! ## Composition -/")
    return "namespace Probe\n" + body + drive + runner + "end Probe\n"


def contract_copy():
    """The extern contract and its proof, copied into `Probe` to check the copied extern."""
    contract = (ROOT / "NanoP4Target/Contract.lean").read_text()
    # from the module's opens, which its sections rely on, to its end
    body = extract(contract, "open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine",
                   "end NanoP4Target")
    # the copies' axiom audits would name `Probe`, not the library
    body, audits = re.subn(r"/-- info: '[^']*'[^-]*-/\n#guard_msgs[^\n]*\n", "", body)
    if audits != 2:
        raise HarnessError(f"expected two contract axiom audits, found {audits}")
    return "namespace Probe\n" + body + "end Probe\n"


TRACE = f"""
theorem Probe.trace (h : PacketStateText) :
    (List.range 4).map (fun n => (Probe.session program (stfPackets.take n)).run) = stfTrace := by
  lazy_eval {RULES}
"""


def lean_probe(case, nonce):
    """Scratch Lean source for a proof probe; baseline proves every claim that the mutation
    cases change, on the library target and on the unmutated copy."""
    source = PRELUDE
    if case in ("baseline", "extern", "receiver"):
        source += target_copy(None if case == "baseline" else case)
    if case in ("baseline", "receiver"):
        source += contract_copy()
    forward = "[[(0, hexText [0, 1, 0])]]"
    if case == "baseline":
        source += claim("branch", "[0, 3, 0]", "[[]]")
        source += claim("extern", "[0, 1, 0]", forward, "Probe.session")
        source += claim("output", "[0, 1, 0]", forward)
        source += TRACE
    if case == "branch":
        source += claim("branch", "[0, 3, 0]", "[[(0, hexText [0, 3, 0])]]")
    if case == "extern":
        source += claim("extern", "[0, 1, 0]", forward, "Probe.session")
    if case == "receiver":
        # the discarded receiver keeps every decision and state: these still prove
        source += claim("receiverForward", "[0, 1, 0]", forward, "Probe.session")
        source += TRACE
    if case == "output":
        source += claim("output", "[0, 1, 0]", "[[(1, hexText [0, 1, 0])]]")
    return source + f'#eval IO.println "PROBE_DONE:{nonce}"\n'


def theorem_lines(source, name):
    """The line range of theorem `name` (or `Probe.name`) in a probe source."""
    lines = source.split("\n")
    starts = [i + 1 for i, line in enumerate(lines) if line.startswith("theorem ")]
    start = next((i + 1 for i, line in enumerate(lines)
                  if line.startswith((f"theorem Probe.{name} ", f"theorem {name} "))), None)
    if start is None:
        raise HarnessError(f"missing probe theorem {name}")
    end = min([s for s in starts if s > start], default=len(lines) + 1)
    return start, end


def validate_lean(case, nonce, result, path, source=""):
    if case == "baseline":
        if result.returncode or result.stderr.strip() or result.stdout.strip() != (
                "PROBE_DONE:" + nonce):
            raise HarnessError(f"baseline proof failed\n{result.stdout}{result.stderr}")
        return
    diagnostics = re.findall(re.escape(str(path)) + r":(\d+):\d+: error: ([^\n]+)", result.stdout)
    # the receiver is rejected inside the copied contract proof, by whatever step fails there;
    # every other mutation by exactly one evaluation mismatch in its claim
    target = "externsContractHolds" if case == "receiver" else case
    start, end = theorem_lines(source, target) if source else (0, 1 << 30)
    evaluation = all(message.startswith("lazy_eval: evaluated to") for _, message in diagnostics)
    if (result.returncode != 1 or result.stderr.strip() or not diagnostics or
            (case != "receiver" and (len(diagnostics) != 1 or not evaluation)) or
            any(not start <= int(line) < end for line, _ in diagnostics) or
            result.stdout.count("error:") != len(diagnostics) or "warning:" in result.stdout or
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
        result = execute(["lake", "env", str(QUOTE_PROGRAM), EXPORT,
                          "ExampleProofs.NanoP4SrcAddrFilter", str(quoted), "--check"],
                         cwd=ROOT, text=True, capture_output=True, timeout=TIMEOUT_SECONDS)
        fresh = result.returncode == 0 and "is current" in result.stdout
        stale = result.returncode == 1 and "is stale" in result.stderr
        if not (fresh if label == "baseline" else stale):
            raise HarnessError(f"identity {label}: quotation check\n{result.stdout}{result.stderr}")
    return "check-consumer identity comparison and nano-program-quote --check"


def run_state(execute, scratch):
    bundle = json.loads(BUNDLE.read_text())
    session = next(s for s in bundle["sessions"] if s["id"] == SESSION)
    for label in ("baseline", "mutant"):
        mutated = json.loads(json.dumps(bundle))
        target = next(s for s in mutated["sessions"] if s["id"] == SESSION)
        if label == "mutant":
            target["drives"][0]["ctx"] = session["init"]["ctx"]
        path = scratch / f"sessions-{label}.json"
        path.write_text(json.dumps(mutated))
        result = execute(["lake", "env", str(CHECK_CONSUMER), str(path)], cwd=ROOT, text=True,
                         capture_output=True, timeout=TIMEOUT_SECONDS)
        if label == "baseline":
            if result.returncode or "[consumer] 7 claims checked" not in result.stdout:
                raise HarnessError(f"state baseline failed\n{result.stdout}{result.stderr}")
        elif (result.returncode != 1 or
              "the proven STF context after 1 packets differs from upstream's" not in result.stderr):
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
            source = lean_probe(case, nonce)
            path.write_text(source)
            result = execute(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                             capture_output=True, timeout=TIMEOUT_SECONDS)
            validate_lean(case, nonce, result, path, source)
        except subprocess.TimeoutExpired as error:
            raise HarnessError(f"{case}: timed out after {TIMEOUT_SECONDS}s") from error
    boundary = ("the extern contract NanoP4Target.externsContractHolds (copied)"
                if case == "receiver" else f"lazy_eval in Probe.{case}")
    return case, "all probes" if case == "baseline" else boundary


def write_bundle():
    """Verify the pinned session recording and decompress it for check-consumer."""
    sys.path.insert(0, str(ROOT / "P4SpecTecTest/Oracle/NanoSwitch/Sessions"))
    import fixture  # noqa: E402
    _, data = fixture.read()
    BUNDLE.parent.mkdir(parents=True, exist_ok=True)
    temporary = BUNDLE.with_name(f"{BUNDLE.name}.{uuid.uuid4().hex}")
    temporary.write_bytes(data)
    temporary.replace(BUNDLE)


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
