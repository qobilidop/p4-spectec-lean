#!/usr/bin/env python3
"""Bounded semantic mutations, using scratch copies and compiled dependencies.

Run inside nix develop after lake build NanoP4Proofs and lake test. These
observations exercise three separate boundaries; they are not additional proofs.
"""

import json
from pathlib import Path
import subprocess
import re
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[3]
CASES = ("baseline", "behavior", "quotation", "representation")
PROBE_TIMEOUT_SECONDS = 60
# Replaying refinement is substantially slower than evaluating the runtime
# probe, especially on CI. Keep a bounded wall-clock guard independently of
# the unchanged 4M-heartbeat proof budget below.
PROOF_TIMEOUT_SECONDS = 300


class HarnessError(RuntimeError):
    """An execution failure, never an accepted semantic rejection."""


def replace_once(text, anchor, replacement):
    if text.count(anchor) != 1 or anchor == replacement:
        raise HarnessError(f"mutation anchor must occur exactly once: {anchor!r}")
    return text.replace(anchor, replacement, 1)


def extract(text, start, end):
    if text.count(start) != 1 or text.count(end) != 1:
        raise HarnessError("missing or ambiguous extraction boundary")
    return text.split(start, 1)[1].split(end, 1)[0]


def replace_exact(text, anchor, replacement, count):
    if text.count(anchor) != count:
        raise HarnessError(f"expected {count} namespace anchors: {anchor!r}")
    return text.replace(anchor, replacement)


def probe(case, nonce):
    if case not in CASES:
        raise HarnessError("unknown mutation")
    generated = (ROOT / "NanoP4Spec/8.04-eval-lvalue.lean").read_text()
    helper = "def «$update_fieldValue»\n" + extract(
        generated, "def «$update_fieldValue»\n", "def «$update_fieldValue».al")
    quote = "def «$update_fieldValue».al" + extract(
        generated, "def «$update_fieldValue».al", "def Lvalue_write.run")
    # The quotation is followed by no helper declarations at this pin.
    representation = (ROOT / "NanoP4Proofs/FieldUpdate/Representation.lean").read_text()
    scalar = "def Scalar.generated" + extract(
        representation, "def Scalar.generated", "/-- Embed an independently represented field")
    if case == "behavior":
        helper = replace_once(helper,
            "pure ((NanoP4Spec.fieldValue.semi value nameIR) :: «fieldValue_t*»)",
            "pure ((NanoP4Spec.fieldValue.semi value_field_h nameIR) :: «fieldValue_t*»)")
    if case == "quotation":
        quote = replace_once(quote, '(Q.i "update_fieldValue")\n       []',
                             '(Q.i "drift_update_fieldValue")\n       []')
    if case == "representation":
        scalar = replace_once(scalar, "| .unsigned w i => .W w i",
                              "| .unsigned w i => .S w i")
    helper = replace_exact(helper, 'NanoP4Spec.«$update_fieldValue»',
                           'Scratch.«$update_fieldValue»', 1)
    scalar = replace_once(scalar, "def Scalar.generated", "def scalarGenerated")
    export = json.dumps(str(ROOT / "exports/nano-p4.al.json"))
    return f'''import NanoP4Proofs.FieldUpdate.Correspondence
import P4SpecTecTest.Quote
set_option linter.missingDocs false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine
open NanoP4Proofs.FieldUpdate
namespace Scratch
{helper}
{quote}
{scalar}
end Scratch
def main : IO UInt32 := do
  let source ← P4SpecTec.Lang.Al.Json.readSpec {export}
  let selected := source.filter fun d => d.it.id.it == "update_fieldValue"
  if selected.length != 1 then throw (IO.userError "missing source helper")
  let quotation := (P4SpecTecTest.Quote.compareSpecs selected
    [Scratch.«$update_fieldValue».al]).isOk
  let name := ByteText.ofString "x"
  let fields : List Field := [⟨.unsigned 8 1, name⟩, ⟨.unsigned 8 2, name⟩]
  let replacement : Scalar := .unsigned 8 9
  let actual := Scratch.«$update_fieldValue» (generatedFields fields) name
    replacement.generated
  let reference := (referenceUpdate 100 (sourceFields fields)
    (Runtime.Value.Make.text name) replacement.source).run
  let behavior := match actual, reference with
    | some (.ok xs), some (.ok ys) =>
      Runtime.Value.eq (canon (toValue xs)) (canon ys)
    | _, _ => false
  let representation := Runtime.Value.eq (canon replacement.source)
    (canon (toValue (Scratch.scalarGenerated replacement)))
  IO.println s!"FIELD_UPDATE:{nonce}:{{quotation}}:{{behavior}}:{{representation}}"
  return 0
'''


def validate(case, nonce, returncode, stdout, stderr):
    expected = {"baseline": (True, True, True), "behavior": (True, False, True),
                "quotation": (False, True, True), "representation": (True, True, False)}[case]
    line = "FIELD_UPDATE:" + nonce + ":" + ":".join(str(x).lower() for x in expected)
    if returncode != 0 or stderr.strip() or stdout.strip() != line:
        raise HarnessError(f"{case}: invalid probe outcome (exit {returncode})\n"
                           f"stdout: {stdout}\nstderr: {stderr}")


def proof_probe(case, nonce):
    """Replay checked proof bodies against the independently compiled scratch definitions."""
    definitions = probe(case, nonce).split("def main : IO UInt32 := do", 1)[0]
    semantics = (ROOT / "NanoP4Proofs/FieldUpdate/Semantics.lean").read_text()
    behavior = "theorem generatedEqUpdate" + extract(
        semantics, "theorem generatedEqUpdate", "/-- info: 'NanoP4Proofs.FieldUpdate.generatedEqUpdate'")
    behavior = replace_exact(behavior, 'NanoP4Spec.«$update_fieldValue»',
                             'Scratch.«$update_fieldValue»', 3)
    emitted = (ROOT / "NanoP4Spec/Refinement/update_fieldValue.lean").read_text()
    refinement = "theorem _root_.NanoP4Spec.«$mutation_fieldValue».refines_group" + extract(emitted,
        "theorem «$update_fieldValue».refines_group",
        "theorem «$update_fieldValue».refines\n")
    refinement = replace_once(refinement, 'NanoP4Spec.«$update_fieldValue»',
                              'Scratch.«$update_fieldValue»')
    definitions += "set_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\n"
    if case != "quotation":
        definitions += ("example : Scratch.«$update_fieldValue».al = "
                        "NanoP4Spec.«$update_fieldValue».al := rfl\n")
    representation = (ROOT / "NanoP4Proofs/FieldUpdate/Representation.lean").read_text()
    adequacy = "theorem sourceRel" + extract(
        representation, "theorem Scalar.sourceRel",
        "/-- info: 'NanoP4Proofs.FieldUpdate.Scalar.sourceRel'")
    adequacy = replace_once(adequacy, "s.generated", "(Scratch.scalarGenerated s)")
    obligations = refinement if case == "behavior" else adequacy if case == "representation" else (
        behavior + "\n" + adequacy if case == "quotation" else
        refinement + "\n" + behavior + "\n" + adequacy)
    start = definitions.count("\n") + 3
    source = definitions + "open NanoP4Spec\nnamespace ProofBoundary\n" + obligations
    end = source.count("\n") + 1
    source += f'\nend ProofBoundary\n#eval IO.println "PROOF_SUCCESS:{nonce}"\n'
    return source, start, end


def validate_proof(case, nonce, result, path, start, end):
    if case in ("baseline", "quotation"):
        if result.returncode or result.stderr.strip() or result.stdout.strip() != (
                "PROOF_SUCCESS:" + nonce):
            raise HarnessError(f"{case}: baseline proof failed\n{result.stdout}{result.stderr}")
        return
    diagnostics = re.findall(re.escape(str(path)) + r":(\d+):\d+: error: ([^\n]+)",
                             result.stdout)
    allowed = ("refine_al: values not related:",) if case == "behavior" else (
        "Tactic `rfl` failed",)
    if (result.returncode != 1 or result.stderr.strip() or not diagnostics or
            any(not start <= int(line) <= end or not message.startswith(allowed)
                for line, message in diagnostics) or
            result.stdout.count("error:") != len(diagnostics) or "warning:" in result.stdout or
            result.stdout.count("PROOF_SUCCESS:" + nonce) != 1):
        raise HarnessError(f"{case}: unrelated proof failure\n{result.stdout}{result.stderr}")


def run_case(case, execute=subprocess.run, probe_timeout=PROBE_TIMEOUT_SECONDS,
             proof_timeout=PROOF_TIMEOUT_SECONDS):
    nonce = uuid.uuid4().hex
    with tempfile.TemporaryDirectory(prefix="field-update-") as scratch:
        path = Path(scratch) / "Probe.lean"
        path.write_text(probe(case, nonce))
        try:
            result = execute(["lake", "env", "lean", "--run", str(path)],
                             cwd=ROOT, text=True, capture_output=True, timeout=probe_timeout)
        except subprocess.TimeoutExpired as error:
            raise HarnessError(f"{case}: probe timed out after {probe_timeout}s") from error
        validate(case, nonce, result.returncode, result.stdout, result.stderr)
        source, start, end = proof_probe(case, nonce)
        path.write_text(source)
        try:
            result = execute(["lake", "env", "lean", str(path)], cwd=ROOT,
                             text=True, capture_output=True, timeout=proof_timeout)
        except subprocess.TimeoutExpired as error:
            raise HarnessError(f"{case}: proof timed out after {proof_timeout}s") from error
        validate_proof(case, nonce, result, path, start, end)
    boundary = {"baseline": "all", "behavior": "update_fieldValue.refines_group",
                "quotation": "compareSpecs", "representation": "Scalar.sourceRel"}[case]
    return {"case": case, "boundary": boundary, "accepted": case == "baseline",
            "proof": "rejected" if case in ("behavior", "representation") else "checked"}


def main():
    try:
        results = [run_case(case) for case in CASES]
    except (HarnessError, OSError) as error:
        print(str(error))
        return 1
    print(json.dumps({"schema": 1, "results": results}, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
