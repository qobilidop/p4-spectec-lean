#!/usr/bin/env python3
"""Cross-layer distinguishing mutations of the Nano certification, each rejected by a named check.

Run inside nix develop after `lake build check-quotes` and the default targets. Every probe
first passes unmutated; each mutation must then be rejected by its named check with its named
diagnostic, and must be observable, so that a rejection is never mere proof-script brittleness.
Any other outcome, including a timeout or an unrelated diagnostic, is a harness failure. These
observations exercise checking boundaries across layers; they are not additional proofs.

| Case | Layer | Mutation | Rejecting check |
|---|---|---|---|
| ordering | generated code | the catch-all last alternative of `$expression_is_lvalue` tried first | its replayed forward certificate |
| failureKind | generated code | the first alternative's failed guard made an error instead of a mismatch | its replayed forward certificate |
| constructor | generated quotation | `DROP` omitted from the quotation of `forwardingDecision` | `compareSpecs`, as `check-quotes` runs it |
| quotation | generated quotation | a premise of `$expression_is_lvalue`'s quotation changed | `compareSpecs`, as `check-quotes` runs it |
| printProvenance | export | a print hint added to `DROP` in a copy of the pinned export | `check-quotes` itself, on the copy |

The two code mutations run a copy of the generated definition and of its generated refinement
proof in a scratch namespace; the copy is the generator's output text, never hand-written. The
quotation cases compare copies of the compiled quotations with the decoded export exactly as
`check-quotes` does; the proofs cannot see them, since they are relative to the compiled
quotation. Quotation comparison erases hint metadata by design, so the print mutation must be
rejected by the separate empty-hint check. Corrupted target state is covered by the
source-address filter's `receiver`, `extern` and `state` mutations
(`ExampleProofs/NanoP4SrcAddrFilter/test/run.py`).
"""

from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import uuid

ROOT = Path(__file__).resolve().parents[4]
CASES = ("baseline", "ordering", "failureKind", "constructor", "quotation", "printProvenance")
# Replaying the refinement proof is the slow step; the heartbeat budget stays the generated one.
TIMEOUT_SECONDS = 900
CHECK_QUOTES = ROOT / ".lake/build/bin/check-quotes"
EXPORT = ROOT / "exports/nano-p4.al.json"
FUNCTION = "«$expression_is_lvalue»"
LVALUE = ROOT / "NanoP4Spec/5.04-typing-lvalue.lean"
DECISION = ROOT / "NanoP4Spec/9-nano-switch.lean"
REFINEMENT = ROOT / "NanoP4Spec/Refinement/Forward/expression_is_lvalue.lean"
GUARD = "let _ ← Eval.check (NanoP4Spec.expression.is_nonTypeName expression)"
FIRST = (GUARD + "\n        let tmp_0 ← Eval.err? (NanoP4Spec.expression.of_nonTypeName expression)"
         "\n        have referenceExpression := tmp_0\n        pure true")
LAST = "pure false"
DROP = ',\n              Q.tc (.Atom (Q.a (.Keyword "DROP"))) "forwardingDecision" []'
PREMISE = '(.MixopSC [.Seq [.Arg (), .Atom (Q.a (.Operator ".")), .Arg ()]])'


class HarnessError(RuntimeError):
    """An execution failure, never an accepted semantic rejection."""


def replace_once(text, anchor, replacement):
    if text.count(anchor) != 1 or anchor == replacement:
        raise HarnessError(f"mutation anchor must occur exactly once: {anchor!r}")
    return text.replace(anchor, replacement, 1)


def extract(text, start, end):
    """The text from the unique `start` up to, excluding, the unique `end`."""
    if text.count(start) != 1 or text.count(end) != 1:
        raise HarnessError(f"missing or ambiguous extraction boundary: {start!r}")
    return start + text.split(start, 1)[1].split(end, 1)[0]


def extract_declaration(text, start):
    """The declaration beginning at the unique `start`, up to the next blank-line boundary."""
    if text.count(start) != 1:
        raise HarnessError(f"missing or ambiguous declaration: {start!r}")
    rest = text.split(start, 1)[1]
    if "\n\n" not in rest:
        raise HarnessError(f"unterminated declaration: {start!r}")
    return start + rest.split("\n\n", 1)[0] + "\n"


def definition(case):
    """The generated definition, copied and optionally mutated."""
    text = extract(LVALUE.read_text(), f"def {FUNCTION} ", f"def {FUNCTION}.al")
    text = replace_once(text, f"NanoP4Spec.{FUNCTION} expression", f"Scratch.{FUNCTION} expression")
    if case == "ordering":
        # Swap the first alternative's body with the catch-all last one's; the do blocks keep
        # their own indentation, so each body is re-indented to the block it moves into.
        first = extract(text, "have expression := p0\n        " + GUARD, ") <|>\n     ((do")
        last = extract(text, "have expression := p0\n          " + LAST, "))))\n  partial_fixpoint")
        if not first.endswith("pure true"):
            raise HarnessError("unexpected first alternative")
        text = replace_once(text, first, last.replace("\n          ", "\n        "))
        text = replace_once(text, "\n          " + last, "\n          " +
                            first.replace("\n        ", "\n          "))
    if case == "failureKind":
        text = replace_once(text, GUARD, GUARD.replace(
            "Eval.check (NanoP4Spec.expression.is_nonTypeName expression)",
            "Eval.err? (if NanoP4Spec.expression.is_nonTypeName expression then some () "
            "else none)"))
    return text


def quotations(case):
    """The compiled quotations of the type and the function, copied and optionally mutated."""
    decision = extract_declaration(DECISION.read_text(), "def forwardingDecision.al ")
    function = extract_declaration(LVALUE.read_text(), f"def {FUNCTION}.al ")
    if case == "constructor":
        decision = replace_once(decision, DROP, "")
    if case == "quotation":
        function = replace_once(function, PREMISE, PREMISE.replace('"."', '"->"'))
    return decision + "\n" + function


def refinement():
    """The generated forward refinement proof, stated about the scratch copy."""
    text = REFINEMENT.read_text()
    body = extract(text, f"theorem {FUNCTION}.refines_group", f"theorem {FUNCTION}.refines\n")
    body, count = re.subn(r"\n\nset_option maxHeartbeats \d+ in\n$", "\n", body)
    if count != 1:
        raise HarnessError("missing or ambiguous refinement theorem boundary")
    body = replace_once(body, f"theorem {FUNCTION}.refines_group",
                        "theorem _root_.NanoP4Spec.«$mutation_expression_is_lvalue».refines_group")
    return replace_once(body, f"(ExceptT.mk (NanoP4Spec.{FUNCTION} p0))",
                        f"(ExceptT.mk (Scratch.{FUNCTION} p0))")


HEADER = """import NanoP4Spec.Refinement.Forward.expression_is_lvalue
import P4SpecTec.Codegen.QuoteCheck
set_option linter.missingDocs false
set_option linter.unusedVariables false
set_option maxRecDepth 8192
open P4SpecTec P4SpecTec.Prelude P4SpecTec.Refine
namespace Scratch
"""


def probe(case, nonce):
    """Runtime observation of the copies and the quotation comparisons."""
    export = json.dumps(str(EXPORT))
    return HEADER + definition(case) + "\n" + quotations(case) + f"""end Scratch

def main : IO UInt32 := do
  let source ← P4SpecTec.Lang.Al.Json.readSpec {export}
  let compare (id : String) (quote : Lang.Al.def) : Bool :=
    let selected := source.filter fun d => d.it.id.it == id
    selected.length == 1 && (P4SpecTec.Codegen.QuoteCheck.compareSpecs selected [quote]).isOk
  let outcome : Option (Except Fail Bool) → String
    | none => "diverges" | some (.ok b) => s!"ok {{b}}" | some (.error f) => s!"{{repr f}}"
  let same (e : NanoP4Spec.expression) : Bool :=
    outcome (Scratch.{FUNCTION} e) == outcome (NanoP4Spec.{FUNCTION} e)
  let observed := [same .APPLY, same .TRUE,
    compare "forwardingDecision" Scratch.forwardingDecision.al,
    compare "expression_is_lvalue" Scratch.{FUNCTION}.al]
  IO.println s!"CROSS_LAYER:{nonce}:{{observed}}"
  return 0
"""


EXPECTED = {"baseline": [True, True, True, True], "ordering": [False, True, True, True],
            "failureKind": [True, False, True, True], "constructor": [True, True, False, True],
            "quotation": [True, True, True, False]}


def validate_probe(case, nonce, result):
    line = f"CROSS_LAYER:{nonce}:[{', '.join(str(x).lower() for x in EXPECTED[case])}]"
    if result.returncode or result.stderr.strip() or result.stdout.strip() != line:
        raise HarnessError(f"{case}: invalid probe outcome (exit {result.returncode})\n"
                           f"expected: {line}\nstdout: {result.stdout}\nstderr: {result.stderr}")


def proof_probe(case, nonce):
    """The copied definition with its copied refinement proof; returns the proof's line span."""
    source = HEADER + definition(case) + "end Scratch\n"
    start = source.count("\n") + 1
    source += refinement()
    end = source.count("\n") + 1
    return source + f'#eval IO.println "PROOF_DONE:{nonce}"\n', start, end


# The replayed proof's own diagnosis of each code mutation.
REJECTION = {"ordering": "refine_al: the interpreter chooses but the generated code does not",
             "failureKind": "refine_al: the interpreter fails but the generated code does not "
                            "fail alike"}


def validate_proof(case, nonce, result, path, start, end):
    if case == "baseline":
        if result.returncode or result.stderr.strip() or result.stdout.strip() != (
                "PROOF_DONE:" + nonce):
            raise HarnessError(f"baseline proof failed\n{result.stdout}{result.stderr}")
        return
    diagnostics = re.findall(re.escape(str(path)) + r":(\d+):\d+: error: ([^\n]+)", result.stdout)
    if (result.returncode != 1 or result.stderr.strip() or not diagnostics or
            any(not start <= int(line) < end or not message.startswith(REJECTION[case])
                for line, message in diagnostics) or
            result.stdout.count("error:") != len(diagnostics) or "warning:" in result.stdout or
            result.stdout.count("PROOF_DONE:" + nonce) != 1):
        raise HarnessError(f"{case}: unrelated proof outcome\n{result.stdout}{result.stderr}")


def hinted_export():
    """The pinned export with a print hint on `DROP`, a valid hint for a nullary case."""
    spec = json.loads(EXPORT.read_text())
    cases = [d for d in spec if d["it"][0] == "TypD" and d["it"][1]["it"] == "forwardingDecision"]
    if len(cases) != 1:
        raise HarnessError("missing or ambiguous forwardingDecision declaration")
    variants = cases[0]["it"][3]["it"]
    if variants[0] != "VariantT" or len(variants[1]) != 2:
        raise HarnessError("unexpected forwardingDecision shape")
    drop = variants[1][1]
    if drop[2] != []:
        raise HarnessError("forwardingDecision DROP already carries hints")
    region = drop[0]["at"]
    drop[2] = [{"it": {"hintid": {"it": "print", "note": None, "at": region},
                       "hintexp": {"it": ["TextE", "drop"], "note": None, "at": region}},
                "note": None, "at": region}]
    return spec


def run_print(execute, scratch):
    """Run `check-quotes` itself with its working directory on an exported copy."""
    for label in ("baseline", "mutant"):
        exports = scratch / label / "exports"
        exports.mkdir(parents=True)
        spec = json.loads(EXPORT.read_text()) if label == "baseline" else hinted_export()
        (exports / EXPORT.name).write_text(json.dumps(spec))
        result = execute([str(CHECK_QUOTES)], cwd=scratch / label, text=True,
                         capture_output=True, timeout=TIMEOUT_SECONDS)
        if label == "baseline":
            if result.returncode or result.stderr.strip() or (
                    "decoded and compiled Nano print environments are empty" not in result.stdout):
                raise HarnessError(f"print baseline failed\n{result.stdout}{result.stderr}")
        elif (result.returncode != 1 or "definitions match the decoded export" not in result.stdout
              or result.stderr.strip() !=
              "[quotes] decoded Nano print hints are nonempty; revise the print contract"):
            raise HarnessError(f"print mutation not rejected\n{result.stdout}{result.stderr}")
    return "check-quotes empty print-hint check (quotations still match)"


def run_case(case, execute=subprocess.run):
    nonce = uuid.uuid4().hex
    with tempfile.TemporaryDirectory(prefix="nano-cross-layer-") as scratch:
        scratch = Path(scratch)
        try:
            if case == "printProvenance":
                return case, run_print(execute, scratch)
            path = scratch / "Probe.lean"
            path.write_text(probe(case, nonce))
            result = execute(["lake", "env", "lean", "--run", str(path)], cwd=ROOT, text=True,
                             capture_output=True, timeout=TIMEOUT_SECONDS)
            validate_probe(case, nonce, result)
            if case in ("baseline", "ordering", "failureKind"):
                source, start, end = proof_probe(case, nonce)
                path.write_text(source)
                result = execute(["lake", "env", "lean", str(path)], cwd=ROOT, text=True,
                                 capture_output=True, timeout=TIMEOUT_SECONDS)
                validate_proof(case, nonce, result, path, start, end)
        except subprocess.TimeoutExpired as error:
            raise HarnessError(f"{case}: timed out after {TIMEOUT_SECONDS}s") from error
    boundary = {"baseline": "all probes",
                "ordering": f"NanoP4Spec.{FUNCTION}.refines_group (replayed)",
                "failureKind": f"NanoP4Spec.{FUNCTION}.refines_group (replayed)",
                "constructor": "compareSpecs (check-quotes)",
                "quotation": "compareSpecs (check-quotes)"}[case]
    return case, boundary


def main():
    # The baseline must pass before any rejection counts.
    print("[cross-layer] baseline: " + run_case("baseline")[1])
    with ThreadPoolExecutor(max_workers=3) as pool:
        for case, boundary in pool.map(run_case, CASES[1:]):
            print(f"[cross-layer] {case} mutation rejected at {boundary}")
    print(f"[cross-layer] {len(CASES) - 1} mutations rejected")


if __name__ == "__main__":
    try:
        main()
    except (HarnessError, OSError) as error:
        print(f"[cross-layer] harness failure: {error}", file=sys.stderr)
        sys.exit(1)
