#!/usr/bin/env python3
"""Distinguishing mutations of the full-P4 regression sweep, each rejected by a named status.

Runs on the observations that `sweep.py --regression` cached (the upstream shell is not
needed) and requires `lake` for the worker rebuilds. The baseline first passes on both legs
exactly as the sweep requires; each mutation must then change the outcome of exactly the
named programs to the named statuses on the named leg, and nothing else. Any other outcome,
including a build failure or a worker that does not restore to its baseline digest, is a
harness failure. These observations exercise the sweep's checking boundaries; they are not
additional proofs.

| Case | Layer | Mutation | Rejecting status |
|---|---|---|---|
| observedCounter | upstream observation | one accepted program's final counters incremented | `counter-disagreement`, both legs |
| observedOutput | upstream observation | one accepted program's outputs emptied | `output-disagreement`, both legs |
| observedClass | upstream observation | one accepted program recorded as rejected | `outcome-disagreement`, both legs |
| generatedRecordFields | generated code | the record expression's field-distinctness premise skipped | `outcome-disagreement` on the duplicate-field program, generated leg |
| interpreterConcat | reference interpreter | list concatenation evaluated in reverse order | `counter-disagreement` on every allocating program and `outcome-disagreement` on every other accepted one, interpreter leg |
| interpreterFresh | reference interpreter | every fresh-identifier allocation consumes two | `counter-disagreement` on every program that allocates, interpreter leg |

A code mutation is applied in place to the committed source (or the regenerated generated
module), the leg's worker rebuilt, and the leg rerun on the cached observations; the source
is then written back byte for byte and the worker rebuilt, which must restore its baseline
digest. The other leg's worker is untouched, so it is not rerun.
"""

import argparse
import gzip
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

import campaign
import contract
import inventory
import sweep


ROOT = sweep.ROOT
CACHE = ROOT / ".artifacts/p4-regression-sweep"
CASES = ("observedCounter", "observedOutput", "observedClass", "generatedRecordFields",
         "interpreterConcat", "interpreterFresh")
OBSERVED = "upstream/testdata/regression/sim/issue-197.p4"
DUPLICATE = "upstream/testdata/regression/neg/issue-207.p4"
WORKER_TIMEOUT = 1800
# The generated code's two record-expression rules (`multiple-non-default` and
# `multiple-default`) each check that the field names are distinct.
GENERATED = ROOT / "P4Spec/8-dynamic/8.02-evaluation-relation.lean"
DISTINCT = re.compile(r"(\(P4Spec\.«\$distinct_» \(τK := P4Spec\.nameIR\) «nameIR_f\*»\)\n"
                      r"\s+let _ ← StateEval\.liftEval \(Eval\.check )(tmp_\d+)\)")
INTERP = ROOT / "P4SpecTec/Interp/InterpAl/Interp.lean"
CONCAT = "pure (Value.Make.list typ_note.it (values_l ++ values_r))"
EFFECTS = ROOT / "P4SpecTec/Interp/Effects.lean"
FRESH = "pure (Value.Make.text (ByteText.ofString (← StateEval.freshTypeId)))"
DISAGREEMENT = ("output-disagreement", "counter-disagreement", "outcome-disagreement")


class HarnessError(RuntimeError):
    """An execution failure, never an accepted rejection."""


def replace_once(text, anchor, replacement):
    if text.count(anchor) != 1 or anchor == replacement:
        raise HarnessError(f"mutation anchor must occur exactly once: {anchor!r}")
    return text.replace(anchor, replacement, 1)


def skip_distinctness(text):
    """Both record-expression distinctness checks made to pass."""
    mutated, count = DISTINCT.subn(lambda m: m.group(1) + "true)", text)
    if count != 2:
        raise HarnessError(f"expected two record-expression distinctness checks, found {count}")
    return mutated


# What a code mutation changes: the file, the rewrite, the worker and the leg it rebuilds.
CODE = {
    "generatedRecordFields": (GENERATED, skip_distinctness, "generated"),
    "interpreterConcat": (INTERP, lambda text: replace_once(
        text, CONCAT, CONCAT.replace("values_l ++ values_r", "values_r ++ values_l")),
        "interpreter"),
    "interpreterFresh": (EFFECTS, lambda text: replace_once(
        text, FRESH, FRESH.replace("(← StateEval.freshTypeId)",
                                   "(← StateEval.freshTypeId *> StateEval.freshTypeId)")),
        "interpreter"),
}


def mutate_observation(case, observation):
    """A copy of one cached observation with the named change to both relations."""
    mutated = json.loads(json.dumps(observation))
    for run in mutated["relations"].values():
        if run["result"]["class"] != "pass":
            raise HarnessError("observation mutations need an accepted program")
        if case == "observedCounter":
            run["counterAfter"] += 1
        elif case == "observedOutput":
            run["result"]["outputs"] = []
        elif case == "observedClass":
            run["result"] = {"class": "unmatch", "diagnostic": {
                "code": None, "message": "mutated", "region": "", "source": "interp"}}
        else:
            raise HarnessError(f"not an observation mutation: {case}")
    return mutated


def load_cache():
    """The cached regression observations by candidate index, and the sweep's identity."""
    identity_path = CACHE / "identity.json"
    if not identity_path.is_file():
        raise HarnessError("run sweep.py --regression first; no cached observations")
    identity = json.loads(identity_path.read_text())
    harness = {path: campaign.file_digest(ROOT / path) for path in sweep.HARNESS}
    if identity.get("harnessSha256") != harness:
        raise HarnessError("cached observations were captured by another harness revision")
    manifest = contract.strict_json(inventory.MANIFEST.read_bytes())
    for key in ("upstreamRevision", "p4cRevision", "inventorySha256"):
        if identity.get(key) != manifest[key]:
            raise HarnessError(f"cached observations were captured at another {key}")
    observations = {}
    for path in sorted((CACHE / "observations").glob("*.json.gz")):
        observations[int(path.name.split(".")[0])] = json.loads(
            gzip.decompress(path.read_bytes()))
    if list((CACHE / "observations").glob("*.err.json")) or not observations:
        raise HarnessError("the cached regression sweep is incomplete")
    if not all(name.startswith("upstream/testdata/regression/")
               for name in (o["name"] for o in observations.values())):
        raise HarnessError("the cache is not the regression set")
    return identity, observations


def statuses(records):
    """Each program's relation statuses, by program path; a failure record is its kind."""
    result = {}
    for record in records.values():
        found = sweep.statuses(record)
        result[record["name"]] = found if found else ("failure:" + record["failure"]["kind"],)
    return result


def changes(baseline, mutated):
    """The programs whose statuses the mutation changed, with their new statuses."""
    if set(baseline) != set(mutated):
        raise HarnessError("the mutated leg did not report every program")
    return {name: mutated[name] for name in sorted(mutated) if mutated[name] != baseline[name]}


def verify(case, expected, found):
    """Exactly the expected programs changed, to exactly the expected statuses."""
    if found != expected:
        raise HarnessError(f"{case}: changed {json.dumps(found, sort_keys=True)}, expected "
                           f"{json.dumps(expected, sort_keys=True)}")


def fresh_expectation(observations):
    """Doubling every allocation changes the final counter of exactly the programs that
    allocate, on both relations (the regression sessions allocate on both or neither)."""
    expected = {}
    for observation in observations.values():
        allocating = [run["counterAfter"] != run["counterAfterBoot"]
                      for run in (observation["relations"][name] for name in contract.RELATIONS)]
        if all(allocating):
            expected[observation["name"]] = ("counter-disagreement",) * len(contract.RELATIONS)
        elif any(allocating):
            raise HarnessError(f"{observation['name']}: allocates on one relation only")
    if len(expected) < 2:
        raise HarnessError("too few allocating programs for the fresh mutation")
    return expected


def concat_expectation(observations):
    """Reversed concatenation changes every accepted or allocating program: a program that
    allocates differs first in its final counter, which the worker checks before outcomes;
    an accepted program without allocation is no longer typed, so its outcome differs; a
    rejected program without allocation still fails with counter zero."""
    expected = {}
    for observation in observations.values():
        runs = [observation["relations"][name] for name in contract.RELATIONS]
        if all(run["counterAfter"] != run["counterAfterBoot"] for run in runs):
            expected[observation["name"]] = ("counter-disagreement",) * len(runs)
        elif all(run["result"]["class"] == "pass" for run in runs):
            expected[observation["name"]] = ("outcome-disagreement",) * len(runs)
    if len(expected) < 2:
        raise HarnessError("too few accepted or allocating programs for the concat mutation")
    return expected


def expectation(case, observations):
    if case == "observedCounter":
        return {OBSERVED: ("counter-disagreement",) * 2}
    if case == "observedOutput":
        return {OBSERVED: ("output-disagreement",) * 2}
    if case == "observedClass":
        return {OBSERVED: ("outcome-disagreement",) * 2}
    if case == "generatedRecordFields":
        return {DUPLICATE: ("outcome-disagreement",) * 2}
    if case == "interpreterConcat":
        return concat_expectation(observations)
    if case == "interpreterFresh":
        return fresh_expectation(observations)
    raise HarnessError(f"unknown case: {case}")


class Legs:
    """The two workers on a directory of observations, as the sweep runs them."""

    def __init__(self, limit, jobs, execute=subprocess.run, run_leg=sweep.run_leg):
        self.limit, self.jobs, self.execute, self.run_leg = limit, jobs, execute, run_leg

    def executable(self, leg):
        return ROOT / ".lake/build/bin" / sweep.LEGS[leg][0]

    def build(self, leg, log):
        with log.open("wb") as handle:
            result = self.execute(["lake", "build", "--wfail", sweep.LEGS[leg][0]], cwd=ROOT,
                                  stdout=handle, stderr=subprocess.STDOUT)
        if result.returncode:
            raise HarnessError(f"{leg} worker build failed; see {log}")

    def run(self, leg, directory):
        command = [str(self.executable(leg)), *sweep.LEGS[leg][1:],
                   "--max-case-bytes", str(self.limit)]
        return statuses(self.run_leg(leg, command, directory, WORKER_TIMEOUT, self.jobs))


def write_observations(directory, observations, mutate=None):
    """A directory of observations as the cache holds them, one optionally mutated."""
    for index, observation in observations.items():
        if mutate is not None and observation["name"] == OBSERVED:
            observation = mutate(observation)
        (directory / f"{index:04d}.json.gz").write_bytes(
            gzip.compress(json.dumps(observation, sort_keys=True).encode(), mtime=0))


def run_code_mutation(case, legs, directory, baseline, digests, log_dir, code=CODE):
    """Mutate, rebuild, run; always write the source back and rebuild to the baseline."""
    path, rewrite, leg = code[case]
    original = path.read_bytes()
    mutated = rewrite(original.decode("utf-8"))
    try:
        path.write_text(mutated)
        legs.build(leg, log_dir / f"{case}.build.log")
        if campaign.file_digest(legs.executable(leg)) == digests[leg]:
            raise HarnessError(f"{case}: the mutated worker has the baseline digest")
        found = changes(baseline[leg], legs.run(leg, directory))
    finally:
        path.write_bytes(original)
        legs.build(leg, log_dir / f"{case}.restore.log")
    if campaign.file_digest(legs.executable(leg)) != digests[leg]:
        raise HarnessError(f"{case}: the {leg} worker did not restore to its baseline digest")
    return leg, found


def run_case(case, legs, observations, baseline, digests, log_dir):
    expected = expectation(case, observations)
    with tempfile.TemporaryDirectory(prefix="p4-mutation-") as scratch:
        directory = Path(scratch)
        if case in CODE:
            write_observations(directory, observations)
            leg, found = run_code_mutation(case, legs, directory, baseline, digests, log_dir)
            verify(case, expected, found)
            return {"leg": leg, "changed": found}
        write_observations(directory, observations, lambda o: mutate_observation(case, o))
        found = {}
        for leg in sweep.LEGS:
            found[leg] = changes(baseline[leg], legs.run(leg, directory))
            verify(f"{case} ({leg})", expected, found[leg])
        return {"leg": "both", "changed": found[next(iter(sweep.LEGS))]}


def run_baseline(legs, observations):
    """Both legs on the unmutated cache must pass as the regression sweep requires."""
    candidates = [{"path": observations[index]["name"]} for index in sorted(observations)]
    with tempfile.TemporaryDirectory(prefix="p4-mutation-") as scratch:
        directory = Path(scratch)
        write_observations(directory, observations)
        records = {leg: legs.run_leg(leg, [str(legs.executable(leg)), *sweep.LEGS[leg][1:],
                                           "--max-case-bytes", str(legs.limit)],
                                     directory, WORKER_TIMEOUT, legs.jobs)
                   for leg in sweep.LEGS}
    problems = sweep.unexpected(candidates, [], records)
    if problems:
        raise HarnessError("baseline does not pass: " + "; ".join(problems[:5]))
    return {leg: statuses(leg_records) for leg, leg_records in records.items()}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    parser.add_argument("--jobs", type=int, default=8)
    parser.add_argument("--only", choices=CASES, action="append",
                        help="run only these mutations (the baseline always runs)")
    args = parser.parse_args(argv)
    identity, observations = load_cache()
    legs = Legs(identity["maxCaseBytes"], args.jobs)
    log_dir = CACHE / "mutations"
    log_dir.mkdir(exist_ok=True)
    for leg in sweep.LEGS:
        legs.build(leg, log_dir / f"baseline-{leg}.build.log")
    digests = {leg: campaign.file_digest(legs.executable(leg)) for leg in sweep.LEGS}
    started = time.monotonic()
    baseline = run_baseline(legs, observations)
    print(f"[p4-mutations] baseline: both legs pass on {len(observations)} programs")
    report = {"candidates": len(observations), "workers": digests, "cases": {}}
    for case in args.only or CASES:
        outcome = run_case(case, legs, observations, baseline, digests, log_dir)
        report["cases"][case] = outcome
        where = "both legs" if outcome["leg"] == "both" else f"the {outcome['leg']} leg"
        print(f"[p4-mutations] {case}: rejected on {where}, "
              f"{len(outcome['changed'])} program(s) changed")
    report["elapsedSeconds"] = round(time.monotonic() - started)
    (log_dir / "summary.json").write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    print(f"[p4-mutations] {len(report['cases'])} mutations rejected; {log_dir / 'summary.json'}")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (HarnessError, OSError, subprocess.SubprocessError) as error:
        print(f"[p4-mutations] harness failure: {error}", file=sys.stderr)
        sys.exit(1)
