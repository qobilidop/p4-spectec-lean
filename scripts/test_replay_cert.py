#!/usr/bin/env python3
"""Certificate replay copies select theorems and add options without changing others."""

import importlib.util
import io
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("replay_cert", ROOT / "scripts/replay-cert.py")
replay = importlib.util.module_from_spec(spec)
spec.loader.exec_module(replay)

MODULE = """import P4SpecTec.Prelude
import NanoP4Spec.Refinement.Spec

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace NanoP4Spec

theorem R.refines_group :
    True := by
  trivial

#audit_axioms NanoP4Spec.R.refines_group

theorem R.refines
    (x : Nat) :
    True := trivial

#audit_axioms NanoP4Spec.R.refines

private def R.realizesMotive
    (q : Nat) : Prop :=
  True

/-- A documented reverse theorem. -/
theorem R.realizes : True := trivial

#audit_axioms NanoP4Spec.R.realizes

end NanoP4Spec
"""

HOISTED = MODULE.replace(
    "#audit_axioms NanoP4Spec.R.refines_group\n\n", "").replace(
    "#audit_axioms NanoP4Spec.R.refines\n\n", "").replace(
    "#audit_axioms NanoP4Spec.R.realizes\n\n",
    "#audit_axioms NanoP4Spec.R.refines_group\n"
    "#audit_axioms NanoP4Spec.R.refines\n"
    "#audit_axioms NanoP4Spec.R.realizes\n\n")


class ReplayTest(unittest.TestCase):
    def test_no_selection_is_identity(self):
        self.assertEqual(replay.select(MODULE, []), MODULE)

    def test_selection_keeps_matching_theorems_and_all_definitions(self):
        kept = replay.select(MODULE, ["realizes"])
        self.assertIn("theorem R.realizes", kept)
        self.assertIn("#audit_axioms NanoP4Spec.R.realizes", kept)
        self.assertIn("private def R.realizesMotive", kept)
        self.assertIn("A documented reverse theorem", kept)
        self.assertNotIn("R.refines", kept)
        self.assertTrue(kept.rstrip().endswith("end NanoP4Spec"))

    def test_prefix_selection_keeps_group_and_corollary(self):
        kept = replay.select(MODULE, ["refines"])
        self.assertIn("theorem R.refines_group", kept)
        self.assertIn("theorem R.refines\n", kept)
        self.assertNotIn("theorem R.realizes", kept)

    def test_hoisted_audits_follow_their_theorems(self):
        kept = replay.select(HOISTED, ["refines"])
        self.assertIn("#audit_axioms NanoP4Spec.R.refines_group", kept)
        self.assertIn("#audit_axioms NanoP4Spec.R.refines\n", kept)
        self.assertNotIn("#audit_axioms NanoP4Spec.R.realizes", kept)
        self.assertNotIn("theorem R.realizes", kept)

    def test_options_follow_the_preamble(self):
        text = replay.instrument(MODULE, replay.options(1000, True, False))
        lines = text.splitlines()
        first = lines.index("set_option maxHeartbeats 4000000")
        self.assertEqual(lines[first + 1], "set_option maxHeartbeats 1000")
        self.assertEqual(lines[first + 2], "set_option refine_al.trace true")
        self.assertEqual(replay.instrument(MODULE, []), MODULE)

    def test_scoped_option_after_preamble_is_not_an_anchor(self):
        scoped = MODULE.replace("theorem R.realizes", "set_option maxRecDepth 1 in\ntheorem R.realizes")
        lines = replay.instrument(scoped, ["set_option pp.all true"]).splitlines()
        self.assertEqual(lines[lines.index("set_option maxHeartbeats 4000000") + 1],
                         "set_option pp.all true")

    def test_budgeted_theorem_is_selected_and_its_budget_overridden(self):
        budgeted = MODULE.replace("theorem R.realizes",
                                  "set_option maxHeartbeats 30000000 in\ntheorem R.realizes")
        kept = replay.select(budgeted, ["refines"])
        self.assertNotIn("R.realizes", kept.replace("R.realizesMotive", ""))
        self.assertIn("set_option maxHeartbeats 30000000 in",
                      replay.select(budgeted, ["realizes"]))
        overridden = replay.instrument(budgeted, replay.options(1000, False, False))
        self.assertNotIn("30000000", overridden)
        self.assertIn("theorem R.realizes", overridden)
        self.assertIn("30000000", replay.instrument(budgeted, ["set_option pp.all true"]))

    def test_generated_modules_keep_what_kept_theorems_use(self):
        # Every theorem named in a kept chunk and defined in the module is kept too.
        directory = ROOT / "NanoP4Spec/Refinement"
        paths = (list(directory.glob("*.lean")) + list(directory.glob("Forward/*.lean")) +
                 list(directory.glob("Reverse/*.lean")))
        for path in sorted(paths):
            text = path.read_text()
            theorems = [name for _, kind, name in
                        ((c, *replay.chunk_kind(c)) for c in replay.chunks(text))
                        if kind == "theorem"]
            for word in ("refines", "realizes"):
                kept = replay.select(text, [word])
                kept_theorems = [name for kind, name in map(replay.chunk_kind,
                                 replay.chunks(kept)) if kind == "theorem"]
                for name in theorems:
                    if name not in kept_theorems:
                        self.assertFalse(replay.mentions(kept, name), (path.name, word, name))

    def test_builtin_selection_keeps_dispatch(self):
        text = (ROOT / "NanoP4Spec/Refinement/add_map.lean").read_text()
        kept = replay.select(text, ["refines"])
        self.assertIn("«$add_map».dispatch", kept)
        self.assertNotIn("theorem «$add_map».realizes", kept)

    def test_selection_uses_full_names(self):
        text = (ROOT / "NanoP4Spec/Refinement/Forward/Type_eq.lean").read_text()
        kept = replay.select(text, ["ParameterType_eq"])
        self.assertIn("theorem ParameterType_eq.refines", kept)

    def test_aggregate_resolves_to_direction_proofs(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            refinement = root / "Fixture/Refinement"
            (refinement / "Forward").mkdir(parents=True)
            (refinement / "Reverse").mkdir()
            aggregate = refinement / "R.lean"
            aggregate.write_text("import Fixture.Refinement.Forward.R\n"
                                 "import Fixture.Refinement.Reverse.R\n")
            forward = refinement / "Forward/R.lean"
            reverse = refinement / "Reverse/R.lean"
            forward.write_text("theorem R.refines : True := trivial\n")
            reverse.write_text("theorem R.realizes : True := trivial\n")
            with patch.object(replay, "ROOT", root):
                self.assertEqual(replay.directional_sources(aggregate, []), [forward, reverse])
                self.assertEqual(replay.directional_sources(aggregate, ["refines"]), [forward])
                self.assertEqual(replay.directional_sources(aggregate, ["realizes"]), [reverse])
                self.assertEqual(replay.directional_sources(aggregate, ["R"]), [forward, reverse])
                self.assertEqual(replay.selected_theorems(aggregate.read_text(), ["refines"]), [])
                self.assertEqual(replay.selected_theorems(forward.read_text(), ["refines"]),
                                 ["R.refines"])
                reverse.unlink()
                with self.assertRaisesRegex(ValueError, "incomplete directional aggregate"):
                    replay.directional_sources(aggregate, ["refines"])

    def test_each_requested_module_must_match_selection(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            refinement = root / "Fixture/Refinement"
            refinement.mkdir(parents=True)
            matching = refinement / "Matching.lean"
            unmatched = refinement / "Unmatched.lean"
            matching.write_text("theorem R.refines : True := trivial\n")
            unmatched.write_text("theorem S.realizes : True := trivial\n")
            with patch.object(replay, "ROOT", root):
                with self.assertRaises(SystemExit) as result:
                    replay.main([str(matching), str(unmatched), "--only", "refines",
                                 "--no-build"])
            self.assertEqual(result.exception.code, 2)

    def test_main_replays_direction_instead_of_empty_aggregate(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            refinement = root / "Fixture/Refinement"
            (refinement / "Forward").mkdir(parents=True)
            (refinement / "Reverse").mkdir()
            aggregate = refinement / "R.lean"
            aggregate.write_text("import Fixture.Refinement.Forward.R\n"
                                 "import Fixture.Refinement.Reverse.R\n")
            forward = refinement / "Forward/R.lean"
            reverse = refinement / "Reverse/R.lean"
            forward.write_text("theorem R.refines : True := trivial\n")
            reverse.write_text("theorem R.realizes : True := trivial\n")
            seen = []

            def checked(source, _args):
                seen.append(source)
                return source, 0, 0.0, root / "replay.log"

            with patch.object(replay, "ROOT", root), \
                    patch.object(replay, "missing_imports", return_value=[]), \
                    patch.object(replay, "replay", side_effect=checked), \
                    patch("sys.stdout", io.StringIO()):
                self.assertEqual(replay.main([str(aggregate), "--only", "refines",
                                              "--no-build", "--jobs", "1"]), 0)
            self.assertEqual(seen, [forward])

    def test_imports_and_paths(self):
        self.assertEqual(replay.imports(MODULE),
                         ["P4SpecTec.Prelude", "NanoP4Spec.Refinement.Spec"])
        self.assertEqual(replay.module_path("NanoP4Spec.Refinement.Spec"),
                         ROOT / "NanoP4Spec/Refinement/Spec.lean")


if __name__ == "__main__":
    unittest.main()
