#!/usr/bin/env python3
"""Policy regressions; add --lean under lake env to exercise the actual header parser."""

import importlib.util
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch


SPEC = importlib.util.spec_from_file_location(
    "boundaries", Path(__file__).with_name("check-library-boundaries.py")
)
BOUNDARIES = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(BOUNDARIES)
WITH_LEAN = "--lean" in sys.argv
if WITH_LEAN:
    sys.argv.remove("--lean")


def config_text():
    """Canonical small fixture matching the package's library classification."""
    defaults = ", ".join(f'"{name}"' for name in sorted(BOUNDARIES.REUSABLE))
    libraries = "\n".join(
        f'[[lean_lib]]\nname = "{name}"'
        for name in sorted(BOUNDARIES.REUSABLE | BOUNDARIES.CONSUMERS)
    )
    return f'defaultTargets = [{defaults}]\ntestDriver = "P4SpecTecTest"\n{libraries}\n'


class Fixture(unittest.TestCase):
    """A temporary package with all required roots, independent of working-tree edits."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.write("lakefile.toml", config_text())
        for name in BOUNDARIES.REUSABLE | BOUNDARIES.CONSUMERS:
            self.write(f"{name}.lean", "prelude\n")

    def write(self, name, content):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(content, encoding="utf-8")
        return path

    def graph(self, edges):
        return {self.root / source: {self.root / dep for dep in deps}
                for source, deps in edges.items()}


class PolicyTests(Fixture):
    def test_configuration(self):
        BOUNDARIES.check_config(self.root)

    def test_package_source_override_rejected(self):
        self.write("lakefile.toml", 'srcDir = "alternate"\n' + config_text())
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "package srcDir"):
            BOUNDARIES.check_config(self.root)

    def test_default_example_or_test_rejected(self):
        for name in BOUNDARIES.CONSUMERS:
            with self.subTest(name=name):
                self.write("lakefile.toml", config_text().replace('"P4Lib",', f'"{name}",'))
                with self.assertRaises(BOUNDARIES.BoundaryError):
                    BOUNDARIES.check_config(self.root)

    def test_example_must_be_a_library(self):
        self.write("lakefile.toml", config_text().replace(
            '[[lean_lib]]\nname = "ExampleProofs"',
            '[[lean_exe]]\nname = "ExampleProofs"',
        ))
        with self.assertRaises(BOUNDARIES.BoundaryError):
            BOUNDARIES.check_config(self.root)

    def test_duplicate_library_rejected(self):
        self.write("lakefile.toml", config_text() + '[[lean_lib]]\nname = "P4Lib"\n')
        with self.assertRaises(BOUNDARIES.BoundaryError):
            BOUNDARIES.check_config(self.root)

    def test_unclassified_library_rejected(self):
        self.write("lakefile.toml", config_text() + '[[lean_lib]]\nname = "NewLibrary"\n')
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "explicit boundary classification"):
            BOUNDARIES.check_config(self.root)

    def test_unclassified_default_target_rejected(self):
        self.write("lakefile.toml", config_text().replace('"P4Lib",', '"example-run",'))
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "example-run"):
            BOUNDARIES.check_config(self.root)

    def test_source_overrides_rejected(self):
        for override in ('srcDir = "examples"', 'roots = ["ExampleProofs"]',
                         'globs = ["ExampleProofs.+"]'):
            with self.subTest(override=override):
                self.write("lakefile.toml", config_text().replace(
                    'name = "P4Lib"', f'name = "P4Lib"\n{override}'))
                with self.assertRaises(BOUNDARIES.BoundaryError):
                    BOUNDARIES.check_config(self.root)

    def test_direct_consumers_rejected(self):
        for consumer in ("ExampleProofs.lean", "P4SpecTecTest/Smoke.lean"):
            with self.subTest(consumer=consumer):
                graph = self.graph({"P4Lib.lean": [consumer]})
                with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "imports a consumer"):
                    BOUNDARIES.check_graph(graph, {self.root / "P4Lib.lean"}, self.root)

    def test_transitive_bridge_rejected(self):
        graph = self.graph({"P4Lib.lean": ["Bridge.lean"],
                            "Bridge.lean": ["ExampleProofs/Proof.lean"]})
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Bridge.lean -> ExampleProofs"):
            BOUNDARIES.check_graph(graph, {self.root / "P4Lib.lean"}, self.root)

    def test_examples_may_depend_on_libraries(self):
        graph = self.graph({"P4Lib.lean": [], "ExampleProofs.lean": ["P4Lib.lean"]})
        BOUNDARIES.check_graph(graph, {self.root / "P4Lib.lean"}, self.root)

    def test_cycles_and_namespace_prefixes_allowed(self):
        graph = self.graph({"P4Lib.lean": ["ExampleProofsExtra.lean"],
                            "ExampleProofsExtra.lean": ["P4Lib.lean"]})
        BOUNDARIES.check_graph(graph, {self.root / "P4Lib.lean"}, self.root)

    def test_missing_graph_input_rejected(self):
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "missing parsed"):
            BOUNDARIES.check_graph(self.graph({"P4Lib.lean": ["Bridge.lean"]}),
                                   {self.root / "P4Lib.lean"}, self.root)

    def test_missing_root_rejected(self):
        (self.root / "P4Lib.lean").unlink()
        with patch.object(BOUNDARIES, "run", return_value=""):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "missing source"):
                BOUNDARIES.source_inventory(self.root)

    def test_missing_tracked_module_rejected(self):
        with patch.object(BOUNDARIES, "run", return_value="P4Lib/Deleted.lean\0"):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Deleted"):
                BOUNDARIES.source_inventory(self.root)

    def test_new_untracked_module_included(self):
        source = self.write("P4Lib/New.lean", "prelude\n")
        with patch.object(BOUNDARIES, "run", return_value=""):
            self.assertIn(source, BOUNDARIES.source_inventory(self.root))

    def test_unreadable_source_rejected(self):
        with patch.object(Path, "open", side_effect=PermissionError("denied")):
            with self.assertRaises(PermissionError):
                BOUNDARIES.require_source(self.root / "P4Lib.lean")

    def test_unreadable_directory_rejected(self):
        (self.root / "P4Lib").mkdir()
        def failed_walk(directory, onerror):
            onerror(PermissionError("cannot enumerate P4Lib"))
        with patch.object(BOUNDARIES.os, "walk", side_effect=failed_walk):
            with self.assertRaisesRegex(PermissionError, "cannot enumerate"):
                BOUNDARIES.source_inventory(self.root)

    def test_parser_process_failures_rejected(self):
        sources = {self.root / "P4Lib.lean"}
        for error in (FileNotFoundError("lean"), UnicodeDecodeError("utf8", b"\xff", 0, 1, "bad")):
            with self.subTest(error=error), patch.object(subprocess, "run", side_effect=error):
                with self.assertRaises(BOUNDARIES.BoundaryError):
                    BOUNDARIES.parse_dependencies(sources, self.root)
        with patch.object(subprocess, "run", return_value=subprocess.CompletedProcess(
                ["lean"], 1, "", "parser failure")):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "parser failure"):
                BOUNDARIES.parse_dependencies(sources, self.root)

    def test_malformed_or_incomplete_parser_output_rejected(self):
        for output in ("not json", "{}", "[]", '[{"source":42,"dependencies":[]}]'):
            with self.subTest(output=output), patch.object(BOUNDARIES, "run", return_value=output):
                with self.assertRaises(BOUNDARIES.BoundaryError):
                    BOUNDARIES.parse_dependencies({self.root / "P4Lib.lean"}, self.root)

    def test_missing_helper_rejected(self):
        with patch.object(BOUNDARIES, "HELPER", self.root / "MissingHelper.lean"):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "MissingHelper"):
                BOUNDARIES.parse_dependencies({self.root / "P4Lib.lean"}, self.root)

    def test_full_closure_checks_disconnected_library_module(self):
        source = self.write("P4Lib/Unused.lean", "prelude\n")
        graph = {self.root / f"{name}.lean": set() for name in BOUNDARIES.REUSABLE}
        graph[source] = {self.root / "ExampleProofs.lean"}
        with patch.object(BOUNDARIES, "run", return_value=""):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Unused.lean"):
                BOUNDARIES.check(self.root, parser=lambda sources, root: graph)


@unittest.skipUnless(WITH_LEAN, "pass --lean under lake env for pinned-parser integration")
class LeanParserTests(Fixture):
    def parse(self, content):
        source = self.write("Header.lean", content)
        return BOUNDARIES.parse_dependencies({source}, self.root)[source]

    def test_header_syntax(self):
        quoted = self.write("ExampleProofs/with.dot.lean", "prelude\n")
        dependencies = self.parse(
            "module\n/- outer /- nested -/ import P4SpecTecTest -/\n"
            "public import\n ExampleProofs.«with.dot»\npublic import P4Lib\n"
            "meta import ExampleProofs\nimport P4Spec\n"
            '-- import P4SpecTecTest\ndef text := "import P4SpecTecTest"\n'
        )
        self.assertIn(quoted, dependencies)
        self.assertIn(self.root / "ExampleProofs.lean", dependencies)
        self.assertIn(self.root / "P4Lib.lean", dependencies)
        self.assertNotIn(self.root / "P4SpecTecTest.lean", dependencies)

    def test_parser_errors_rejected(self):
        for header in ("import\n", "import ExampleProofs.«unterminated\n",
                       "/- unclosed comment", "import ExampleProofs.\n"):
            with self.subTest(header=header):
                with self.assertRaises(BOUNDARIES.BoundaryError):
                    self.parse(header)

    def test_missing_dependency_rejected(self):
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "missing source"):
            self.parse("import ExampleProofs.Missing\n")

    def test_missing_parser_input_rejected(self):
        with self.assertRaises(BOUNDARIES.BoundaryError):
            BOUNDARIES.parse_dependencies({self.root / "Missing.lean"}, self.root)

    def test_full_parser_closure_rejects_bridge(self):
        self.write("P4Lib.lean", "import Bridge\n")
        self.write("Bridge.lean", "import\n ExampleProofs\n")
        with patch.object(BOUNDARIES, "source_inventory", return_value={self.root / "P4Lib.lean"}):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Bridge.lean -> ExampleProofs"):
                BOUNDARIES.check(self.root)


if __name__ == "__main__":
    unittest.main()
