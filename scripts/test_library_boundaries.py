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
        for name in sorted(BOUNDARIES.LIBRARIES)
    )
    return f'defaultTargets = [{defaults}]\ntestDriver = "P4SpecTecTest"\n{libraries}\n'


class Fixture(unittest.TestCase):
    """A temporary package with all required roots, independent of working-tree edits."""

    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name).resolve()
        self.write("lakefile.toml", config_text())
        for name in BOUNDARIES.LIBRARIES:
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
                self.write("lakefile.toml", config_text().replace('"NanoP4Spec",', f'"{name}",'))
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
        self.write("lakefile.toml", config_text() + '[[lean_lib]]\nname = "P4SpecTec"\n')
        with self.assertRaises(BOUNDARIES.BoundaryError):
            BOUNDARIES.check_config(self.root)

    def test_unclassified_library_rejected(self):
        self.write("lakefile.toml", config_text() + '[[lean_lib]]\nname = "NewLibrary"\n')
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "explicit boundary classification"):
            BOUNDARIES.check_config(self.root)

    def test_unclassified_default_target_rejected(self):
        self.write("lakefile.toml", config_text().replace('"NanoP4Spec",', '"example-run",'))
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "example-run"):
            BOUNDARIES.check_config(self.root)

    def test_source_overrides_rejected(self):
        for override in ('srcDir = "examples"', 'roots = ["ExampleProofs"]',
                         'globs = ["ExampleProofs.+"]'):
            with self.subTest(override=override):
                self.write("lakefile.toml", config_text().replace(
                    'name = "P4SpecTec"', f'name = "P4SpecTec"\n{override}'))
                with self.assertRaises(BOUNDARIES.BoundaryError):
                    BOUNDARIES.check_config(self.root)

    def test_direct_consumers_rejected(self):
        for consumer in ("ExampleProofs.lean", "P4SpecTecTest/Smoke.lean", "Tools/Generate.lean"):
            with self.subTest(consumer=consumer):
                graph = self.graph({"P4SpecTec.lean": [consumer]})
                with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "imports a consumer"):
                    BOUNDARIES.check_graph(graph, {self.root / "P4SpecTec.lean"}, self.root)

    def test_transitive_bridge_rejected(self):
        graph = self.graph({"P4SpecTec.lean": ["Bridge.lean"],
                            "Bridge.lean": ["ExampleProofs/Proof.lean"]})
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Bridge.lean -> ExampleProofs"):
            BOUNDARIES.check_graph(graph, {self.root / "P4SpecTec.lean"}, self.root)

    def test_examples_may_depend_on_libraries(self):
        graph = self.graph({"P4SpecTec.lean": [], "ExampleProofs.lean": ["P4SpecTec.lean"]})
        BOUNDARIES.check_graph(graph, {self.root / "P4SpecTec.lean"}, self.root)

    def test_cycles_and_namespace_prefixes_allowed(self):
        graph = self.graph({"P4SpecTec.lean": ["ExampleProofsExtra.lean"],
                            "ExampleProofsExtra.lean": ["P4SpecTec.lean"]})
        BOUNDARIES.check_graph(graph, {self.root / "P4SpecTec.lean"}, self.root)

    def test_missing_graph_input_rejected(self):
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "missing parsed"):
            BOUNDARIES.check_graph(self.graph({"P4SpecTec.lean": ["Bridge.lean"]}),
                                   {self.root / "P4SpecTec.lean"}, self.root)

    def test_missing_root_rejected(self):
        (self.root / "P4SpecTec.lean").unlink()
        with patch.object(BOUNDARIES, "run", return_value=""):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "missing source"):
                BOUNDARIES.source_inventory(self.root)

    def test_missing_tracked_module_rejected(self):
        with patch.object(BOUNDARIES, "run", return_value="P4SpecTec/Deleted.lean\0"):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Deleted"):
                BOUNDARIES.source_inventory(self.root)

    def test_new_untracked_module_included(self):
        source = self.write("P4SpecTec/New.lean", "prelude\n")
        with patch.object(BOUNDARIES, "run", return_value=""):
            self.assertIn(source, BOUNDARIES.source_inventory(self.root))

    def test_unreadable_source_rejected(self):
        with patch.object(Path, "open", side_effect=PermissionError("denied")):
            with self.assertRaises(PermissionError):
                BOUNDARIES.require_source(self.root / "P4SpecTec.lean")

    def test_unreadable_directory_rejected(self):
        (self.root / "P4SpecTec").mkdir()
        def failed_walk(directory, onerror):
            onerror(PermissionError("cannot enumerate P4SpecTec"))
        with patch.object(BOUNDARIES.os, "walk", side_effect=failed_walk):
            with self.assertRaisesRegex(PermissionError, "cannot enumerate"):
                BOUNDARIES.source_inventory(self.root)

    def test_parser_process_failures_rejected(self):
        sources = {self.root / "P4SpecTec.lean"}
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
                    BOUNDARIES.parse_dependencies({self.root / "P4SpecTec.lean"}, self.root)

    def test_missing_helper_rejected(self):
        with patch.object(BOUNDARIES, "HELPER", self.root / "MissingHelper.lean"):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "MissingHelper"):
                BOUNDARIES.parse_dependencies({self.root / "P4SpecTec.lean"}, self.root)

    def test_full_closure_checks_disconnected_library_module(self):
        source = self.write("P4SpecTec/Unused.lean", "prelude\n")
        graph = {self.root / f"{name}.lean": set()
                 for name in BOUNDARIES.LIBRARIES}
        for forbidden in ("ExampleProofs.lean", "NanoP4Spec.lean"):
            with self.subTest(forbidden=forbidden):
                graph[source] = {self.root / forbidden}
                with patch.object(BOUNDARIES, "run", return_value=""):
                    with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Unused.lean"):
                        BOUNDARIES.check(self.root, parser=lambda sources, root:
                                         {source: graph[source] for source in sources})

    def test_direct_and_transitive_core_model_imports_rejected(self):
        for edges in ({"P4SpecTec.lean": ["NanoP4Spec.lean"]},
                      {"P4SpecTec.lean": ["Bridge.lean"],
                       "Bridge.lean": ["NanoP4Spec/Model.lean"]}):
            with self.subTest(edges=edges):
                with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "imports a generated model"):
                    BOUNDARIES.check_graph(self.graph(edges),
                                           {self.root / "P4SpecTec.lean"}, self.root)

    def test_generated_library_may_depend_on_core(self):
        graph = self.graph({"NanoP4Spec.lean": ["P4SpecTec.lean"], "P4SpecTec.lean": []})
        BOUNDARIES.check_graph(graph, {self.root / "NanoP4Spec.lean"}, self.root)

    def test_ignored_generated_library_boundaries(self):
        graph = self.graph({"P4Spec.lean": ["P4Spec/Model.lean"],
                            "P4Spec/Model.lean": ["P4SpecTec.lean"], "P4SpecTec.lean": []})
        BOUNDARIES.check_graph(graph, {self.root / "P4Spec.lean"}, self.root)
        for start, edges, message in (
                ("P4SpecTec.lean", {"P4SpecTec.lean": ["P4Spec.lean"], "P4Spec.lean": []},
                 "imports a generated model"),
                ("NanoP4Target.lean", {"NanoP4Target.lean": ["P4Spec/Model.lean"],
                                       "P4Spec/Model.lean": []},
                 "imports ignored generated sources"),
                ("P4Spec.lean", {"P4Spec.lean": ["NanoP4Spec.lean"], "NanoP4Spec.lean": []},
                 "imports beyond the core"),
                ("P4Spec.lean", {"P4Spec.lean": ["P4SpecTecTest.lean"], "P4SpecTecTest.lean": []},
                 "imports a consumer")):
            with self.subTest(start=start, message=message):
                with self.assertRaisesRegex(BOUNDARIES.BoundaryError, message):
                    BOUNDARIES.check_graph(self.graph(edges), {self.root / start}, self.root)

    def test_consumer_root_cannot_reach_ignored_generated_sources(self):
        graph = self.graph({"P4SpecTecTest.lean": ["P4SpecTecTest/Unit.lean"],
                            "P4SpecTecTest/Unit.lean": ["P4Spec.lean"], "P4Spec.lean": [],
                            "ExampleProofs.lean": []})
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "reaches ignored generated"):
            BOUNDARIES.check_consumer_roots(graph, self.root)
        # A registered executable under the test namespace may; the library root may not.
        graph[self.root / "P4SpecTecTest/Unit.lean"] = set()
        graph[self.root / "P4SpecTecTest/Tool.lean"] = {self.root / "P4Spec.lean"}
        BOUNDARIES.check_consumer_roots(graph, self.root)

    def test_missing_generated_sources_named(self):
        (self.root / "P4Spec.lean").unlink()
        with patch.object(BOUNDARIES, "run", return_value=""):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "regenerate the library first"):
                BOUNDARIES.source_inventory(self.root)

    def test_transitive_root_reachability(self):
        sources = {self.root / f"{name}.lean"
                   for name in BOUNDARIES.LIBRARIES}
        graph = {source: set() for source in sources}
        helper = self.root / "P4SpecTec/Helper.lean"
        leaf = self.root / "P4SpecTec/Leaf.lean"
        graph[self.root / "P4SpecTec.lean"] = {helper}
        graph[helper] = {leaf}
        graph[leaf] = set()
        BOUNDARIES.check_reachability(graph, sources | {helper, leaf}, set(), self.root)

    def test_unregistered_main_is_not_exempt(self):
        sources = {self.root / f"{name}.lean"
                   for name in BOUNDARIES.LIBRARIES}
        graph = {source: set() for source in sources}
        main = self.root / "P4SpecTec/Unused/Main.lean"
        graph[main] = set()
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "unreachable.*Unused/Main.lean"):
            BOUNDARIES.check_reachability(graph, sources | {main}, set(), self.root)

    def test_registered_executable_and_helpers_are_reachable(self):
        sources = {self.root / f"{name}.lean"
                   for name in BOUNDARIES.LIBRARIES}
        graph = {source: set() for source in sources}
        executable = self.root / "P4SpecTec/Driver.lean"
        helper = self.root / "P4SpecTec/Driver/Helper.lean"
        graph[executable] = {helper}
        graph[helper] = set()
        BOUNDARIES.check_reachability(graph, sources | {executable, helper},
                                      {executable}, self.root)
        graph[executable] = set()
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Driver/Helper.lean"):
            BOUNDARIES.check_reachability(graph, sources | {executable, helper},
                                          {executable}, self.root)

    def test_executable_configuration(self):
        self.write("lakefile.toml", config_text() +
                   '[[lean_exe]]\nname = "driver"\nroot = "P4SpecTec.Driver"\n')
        self.assertEqual(BOUNDARIES.check_config(self.root),
                         {self.root / "P4SpecTec/Driver.lean"})

    def test_invalid_executable_configuration_rejected(self):
        for extra in ('[[lean_exe]]\nname = "driver"\nroot = "../Other"\n',
                      '[[lean_exe]]\nname = "driver"\nroot = "P4SpecTec.Driver"\n'
                      'srcDir = "other"\n',
                      '[[lean_exe]]\nname = "driver"\nroot = "P4SpecTec.Driver"\n'
                      '[[lean_exe]]\nname = "driver"\nroot = "P4SpecTec.Other"\n'):
            with self.subTest(extra=extra):
                self.write("lakefile.toml", config_text() + extra)
                with self.assertRaises(BOUNDARIES.BoundaryError):
                    BOUNDARIES.check_config(self.root)

    def test_missing_executable_source_rejected(self):
        self.write("lakefile.toml", config_text() +
                   '[[lean_exe]]\nname = "driver"\nroot = "P4SpecTec.Driver"\n')
        with patch.object(BOUNDARIES, "run", return_value=""):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Driver.lean"):
                BOUNDARIES.check(self.root)



@unittest.skipUnless(WITH_LEAN, "pass --lean under lake env for pinned-parser integration")
class LeanParserTests(Fixture):
    def parse(self, content):
        source = self.write("Header.lean", content)
        return BOUNDARIES.parse_dependencies({source}, self.root)[source]

    def test_header_syntax(self):
        quoted = self.write("ExampleProofs/with.dot.lean", "prelude\n")
        dependencies = self.parse(
            "module\n/- outer /- nested -/ import P4SpecTecTest -/\n"
            "public import\n ExampleProofs.«with.dot»\npublic import P4SpecTec\n"
            "meta import ExampleProofs\nimport NanoP4Spec\n"
            '-- import P4SpecTecTest\ndef text := "import P4SpecTecTest"\n'
        )
        self.assertIn(quoted, dependencies)
        self.assertIn(self.root / "ExampleProofs.lean", dependencies)
        self.assertIn(self.root / "P4SpecTec.lean", dependencies)
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
        self.write("P4SpecTec.lean", "import Bridge\n")
        self.write("Bridge.lean", "import\n ExampleProofs\n")
        with patch.object(BOUNDARIES, "source_inventory", return_value={self.root / "P4SpecTec.lean"}):
            with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "Bridge.lean -> ExampleProofs"):
                BOUNDARIES.check(self.root)

    def check_fixture(self):
        sources = {path for path in self.root.rglob("*.lean")
                   if BOUNDARIES.namespace(path, self.root)
                   in BOUNDARIES.LIBRARIES | BOUNDARIES.TOOLS}
        with patch.object(BOUNDARIES, "source_inventory", return_value=sources):
            BOUNDARIES.check(self.root)

    def test_parser_closure_rejects_core_model_bridge(self):
        self.write("P4SpecTec.lean", "module\npublic import Bridge\n")
        self.write("Bridge.lean", "import\n NanoP4Spec\n")
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError,
                                    "Bridge.lean -> NanoP4Spec.lean"):
            self.check_fixture()

    def test_parser_transitive_reachability_and_unreachable_source(self):
        self.write("P4SpecTec.lean", "module\npublic import P4SpecTec.Helper\n")
        self.write("P4SpecTec/Helper.lean", "import\n P4SpecTec.Leaf\n")
        self.write("P4SpecTec/Leaf.lean", "prelude\n")
        self.check_fixture()
        self.write("P4SpecTec/Unreachable.lean", "prelude\n")
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "unreachable.*Unreachable.lean"):
            self.check_fixture()

    def test_parser_standalone_tool_reachability(self):
        self.write("lakefile.toml", config_text() +
                   '[[lean_exe]]\nname = "driver"\nroot = "Tools.Driver"\n')
        self.write("Tools/Driver.lean", "import Tools.Helper\n")
        self.write("Tools/Helper.lean", "prelude\n")
        self.check_fixture()
        self.write("Tools/Unused.lean", "prelude\n")
        with self.assertRaisesRegex(BOUNDARIES.BoundaryError, "unreachable.*Tools/Unused.lean"):
            self.check_fixture()

    def test_parser_registered_executable_reaches_helpers(self):
        self.write("lakefile.toml", config_text() +
                   '[[lean_exe]]\nname = "driver"\nroot = "P4SpecTec.Driver"\n')
        self.write("P4SpecTec/Driver.lean", "import P4SpecTec.Driver.Helper\n")
        self.write("P4SpecTec/Driver/Helper.lean", "prelude\n")
        self.check_fixture()


if __name__ == "__main__":
    unittest.main()
