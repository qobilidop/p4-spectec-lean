#!/usr/bin/env python3
"""Offline sensitivities for the bounded type oracle's source provenance."""

import importlib.util
import pathlib
import unittest
from unittest import mock


SPEC = importlib.util.spec_from_file_location("type_runtime_oracle",
                                            pathlib.Path(__file__).with_name("capture.py"))
ORACLE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ORACLE)


class Provenance(unittest.TestCase):
    def test_no_build_after_bad_provenance(self):
        with mock.patch.object(ORACLE, "revision_guard", side_effect=SystemExit("bad pin")), \
                mock.patch.object(ORACLE.subprocess, "run") as run:
            with self.assertRaises(SystemExit):
                ORACLE.observations(pathlib.Path("/fake/upstream"))
            run.assert_not_called()

    def test_rebuild_before_link(self):
        upstream = pathlib.Path("/fake/upstream")
        with mock.patch.object(ORACLE, "revision_guard", return_value="pin"), \
                mock.patch.object(ORACLE.subprocess, "run") as run, \
                mock.patch.object(ORACLE.subprocess, "check_output", return_value=b"[]"), \
                mock.patch.object(ORACLE.shutil, "copyfile"):
            run.return_value.returncode = 0
            self.assertEqual(ORACLE.observations(upstream), {"upstreamRevision": "pin", "cases": []})
            self.assertEqual(run.call_args_list[0].args[0],
                             ["dune", "build", "p4spec/bin/main.exe"])
            self.assertEqual(run.call_args_list[1].args[0][0], "ocamlfind")


if __name__ == "__main__":
    unittest.main()
