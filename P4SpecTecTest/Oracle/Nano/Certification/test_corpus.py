"""Mutations exercise inventory boundaries, not merely JSON readability."""

import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import corpus


class CorpusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.manifest = corpus.load()
        cls.expected = corpus.generate()

    def assert_inventory_rejected(self, mutate):
        manifest = copy.deepcopy(self.manifest)
        mutate(manifest)
        # The regeneration boundary is exercised separately against real pins.
        # These mutations test comparison against that independently derived value.
        with patch.object(corpus, "generate", return_value=self.expected):
            with self.assertRaisesRegex(corpus.CorpusError, "case inventory or evidence differs"):
                corpus.check_manifest(manifest)

    def test_current_inventory(self):
        self.assertEqual(self.manifest, self.expected)
        self.assertEqual(len(corpus.check_manifest(self.manifest)), 117)
        typing = [c for c in self.manifest["cases"] if c["kind"] == "typing"]
        packet = [c for c in self.manifest["cases"] if c["kind"] == "packet"]
        self.assertEqual(len(typing), 78)
        self.assertEqual(len(packet), 39)
        self.assertEqual(sum(c["upstreamVerdict"] == "fail" for c in typing), 30)
        self.assertEqual(sum(bool(c["observations"]) for c in packet), 3)
        self.assertEqual(len(set(corpus.obligation_ids(self.manifest))), 117)

    def test_removed_case(self):
        self.assert_inventory_rejected(lambda m: m["cases"].pop())

    def test_removed_rejection(self):
        def mutate(manifest):
            manifest["cases"] = [c for c in manifest["cases"]
                                 if c["id"] != "corpus:typing:negative/wrong-width"]
        self.assert_inventory_rejected(mutate)

    def test_forged_proof_flag(self):
        self.assert_inventory_rejected(lambda m: m["cases"][0].update(certified=True))

    def test_forged_evidence_flag(self):
        self.assert_inventory_rejected(lambda m: m["cases"][0].update(replayChecked=True))

    def test_stale_source_digest(self):
        self.assert_inventory_rejected(
            lambda m: m["cases"][0]["source"].update(sha256="0" * 64))

    def test_stale_observation_digest(self):
        self.assert_inventory_rejected(
            lambda m: m["cases"][0]["observations"][0].update(sha256="0" * 64))

    def test_forged_exclusion(self):
        self.assert_inventory_rejected(
            lambda m: m["cases"][0].update(outOfProfile="unsupported adapter"))

    def test_missing_source_rejected_before_manifest_comparison(self):
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(corpus, "git", return_value=b"pinned source\n"):
                with self.assertRaisesRegex(corpus.CorpusError, "missing corpus input:"):
                    corpus.pinned_file(Path(directory), "pin", "hidden-case.p4")

    def test_modified_source_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "changed-case.p4"
            path.write_bytes(b"modified source\n")
            with patch.object(corpus, "git", return_value=b"pinned source\n"):
                with self.assertRaisesRegex(corpus.CorpusError, "modified pinned source:"):
                    corpus.pinned_file(Path(directory), "pin", path.name)

    def test_stale_pin(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["pins"][corpus.UPSTREAM] = "0" * 40
        with patch.object(corpus, "generate", return_value=self.expected):
            with self.assertRaisesRegex(corpus.CorpusError, "manifest pins differ"):
                corpus.check_manifest(manifest)

    def test_indexed_pin_uses_staged_revision_instead_of_head(self):
        staged = "a" * 40
        committed = "b" * 40

        def read_git(root, *args):
            if args == ("ls-files", "--stage", "-z", "--", corpus.UPSTREAM):
                return f"160000 {staged} 0\t{corpus.UPSTREAM}\0".encode()
            if args == ("rev-parse", f"HEAD:{corpus.UPSTREAM}"):
                return committed.encode() + b"\n"
            self.fail(f"unexpected Git call: {args}")

        with patch.object(corpus, "git", side_effect=read_git) as read:
            self.assertEqual(corpus.indexed_pin(corpus.ROOT, corpus.UPSTREAM), staged)
            read.assert_called_once_with(corpus.ROOT, "ls-files", "--stage", "-z",
                                         "--", corpus.UPSTREAM)

    def test_indexed_pin_rejects_missing_gitlink(self):
        with patch.object(corpus, "git", return_value=b""):
            with self.assertRaisesRegex(corpus.CorpusError, "missing or unmerged indexed gitlink"):
                corpus.indexed_pin(corpus.ROOT, corpus.UPSTREAM)

    def test_indexed_pin_rejects_regular_file(self):
        entry = f"100644 {'a' * 40} 0\t{corpus.UPSTREAM}\0".encode()
        with patch.object(corpus, "git", return_value=entry):
            with self.assertRaisesRegex(corpus.CorpusError, "invalid or unmerged indexed gitlink"):
                corpus.indexed_pin(corpus.ROOT, corpus.UPSTREAM)

    def test_indexed_pin_rejects_conflict(self):
        entries = b"".join(f"160000 {'a' * 40} {stage}\t{corpus.UPSTREAM}\0".encode()
                           for stage in (1, 2, 3))
        with patch.object(corpus, "git", return_value=entries):
            with self.assertRaisesRegex(corpus.CorpusError, "missing or unmerged indexed gitlink"):
                corpus.indexed_pin(corpus.ROOT, corpus.UPSTREAM)

    def test_generate_rejects_checkout_at_other_revision(self):
        with patch.object(corpus, "indexed_pin", return_value="a" * 40):
            with patch.object(corpus, "git", return_value=("b" * 40 + "\n").encode()):
                with self.assertRaisesRegex(corpus.CorpusError, "checkout differs from recorded pin"):
                    corpus.generate()

    def test_wrong_profile_scalar_type(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["profile"]["dynamicGuards"] = 0
        with patch.object(corpus, "generate", return_value=self.expected):
            with self.assertRaisesRegex(corpus.CorpusError, "source context or profile differs"):
                corpus.check_manifest(manifest)

    def test_wrong_schema_scalar_type(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["schemaVersion"] = True
        with patch.object(corpus, "generate", return_value=self.expected):
            with self.assertRaisesRegex(corpus.CorpusError, "source context or profile differs"):
                corpus.check_manifest(manifest)

    def test_duplicate_key_rejected(self):
        with self.assertRaisesRegex(corpus.CorpusError, "duplicate manifest key"):
            json.loads('{"certified":false,"certified":true}',
                       object_pairs_hook=corpus.strict_object)


if __name__ == "__main__":
    unittest.main()
