#!/usr/bin/env python3
"""Unit tests for scripts/bump_moves.py. Run with: python3 scripts/test_bump_moves.py

The rule is tested here once; test_resolve_deps.py (ForwardMoves) and test_check_bump.py exercise it
through the resolver and through the guard, so the two cannot drift apart.
"""

import base64
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import bump_moves as bm  # noqa: E402

TC = "leanprover/lean4:"


def move(status, on_branch, order, tag):
    return bm.mathlib_move(status, on_branch, lambda: order, lambda: tag)


class MathlibMove(unittest.TestCase):
    def test_a_descendant_on_the_branch_is_a_descendant_whatever_the_toolchain(self):
        for order in ("older", "same", "newer", None):
            self.assertEqual(move("ahead", True, order, False), ("descendant", None), order)

    def test_off_the_branch_needs_a_newer_toolchain(self):
        for status in ("ahead", "diverged"):
            for order in ("older", "same", None):
                self.assertEqual(move(status, False, order, True), (None, "toolchain-not-newer"), (status, order))

    def test_a_release_tag_on_a_newer_toolchain_is_a_release_ahead_or_diverged(self):
        for status in ("ahead", "diverged"):
            self.assertEqual(move(status, False, "newer", True), ("release", None), status)

    def test_a_diverged_rev_on_the_branch_is_the_way_back(self):
        self.assertEqual(move("diverged", True, "newer", False), ("toolchain", None))

    def test_otherwise_it_is_neither_a_release_nor_on_the_branch(self):
        self.assertEqual(move("ahead", False, "newer", False), (None, "neither-release-nor-branch"))
        self.assertEqual(move("diverged", False, "newer", False), (None, "neither-release-nor-branch"))

    def test_behind_and_identical_are_never_forward(self):
        for status in ("behind", "identical", "", None):
            self.assertEqual(move(status, True, "newer", True), (None, "not-forward"), status)

    def test_the_facts_are_fetched_only_when_the_rule_reaches_them(self):
        calls = []
        order = lambda: calls.append("toolchain") or "newer"  # noqa: E731
        tag = lambda: calls.append("tag") or True  # noqa: E731
        bm.mathlib_move("ahead", True, order, tag)
        bm.mathlib_move("behind", False, order, tag)
        self.assertEqual(calls, [])  # a plain bump along the branch asks nothing
        bm.mathlib_move("diverged", False, lambda: calls.append("toolchain") or "same", tag)
        self.assertEqual(calls, ["toolchain"])  # no toolchain gain: the tag is never looked up
        bm.mathlib_move("ahead", False, order, tag)
        self.assertEqual(calls, ["toolchain", "toolchain", "tag"])


class DependencyMove(unittest.TestCase):
    def test_only_a_descendant_on_the_branch(self):
        self.assertEqual(bm.dependency_move("ahead", True), ("descendant", None))
        self.assertEqual(bm.dependency_move("ahead", False), (None, "off-branch"))
        for status in ("diverged", "behind", "identical"):
            self.assertEqual(bm.dependency_move(status, True), (None, "not-forward"), status)


def content(text):
    return base64.b64encode(text.encode()).decode()


class Decide(unittest.TestCase):
    """The guard's verdicts and what it fetched to reach them, over a fake `gh`."""

    def gh(self, toolchain="v4.35.0", tags=()):
        self.paths = []
        refs = "\n".join(f"refs/tags/{n}\t{sha}\tcommit" for n, sha in tags)

        def fake(path, jq=None):
            self.paths.append(path)
            if "contents/lean-toolchain" in path:
                return content(TC + toolchain + "\n")
            if "matching-refs" in path:
                return refs
            raise RuntimeError(f"gh api {path} failed")
        return fake

    def decide(self, name, status, st_branch, tc="v4.34.0", **gh):
        return bm.decide(name, status, st_branch, "master", TC + tc, "old", "new", "o/r", self.gh(**gh))

    def test_a_plain_bump_along_the_branch_fetches_nothing(self):
        ok, message, details = self.decide("mathlib", "ahead", "ahead")
        self.assertEqual((ok, message, details), (True, "mathlib old -> new is a forward move on 'master'.", ("", "", True)))
        self.assertEqual(self.paths, [])

    def test_a_release_names_its_toolchain_and_tag(self):
        ok, message, details = self.decide("mathlib", "diverged", "diverged", tags=[("v4.35.0", "new")])
        self.assertTrue(ok)
        self.assertEqual(message, "mathlib old -> new is release v4.35.0, on newer toolchain leanprover/lean4:v4.35.0.")
        self.assertEqual(details, (TC + "v4.35.0", "v4.35.0", False))

    def test_the_way_back_to_the_branch(self):
        ok, message, _ = self.decide("mathlib", "diverged", "identical")
        self.assertTrue(ok)
        self.assertIn("is on 'master', on newer toolchain", message)

    def test_each_refusal_says_why(self):
        cases = [
            (("TauCeti", "ahead", "diverged"), {}, "TauCeti new rev new is not on branch 'master'"),
            (("TauCeti", "behind", "ahead"), {}, "TauCeti rev is not a forward move from base (compare status: behind)"),
            (("mathlib", "behind", "ahead"), {}, "mathlib rev is not a forward move from base"),
            (("mathlib", "diverged", "diverged"), {"toolchain": "v4.34.0"}, "toolchain is not newer than base's"),
            (("mathlib", "ahead", "diverged"), {}, "is ahead of old and is neither a release tag nor on branch 'master'"),
        ]
        for args, gh, fragment in cases:
            ok, message, _ = self.decide(*args, **gh)
            self.assertFalse(ok, args)
            self.assertIn(fragment, message, args)

    def test_the_toolchain_is_decoded_and_stripped_one_way(self):
        gh = self.gh(toolchain="v4.35.0")
        self.assertEqual(bm.fetch_toolchain(gh, "o/r", "abc"), TC + "v4.35.0")
        self.assertEqual(self.paths, ["repos/o/r/contents/lean-toolchain?ref=abc"])
        padded = lambda path, jq=None: base64.b64encode(f"  {TC}v4.35.0 \n\n".encode()).decode()  # noqa: E731
        self.assertEqual(bm.fetch_toolchain(padded, "o/r", "abc"), TC + "v4.35.0")

    def test_a_failed_fetch_is_an_error_naming_what_failed(self):
        with self.assertRaisesRegex(RuntimeError, "cannot fetch mathlib lean-toolchain at new"):
            bm.decide("mathlib", "diverged", "diverged", "master", TC + "v4.34.0", "old", "new", "o/r",
                      lambda path, jq=None: (_ for _ in ()).throw(RuntimeError("boom")))


if __name__ == "__main__":
    unittest.main()
