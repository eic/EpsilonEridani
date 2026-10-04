#!/usr/bin/env python3
"""Unit tests for scripts/lean_versions.py.

Run with: python3 scripts/test_lean_versions.py

The parse/order rule that check-bump.sh, toolchain_tags.py and resolve_deps.py share is pinned here,
once, so a drift in it fails here rather than as a resolver proposal the guard refuses.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import lean_versions as lv  # noqa: E402


class VersionNames(unittest.TestCase):
    def test_releases_and_rcs_parse(self):
        self.assertEqual(lv.parse_release("v4.33.0")[:3], (4, 33, 0))
        self.assertEqual(lv.parse_release("v4.33.0-rc2")[3], 2)

    def test_non_releases_do_not(self):
        for name in ("v2024", "v4.32.0-rc1-patch1", "nightly-2026-01-01", "", None):
            self.assertIsNone(lv.parse_release(name), name)

    def test_a_final_release_sorts_after_its_own_rcs(self):
        order = ["v4.32.1", "v4.33.0-rc1", "v4.33.0-rc2", "v4.33.0", "v4.34.0-rc1"]
        self.assertEqual(sorted(order, key=lv.release_key), order)

    def test_a_name_that_is_not_a_release_sorts_after_every_release(self):
        order = ["v4.33.0", "nightly-2026-01-01"]
        self.assertEqual(sorted(reversed(order), key=lv.release_key), order)

    def test_only_release_toolchains_name_a_release(self):
        self.assertEqual(lv.release_of_toolchain("leanprover/lean4:v4.33.0"), "v4.33.0")
        self.assertIsNone(lv.release_of_toolchain("leanprover/lean4:nightly-2026-01-01"))
        self.assertIsNone(lv.release_of_toolchain("leanprover/lean4-pr-releases:pr-1"))
        self.assertIsNone(lv.release_of_toolchain(""))


class Toolchains(unittest.TestCase):
    def test_release_sorts_above_its_rcs(self):
        self.assertGreater(lv.parse_toolchain("leanprover/lean4:v4.35.0"),
                           lv.parse_toolchain("leanprover/lean4:v4.35.0-rc3"))
        self.assertGreater(lv.parse_toolchain("leanprover/lean4:v4.35.0-rc1"),
                           lv.parse_toolchain("leanprover/lean4:v4.34.1"))

    def test_unrecognised(self):
        self.assertIsNone(lv.parse_toolchain("leanprover/lean4:nightly-2026-09-01"))
        self.assertIsNone(lv.parse_toolchain(None))

    def test_show_drops_the_prefix_and_marks_a_missing_pin(self):
        self.assertEqual(lv.show_toolchain(" leanprover/lean4:v4.34.0\n"), "v4.34.0")
        self.assertEqual(lv.show_toolchain(None), "?")


class ReleaseTags(unittest.TestCase):
    REFS = "\n".join(["refs/tags/v4.33.0\tc1\tcommit",
                      "refs/tags/v4.34.0\ttagobj\ttag",
                      "refs/tags/not-a-release\tc3\tcommit"])

    def gh(self, path, jq=None):
        if "matching-refs" in path:
            return self.REFS
        assert path.endswith("git/tags/tagobj"), path
        return "c2"

    def test_lists_releases_and_dereferences_annotated_tags(self):
        self.assertEqual(lv.release_tags(self.gh, "o/r"), {"v4.33.0": "c1", "v4.34.0": "c2"})

    def test_a_lenient_listing_may_answer_none_while_tags_still_resolve(self):
        lenient = lambda path, jq=None: None if "matching-refs" in path else self.gh(path, jq)  # noqa: E731
        self.assertEqual(lv.release_tags(lenient, "o/r", resolve=self.gh), {})

    def test_the_resolver_dereferences_what_the_listing_found(self):
        listing = lambda path, jq=None: self.REFS  # noqa: E731
        self.assertEqual(lv.release_tags(listing, "o/r", resolve=self.gh), {"v4.33.0": "c1", "v4.34.0": "c2"})


if __name__ == "__main__":
    unittest.main()
