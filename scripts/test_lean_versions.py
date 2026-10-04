#!/usr/bin/env python3
"""Unit tests for scripts/lean_versions.py.

Run with: python3 scripts/test_lean_versions.py

The parse/order rule that check-bump.sh, toolchain_tags.py and resolve_deps.py share is pinned here,
once, so a drift in it fails here rather than as a resolver proposal the guard refuses.
"""

import os
import subprocess
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


class TrustedReleaseTags(unittest.TestCase):
    def test_only_the_v4_series_is_trusted(self):
        for name in ("v4.34.0", "v4.34.1", "v4.35.0-rc1"):
            self.assertTrue(lv.is_trusted_release_tag(name), name)
        for name in ("v5.0.0", "v3.9.0", "v4.34.1-patch1", "nightly-2026-01-01", "", None):
            self.assertFalse(lv.is_trusted_release_tag(name), name)

    def refs(self, *named):
        lines = [f"refs/tags/{n}\t{sha}\tcommit" for n, sha in named]
        return lambda path, jq=None: "\n".join(lines)

    def test_release_tag_of_names_the_trusted_tag_on_a_commit(self):
        gh = self.refs(("v4.34.0", "a"), ("v4.34.1", "b"), ("v5.0.0", "c"))
        self.assertEqual(lv.release_tag_of(gh, "o/r", "b"), "v4.34.1")
        self.assertIsNone(lv.release_tag_of(gh, "o/r", "c"))  # a v5 tag is not trusted
        self.assertIsNone(lv.release_tag_of(gh, "o/r", "zzz"))

    def test_release_tag_of_prefers_the_final_release_over_its_rc(self):
        gh = self.refs(("v4.35.0-rc1", "a"), ("v4.35.0", "a"))
        self.assertEqual(lv.release_tag_of(gh, "o/r", "a"), "v4.35.0")


class ToolchainOrder(unittest.TestCase):
    def test_older_same_newer(self):
        t = lambda v: lv.TOOLCHAIN_PREFIX + v  # noqa: E731
        self.assertEqual(lv.toolchain_order(t("v4.34.1"), t("v4.34.0")), "older")
        self.assertEqual(lv.toolchain_order(t("v4.34.1"), t("v4.34.1")), "same")
        self.assertEqual(lv.toolchain_order(t("v4.35.0-rc3"), t("v4.35.0")), "newer")

    def test_anything_but_a_release_has_no_order(self):
        t = lambda v: lv.TOOLCHAIN_PREFIX + v  # noqa: E731
        self.assertIsNone(lv.toolchain_order(t("v4.34.0"), t("nightly-2026-01-01")))
        self.assertIsNone(lv.toolchain_order(None, t("v4.34.0")))


class WhyNotNewer(unittest.TestCase):
    def test_a_newer_release_is_newer(self):
        for old, new in (("v4.34.0", "v4.34.1"), ("v4.35.0-rc3", "v4.35.0"), ("v4.34.1", "v4.35.0-rc1")):
            self.assertIsNone(lv.why_not_newer(lv.TOOLCHAIN_PREFIX + old, lv.TOOLCHAIN_PREFIX + new), (old, new))

    def test_older_and_equal_say_why(self):
        old, new = lv.TOOLCHAIN_PREFIX + "v4.35.0", lv.TOOLCHAIN_PREFIX + "v4.35.0-rc3"
        self.assertIn("moved backward", lv.why_not_newer(old, new))
        self.assertIn("is not newer", lv.why_not_newer(old, old))

    def test_anything_but_a_release_is_refused_whichever_side_it_is_on(self):
        release, nightly = lv.TOOLCHAIN_PREFIX + "v4.34.0", lv.TOOLCHAIN_PREFIX + "nightly-2026-01-01"
        for old, new in ((release, nightly), (nightly, release)):
            self.assertIn("is not a leanprover/lean4 vX.Y.Z[-rcN] release", lv.why_not_newer(old, new))

    def test_the_command_line_is_the_same_answer(self):
        run = lambda *a: subprocess.run([sys.executable, lv.__file__, "newer", *a], capture_output=True, text=True)  # noqa: E731
        ok = run(lv.TOOLCHAIN_PREFIX + "v4.34.0", lv.TOOLCHAIN_PREFIX + "v4.34.1")
        self.assertEqual((ok.returncode, ok.stdout), (0, ""))
        bad = run(lv.TOOLCHAIN_PREFIX + "v4.34.1", lv.TOOLCHAIN_PREFIX + "v4.34.0")
        self.assertEqual(bad.returncode, 1)
        self.assertIn("moved backward", bad.stdout)


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
