#!/usr/bin/env python3
"""Unit tests for scripts/mathlib_cache.py.

Run with: python3 scripts/test_mathlib_cache.py

`gh` is a fake that answers the three API calls the predicate makes. The case that matters most is a
release tag ON master: mathlib's release_cache.yml skips it yet concludes `success`, so that run must
not count as a published cache.
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import mathlib_cache as mc  # noqa: E402

PUSH = {"event": "push", "head_branch": "master"}


class Fake:
    """build_runs / release_runs are what gh's jq filter leaves: the successful completed runs."""

    def __init__(self, build_runs=(), release_runs=(), compare="diverged"):
        self.build_runs, self.release_runs, self.compare = list(build_runs), list(release_runs), compare
        self.calls = []

    def __call__(self, path, jq=None):
        import json
        self.calls.append(path)
        if "workflows/build.yml/runs" in path:
            assert "event=push" in path, path
            return json.dumps(self.build_runs)
        if "workflows/release_cache.yml/runs" in path:
            return json.dumps(self.release_runs)
        if "/compare/" in path:
            return self.compare + "\n"
        raise AssertionError(path)


class CachePublished(unittest.TestCase):
    def test_a_successful_master_push_build_publishes(self):
        self.assertTrue(mc.cache_published(Fake(build_runs=[PUSH]), "m/m", "sha"))

    def test_a_build_on_another_branch_does_not(self):
        runs = [{"event": "push", "head_branch": "bump_to_v4.34.1"}]
        self.assertFalse(mc.cache_published(Fake(build_runs=runs), "m/m", "sha"))

    def test_nothing_published_and_no_tag(self):
        self.assertFalse(mc.cache_published(Fake(), "m/m", "sha"))

    def test_an_off_master_tag_is_published_by_its_release_cache_run(self):
        fake = Fake(release_runs=[{"event": "push", "head_branch": "v4.34.1"}], compare="diverged")
        self.assertTrue(mc.cache_published(fake, "m/m", "sha", "v4.34.1"))

    def test_a_release_cache_run_on_another_tag_does_not(self):
        fake = Fake(release_runs=[{"event": "push", "head_branch": "v4.34.0"}], compare="diverged")
        self.assertFalse(mc.cache_published(fake, "m/m", "sha", "v4.34.1"))

    def test_an_on_master_tag_is_not_published_by_a_skipped_release_cache_run(self):
        # the gate job skips the build for a tag on master, and the run still concludes success
        for status in ("ahead", "identical"):
            fake = Fake(release_runs=[{"event": "push", "head_branch": "v4.35.0"}], compare=status)
            self.assertFalse(mc.cache_published(fake, "m/m", "sha", "v4.35.0"), status)
            self.assertFalse(any("release_cache.yml" in call for call in fake.calls), status)

    def test_an_on_master_tag_is_published_once_its_master_build_is(self):
        fake = Fake(build_runs=[PUSH], release_runs=[{"event": "push", "head_branch": "v4.35.0"}], compare="ahead")
        self.assertTrue(mc.cache_published(fake, "m/m", "sha", "v4.35.0"))

    def test_a_caller_holding_the_compare_answer_spares_the_api_call(self):
        fake = Fake(release_runs=[{"event": "push", "head_branch": "v4.34.1"}])
        self.assertTrue(mc.cache_published(fake, "m/m", "sha", "v4.34.1", known_on_master=lambda: False))
        self.assertFalse(any("/compare/" in call for call in fake.calls))
        self.assertFalse(mc.cache_published(fake, "m/m", "sha", "v4.34.1", known_on_master=lambda: True))

    def test_cache_source_names_what_published_it(self):
        self.assertEqual(mc.cache_source(Fake(build_runs=[PUSH]), "m/m", "sha"), "master")
        off_master = Fake(release_runs=[{"event": "push", "head_branch": "v4.34.1"}], compare="diverged")
        self.assertEqual(mc.cache_source(off_master, "m/m", "sha", "v4.34.1"), "release")
        self.assertIsNone(mc.cache_source(Fake(), "m/m", "sha", "v4.34.1"))

    def test_the_master_build_is_named_first_when_both_published(self):
        both = Fake(build_runs=[PUSH], release_runs=[{"event": "push", "head_branch": "v4.34.1"}], compare="diverged")
        self.assertEqual(mc.cache_source(both, "m/m", "sha", "v4.34.1"), "master")

    def test_a_failed_lookup_is_an_error_not_an_answer(self):
        def failing(path, jq=None):
            raise RuntimeError("gh api failed")
        with self.assertRaises(RuntimeError):
            mc.cache_published(failing, "m/m", "sha")


class Listing(unittest.TestCase):
    def gh_answering(self, out):
        self.paths = []

        def gh(path, jq=None):
            self.paths.append(path)
            return out
        return gh

    def test_newest_master_build_names_the_commit(self):
        self.assertEqual(mc.newest_master_build(self.gh_answering("abc123\n"), "m/m"), "abc123")
        self.assertIn("build.yml/runs?branch=master&event=push&status=success", self.paths[0])

    def test_none_before_there_is_a_build(self):
        self.assertIsNone(mc.newest_master_build(self.gh_answering("\n"), "m/m"))

    def test_a_missing_workflow_is_an_error_not_no_build(self):
        def missing(path, jq=None):
            raise RuntimeError("gh api failed: HTTP 404")
        with self.assertRaises(RuntimeError):
            mc.newest_master_build(missing, "m/m")

    def test_master_membership_asks_the_compare_against_master(self):
        for status, expected in (("ahead", True), ("identical", True), ("behind", False), ("diverged", False)):
            self.assertEqual(mc.on_master(self.gh_answering(status + "\n"), "m/m", "abc"), expected, status)
            self.assertEqual(self.paths, ["repos/m/m/compare/abc...master"])


if __name__ == "__main__":
    unittest.main()
