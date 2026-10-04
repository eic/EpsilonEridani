#!/usr/bin/env python3
"""Unit tests for scripts/resolve_deps.py.

Run with: python3 scripts/test_resolve_deps.py

No network: synthetic commit graphs answer the same questions `gh api` would, and one real
recording (resolve_deps_fixtures/2026-10-03.json, made with `--record`) replays the upstream
state on the day the resolver was written: Physlib on mathlib's v4.34.1 tag, TauCeti already
on Lean v4.35.0-rc3, and main on v4.34.0.
"""

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import resolve_deps as rd  # noqa: E402

FIXTURES = Path(__file__).resolve().parent / "resolve_deps_fixtures"
ML, PL, TC = "leanprover-community/mathlib4", "example/Physlib", "example/TauCeti"
REQUIRES = [("Physlib", PL, "master"), ("TauCeti", TC, "main"), ("mathlib", ML, "master")]


def lean(v):
    return f"leanprover/lean4:{v}"


class Graph:
    """A tiny stand-in for GitHub: per repository, commits with one parent, a date and files."""

    def __init__(self):
        self.repos = {}
        self.tags = {}
        self.cached = None
        self.uncached = set()  # mathlib commits whose cache is not published
        self.clock = 0

    def commit(self, repo, sha, parent=None, branch=None, **files):
        r = self.repos.setdefault(repo, {"commits": {}, "branches": {}})
        inherited = dict(r["commits"][parent]["files"]) if parent else {}
        names = {"manifest": "lake-manifest.json", "lake_manifest": "lake-manifest.json",
                 "lean_toolchain": "lean-toolchain"}
        inherited.update({names[k]: v for k, v in files.items()})
        self.clock += 1
        r["commits"][sha] = {"parent": parent, "date": f"2026-09-{self.clock:02d}T00:00:00Z",
                             "files": inherited}
        if branch:
            r["branches"][branch] = sha
        return sha

    def ancestors(self, repo, sha):
        out, commits = [], self.repos[repo]["commits"]
        while sha:
            out.append(sha)
            sha = commits[sha]["parent"]
        return out

    # the source interface
    def tip(self, repo, branch):
        return self.repos[repo]["branches"][branch]

    def date(self, repo, sha):
        return self.repos[repo]["commits"][sha]["date"]

    def parent(self, repo, sha):
        return self.repos[repo]["commits"][sha]["parent"]

    def file(self, repo, sha, path):
        return self.repos[repo]["commits"][sha]["files"][path]

    def compare(self, repo, base, head):
        branches = self.repos[repo]["branches"]  # like GitHub, a branch name stands for its tip
        base, head = branches.get(base, base), branches.get(head, head)
        a, b = set(self.ancestors(repo, head)), set(self.ancestors(repo, base))
        ahead, behind = len(a - b), len(b - a)
        status = ("identical" if not ahead and not behind else "ahead" if not behind
                  else "behind" if not ahead else "diverged")
        return [status, ahead, behind]

    def boundaries(self, repo, branch, base):
        chain = self.ancestors(repo, self.tip(repo, branch))
        chain = chain[:chain.index(base)] if base in chain else chain
        commits = self.repos[repo]["commits"]

        def pins(sha):
            f = commits[sha]["files"]
            return f.get("lean-toolchain"), f.get("lake-manifest.json")
        return [s for s in chain if commits[s]["parent"] and pins(s) != pins(commits[s]["parent"])]

    def cached_master_tip(self, repo):
        return self.cached

    def cache_published(self, repo, sha, tag):
        return sha not in self.uncached

    def release_tags(self, repo):
        return dict(self.tags)


def manifest(mathlib_rev):
    return json.dumps({"packages": [{"name": "mathlib", "rev": mathlib_rev}]})


def resolve(g, pins, toolchain, exclude=()):
    return rd.Resolver(g, REQUIRES, pins, toolchain).resolve(exclude)


def mathlib_line(g):
    """m0 -> m1 -> m2 (v4.34.0) -> m3 (v4.35.0-rc1) on master; s1 = v4.34.1, off m0 on stable.

    As on mathlib: the patch release diverges from master, so it is not a descendant of m1."""
    g.commit(ML, "m0", lean_toolchain=lean("v4.34.0"))
    g.commit(ML, "m1", "m0")
    g.commit(ML, "m2", "m1")
    g.commit(ML, "m3", "m2", branch="master", lean_toolchain=lean("v4.35.0-rc1"))
    g.commit(ML, "s1", "m0", branch="stable", lean_toolchain=lean("v4.34.1"))
    g.tags = {"s1": "v4.34.1"}
    g.cached = "m3"


class Toolchains(unittest.TestCase):
    # parsing and ordering are lean_versions', tested in test_lean_versions.py
    def test_rcs_share_the_line(self):
        self.assertEqual(rd.line_of(rd.parse_toolchain(lean("v4.35.0-rc3"))), (4, 35))


class Resolution(unittest.TestCase):
    def test_everything_moves_when_everything_agrees(self):
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(PL, "p2", "p1", branch="master", lake_manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        g.commit(TC, "t1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t2", "t1", branch="main", lake_manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertEqual({n: p["rev"] for n, p in r["pins"].items()},
                         {"mathlib": "m3", "Physlib": "p2", "TauCeti": "t2"})
        self.assertEqual(r["toolchain"]["chosen"], lean("v4.35.0-rc1"))
        self.assertEqual(r["holds"], [])
        self.assertTrue(r["changed"])

    def test_slow_dependency_holds_mathlib_and_the_fast_one_waits(self):
        # Physlib stays on the 4.34 line (the release tag); TauCeti races ahead to 4.35.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(PL, "p2", "p1", branch="master", lake_manifest=manifest("s1"), lean_toolchain=lean("v4.34.1"))
        g.commit(TC, "t1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t2", "t1")  # an ordinary commit, same pins: the newest one that fits
        g.commit(TC, "t3", "t2", branch="main", lake_manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertEqual({n: (p["rev"], p["fit"]) for n, p in r["pins"].items()},
                         {"mathlib": ("s1", "release"), "Physlib": ("p2", "exact"), "TauCeti": ("t2", "near")})
        held = {h["pin"]: h for h in r["holds"]}
        self.assertEqual(held["mathlib"]["held_by"], ["Physlib"])
        self.assertIn("v4.35.0-rc1", held["TauCeti"]["text"])

    def test_which_dependency_leads_is_not_hard_coded(self):
        # Same story with the roles swapped: now TauCeti is the slow one.
        g = Graph()
        mathlib_line(g)
        g.commit(TC, "t1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t2", "t1", branch="main", lake_manifest=manifest("s1"), lean_toolchain=lean("v4.34.1"))
        g.commit(PL, "p1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(PL, "p2", "p1", branch="master", lake_manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertEqual(r["pins"]["mathlib"]["rev"], "s1")
        self.assertEqual({h["pin"]: h["held_by"] for h in r["holds"]}["mathlib"], ["TauCeti"])

    def test_dependencies_never_move_backward(self):
        # TauCeti's pin is already past the 4.34 line, as on 2026-10-03: it stays, carried. A
        # carried pin is deliberately not checked against M (main builds it today), so a 4.35
        # pin rides along with mathlib's 4.34.1 tag.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", branch="master", manifest=manifest("s1"), lean_toolchain=lean("v4.34.1"))
        g.commit(TC, "t1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t2", "t1", branch="main", lake_manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t2"}, lean("v4.34.0"))
        self.assertEqual((r["pins"]["TauCeti"]["rev"], r["pins"]["TauCeti"]["fit"]), ("t2", "carried"))
        self.assertEqual(r["pins"]["mathlib"]["rev"], "s1")

    def test_carrying_is_only_allowed_within_the_current_line(self):
        # Physlib has nothing on 4.35, so mathlib may not cross to 4.35 by carrying it.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", branch="master", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t1", branch="main", manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertEqual(r["pins"]["mathlib"]["rev"], "m1")
        self.assertEqual(r["pins"]["TauCeti"]["fit"], "carried")
        blocked = {b["mathlib"]: [x["dependency"] for x in b["blockers"]] for b in r["blocked"]}
        self.assertEqual(blocked["m3"], ["Physlib"])

    def test_nothing_newer_means_unchanged_and_no_alarm(self):
        g = Graph()
        g.commit(ML, "m1", branch="master", lean_toolchain=lean("v4.34.0"))
        g.cached = "m1"
        g.commit(PL, "p1", branch="master", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t1", branch="main", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertFalse(r["changed"])
        self.assertEqual(r["holds"], [])
        self.assertIn("already on the newest compatible set", rd.summary(r))

    def test_mathlib_never_moves_backward(self):
        # A dependency pinning an older mathlib does not drag the pin back.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", branch="master", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t1", branch="main", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        r = resolve(g, {"mathlib": "m2", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertNotIn("m1", [f["mathlib"] for f in r["feasible"]])

    def test_an_excluded_set_yields_the_next_one(self):
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(PL, "p2", "p1", branch="master", lake_manifest=manifest("m2"))
        g.commit(TC, "t1", branch="main", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        pins = {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}
        first = resolve(g, pins, lean("v4.34.0"))
        self.assertEqual(first["pins"]["mathlib"]["rev"], "m2")
        bad = {n: p["rev"] for n, p in first["pins"].items()}
        second = resolve(g, pins, lean("v4.34.0"), exclude=[bad])
        self.assertNotEqual({n: p["rev"] for n, p in second["pins"].items()}, bad)

    def test_mathlib_hold_quotes_the_newest_blocked_commit(self):
        # Blocked commits are collected cached-tip first, then dependency pins: here the newer
        # m4 comes second, and its reason is the one to report.
        g = Graph()
        mathlib_line(g)
        g.commit(ML, "m4", "m3", branch="master", lean_toolchain=lean("v4.36.0-rc1"))
        g.commit(PL, "p1", branch="master", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t2", "t1", branch="main", lake_manifest=manifest("m4"), lean_toolchain=lean("v4.36.0-rc1"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertEqual([b["mathlib"] for b in r["blocked"]], ["m3", "m4"])
        held = {h["pin"]: h["text"] for h in r["holds"]}
        self.assertIn("v4.36.0-rc1's line", held["mathlib"])
        self.assertNotIn("v4.35.0-rc1's line", held["mathlib"])

    def test_hold_names_the_next_commit_that_pins_something_else(self):
        # t2 is the commit just before t3's boundary, so it pins what t1 does: it explains nothing.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", branch="master", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t1", manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        g.commit(TC, "t2", "t1")
        g.commit(ML, "m4", "m3", lean_toolchain=lean("v4.35.0-rc2"))
        g.commit(TC, "t3", "t2", branch="main", lake_manifest=manifest("m4"), lean_toolchain=lean("v4.35.0-rc2"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertEqual(r["pins"]["TauCeti"]["fit"], "carried")
        held = {h["pin"]: h["text"] for h in r["holds"]}
        self.assertIn("newer commits pin Lean v4.35.0-rc2 and mathlib m4", held["TauCeti"])

    def test_an_uncached_mathlib_is_not_offered(self):
        # Both dependencies pin m2, which fits; but m2's oleans were never published.
        g = Graph()
        mathlib_line(g)
        g.uncached = {"m2"}
        g.commit(PL, "p1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(PL, "p2", "p1", branch="master", lake_manifest=manifest("m2"))
        g.commit(TC, "t1", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t2", "t1", branch="main", lake_manifest=manifest("m2"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertNotEqual(r["pins"]["mathlib"]["rev"], "m2")
        blocked = {b["mathlib"]: [x["dependency"] for x in b["blockers"]] for b in r["blocked"]}
        self.assertEqual(blocked["m2"], ["cache"])

    def test_a_release_move_counts_the_master_commits_it_leaves_out(self):
        # s1 branches off m0; moving there from m1 leaves m1 out.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", branch="master", manifest=manifest("s1"), lean_toolchain=lean("v4.34.1"))
        g.commit(TC, "t1", branch="main", manifest=manifest("s1"), lean_toolchain=lean("v4.34.1"))
        r = resolve(g, {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.0"))
        self.assertEqual((r["pins"]["mathlib"]["rev"], r["pins"]["mathlib"]["dropped_commits"]), ("s1", 1))
        self.assertIn("leaves out 1 commit(s)", rd.summary(r))

    def test_from_a_patch_release_back_to_master(self):
        # Pinned at the v4.34.1 tag (stable): master's m3 is no descendant, but its toolchain is
        # newer and it is on master, so it is forward; s1's own commit is left out.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", branch="master", manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        g.commit(TC, "t1", branch="main", manifest=manifest("m3"), lean_toolchain=lean("v4.35.0-rc1"))
        r = resolve(g, {"mathlib": "s1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.1"))
        ml = r["pins"]["mathlib"]
        self.assertEqual((ml["rev"], ml["fit"], ml["dropped_commits"]), ("m3", "toolchain", 1))

    def test_an_older_master_commit_is_not_forward_from_a_patch_release(self):
        # m1 is on master too, but on v4.34.0: going there from v4.34.1 would be backward.
        g = Graph()
        mathlib_line(g)
        g.commit(PL, "p1", branch="master", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.commit(TC, "t1", branch="main", manifest=manifest("m1"), lean_toolchain=lean("v4.34.0"))
        g.cached = None
        r = resolve(g, {"mathlib": "s1", "Physlib": "p1", "TauCeti": "t1"}, lean("v4.34.1"))
        self.assertEqual(r["pins"]["mathlib"]["rev"], "s1")
        self.assertNotIn("m1", [f["mathlib"] for f in r["feasible"]])

    def test_unrecognised_root_toolchain_fails_cleanly(self):
        g = Graph()
        mathlib_line(g)
        with self.assertRaises(RuntimeError):
            rd.Resolver(g, REQUIRES, {"mathlib": "m1"}, "leanprover/lean4:nightly-2026-09-01")

    def test_mathlib_off_master_fails_cleanly(self):
        # the cache signals are master's, so another branch would not mean what it says
        g = Graph()
        mathlib_line(g)
        requires = [r if r[0] != "mathlib" else ("mathlib", ML, "stable") for r in REQUIRES]
        with self.assertRaises(RuntimeError):
            rd.Resolver(g, requires, {"mathlib": "m1"}, lean("v4.34.0"))


class GitHubCacheQuestion(unittest.TestCase):
    """The real GitHub class, over a fake `gh api`: the release-tag cache check shares the resolver's
    memoised compare instead of asking the same question again."""

    def test_forward_and_cache_published_ask_master_membership_once(self):
        calls = []

        def fake_gh(path, jq=None, paginate=False):
            calls.append(path)
            if "/compare/" in path:
                return json.dumps(["diverged", 1, 1]) if jq and "@json" in jq else "diverged"
            return "[]"
        saved, rd.gh = rd.gh, fake_gh
        try:
            src = rd.GitHub()
            src.compare(ML, "tag-sha", "master")        # what Resolver.forward asks
            self.assertFalse(src.cache_published(ML, "tag-sha", "v4.34.1"))
        finally:
            rd.gh = saved
        self.assertEqual(sum("/compare/" in c for c in calls), 1, calls)

    def test_cached_master_tip_is_the_shared_listing(self):
        saved, rd.gh = rd.gh, lambda path, jq=None, paginate=False: "abc\n" if "branch=master" in path else ""
        try:
            self.assertEqual(rd.GitHub().cached_master_tip(ML), "abc")
        finally:
            rd.gh = saved


class RealRecording(unittest.TestCase):
    """The upstream state of 2026-10-03, replayed against main's pins of that day."""

    PINS = {"mathlib": "db1c5741da0acf96c97584de6ccf0e3bfbc0ae99",
            "Physlib": "35d1bb4313be7127a39cd6cf29f02b758b9461b9",
            "TauCeti": "a1fff14d3219e392c7e25b0114bf5a24ba1e37bc"}
    REQUIRES = [("Physlib", "leanprover-community/physlib", "master"),
                ("TauCeti", "TauCetiProject/TauCeti", "main"),
                ("mathlib", "leanprover-community/mathlib4", "master")]

    def setUp(self):
        src = rd.Replay(json.loads((FIXTURES / "2026-10-03.json").read_text()))
        self.r = rd.Resolver(src, self.REQUIRES, self.PINS, lean("v4.34.0")).resolve()

    def test_chosen_set(self):
        self.assertEqual({n: (p["rev"][:7], p["fit"]) for n, p in self.r["pins"].items()},
                         {"mathlib": ("d13f23b", "release"),
                          "Physlib": ("d86d07d", "exact"),
                          "TauCeti": ("a1fff14", "carried")})
        self.assertEqual(self.r["toolchain"]["chosen"], lean("v4.34.1"))

    def test_physlib_is_what_holds_mathlib(self):
        held = {h["pin"]: h["held_by"] for h in self.r["holds"]}
        self.assertEqual(held, {"mathlib": ["Physlib"], "TauCeti": ["mathlib"]})

    def test_the_release_move_leaves_out_one_master_commit(self):
        # db1c574 is v4.34.0 plus #43805; the v4.34.1 tag is v4.34.0 plus the toolchain bump.
        self.assertEqual(self.r["pins"]["mathlib"]["dropped_commits"], 1)

    def test_tauceti_hold_names_a_real_change(self):
        # c60a71f, just before the first boundary, pins mathlib 5e0c4e5 like a1fff14 itself;
        # the next commit that pins something else is 81acd31, on mathlib d870b90.
        text = {h["pin"]: h["text"] for h in self.r["holds"]}["TauCeti"]
        self.assertIn("newer commits pin Lean v4.35.0-rc3 and mathlib d870b90", text)


class Project(unittest.TestCase):
    def test_reads_requires_pins_and_toolchain(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            (root / "lakefile.toml").write_text(
                'name = "X"\n[[require]]\nname = "Physlib"\ngit = "https://github.com/leanprover-community/physlib"\n'
                'rev = "master"\n[[require]]\nname = "mathlib"\n'
                'git = "https://github.com/leanprover-community/mathlib4.git"\nrev = "master"\n')
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [
                {"name": "mathlib", "rev": "a" * 40, "inherited": False},
                {"name": "Physlib", "rev": "b" * 40, "inherited": False},
                {"name": "batteries", "rev": "c" * 40, "inherited": True}]}))
            (root / "lean-toolchain").write_text(lean("v4.34.0") + "\n")
            requires, pins, tc = rd.read_project(root)
        self.assertEqual(requires, [("Physlib", "leanprover-community/physlib", "master"),
                                    ("mathlib", "leanprover-community/mathlib4", "master")])
        self.assertEqual(pins, {"mathlib": "a" * 40, "Physlib": "b" * 40})
        self.assertEqual(tc, lean("v4.34.0"))

    def test_main_replays_the_repository_itself(self):
        # The checked-in manifest must be one the resolver can read, or the job fails closed.
        requires, pins, _ = rd.read_project(Path(__file__).resolve().parents[1])
        self.assertEqual(sorted(n for n, _, _ in requires), sorted(pins))


if __name__ == "__main__":
    unittest.main()
