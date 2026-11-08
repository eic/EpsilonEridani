#!/usr/bin/env python3
"""scripts/bump_excludes.py: remember pin sets whose bump build failed inside a dependency.

Run: python3 scripts/test_bump_excludes.py   (exit 0 = pass)
"""
import base64
import json
import pathlib
import sys
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import bump_excludes as be  # noqa: E402

PHYSLIB_LOG = ("✖ [9292/9383] Building Physlib.Relativity.Tensors.RealTensor.Velocity.Basic (5.7s)\n"
               "error: Physlib/Relativity/Tensors/RealTensor/Velocity/Basic.lean:27:46: Type mismatch\n")
OWN_LOG = PHYSLIB_LOG + "✖ [9284/9383] Building EpsilonEridani.Particles.Fragmentation.MomentumSumRule (6.2s)\n"
MANIFEST = json.dumps({"packages": [
    {"name": "mathlib", "rev": "m" * 40, "inherited": False},
    {"name": "Physlib", "rev": "p" * 40, "inherited": False},
    {"name": "TauCeti", "rev": "t" * 40, "inherited": False},
    {"name": "batteries", "rev": "b" * 40, "inherited": True}]})
PINS = {"mathlib": "m" * 40, "Physlib": "p" * 40, "TauCeti": "t" * 40}


class Pure(unittest.TestCase):
    def test_marker_round_trips(self):
        sets = [PINS, {"mathlib": "x" * 40}]
        self.assertEqual(be.read_marker("text\n" + be.render_marker(sets) + "\nmore"), sets)

    def test_marker_tolerates_garbage(self):
        self.assertEqual(be.read_marker("no marker"), [])
        self.assertEqual(be.read_marker("<!-- epsiloneridani-bump-excluded:v1 [oops -->"), [])
        self.assertEqual(be.read_marker('<!-- epsiloneridani-bump-excluded:v1 [{"a": 1}, {}] -->'), [])

    def test_dependency_only(self):
        self.assertTrue(be.dependency_only(be.failing_modules(PHYSLIB_LOG)))
        self.assertFalse(be.dependency_only(be.failing_modules(OWN_LOG)))
        self.assertFalse(be.dependency_only([]))

    def test_direct_pins_skip_inherited(self):
        self.assertEqual(be.direct_pins(MANIFEST), PINS)

    def test_add_set_once(self):
        sets, added = be.add_set([], PINS)
        self.assertTrue(added)
        self.assertEqual(be.add_set(sets, dict(PINS)), (sets, False))


class Main(unittest.TestCase):
    def run_main(self, pr, statuses=None, log=PHYSLIB_LOG):
        def fake_gh(*args, raw=False):
            if args[0] == "api" and "/pulls?" in args[1]:
                return [pr] if pr else []
            if args[0] == "api" and "/statuses" in args[1]:
                return statuses if statuses is not None else [
                    {"context": "build", "state": "failure", "target_url": "https://github.com/o/r/actions/runs/42"}]
            if args[0] == "api" and "lake-manifest.json" in args[1]:
                return {"content": base64.b64encode(MANIFEST.encode()).decode()}
            if args[0] == "run":
                return log
            raise AssertionError(args)

        saved = be.gh
        be.gh = fake_gh
        out = pathlib.Path(tempfile.mkdtemp()) / "exclude.json"
        try:
            be.main(["--repo", "o/r", "--branch", "bump-mathlib/resolved", "--out", str(out)])
        finally:
            be.gh = saved
        return json.loads(out.read_text())

    def pr(self, body=""):
        return {"number": 7, "body": body, "head": {"sha": "h" * 40, "repo": {"full_name": "o/r"}},
                "user": {"login": be.BOT}}

    def test_no_bump_pr_excludes_nothing(self):
        self.assertEqual(self.run_main(None), [])

    def test_dependency_failure_is_added(self):
        self.assertEqual(self.run_main(self.pr()), [PINS])

    def test_carried_sets_survive_and_are_not_duplicated(self):
        earlier = {"mathlib": "a" * 40}
        body = "x\n" + be.render_marker([earlier, PINS])
        self.assertEqual(self.run_main(self.pr(body)), [earlier, PINS])

    def test_own_failure_is_not_excluded(self):
        self.assertEqual(self.run_main(self.pr(), log=OWN_LOG), [])

    def test_green_build_is_not_excluded(self):
        green = [{"context": "build", "state": "success", "target_url": "https://github.com/o/r/actions/runs/1"}]
        self.assertEqual(self.run_main(self.pr(), statuses=green), [])

    def test_someone_elses_pr_is_ignored(self):
        pr = self.pr(be.render_marker([PINS]))
        pr["user"]["login"] = "mallory"
        self.assertEqual(self.run_main(pr), [])


class GhFailures(unittest.TestCase):
    def run_gh(self, rc, stdout="", stderr=""):
        import subprocess
        saved = be.subprocess.run
        be.subprocess.run = lambda cmd, **kw: subprocess.CompletedProcess(cmd, rc, stdout, stderr)
        try:
            return be.gh("api", "repos/o/r/pulls")
        finally:
            be.subprocess.run = saved

    def test_a_failure_stops_the_run_and_says_why(self):
        with self.assertRaises(SystemExit) as cm:
            self.run_gh(1, stderr="HTTP 403: Resource not accessible by integration")
        self.assertIn("`gh api repos/o/r/pulls` failed (1): HTTP 403", str(cm.exception))

    def test_unparseable_json_stops_the_run(self):
        with self.assertRaises(SystemExit) as cm:
            self.run_gh(0, stdout="<html>")
        self.assertIn("unparseable JSON", str(cm.exception))

    def test_success_parses(self):
        self.assertEqual(self.run_gh(0, stdout='[{"a": 1}]'), [{"a": 1}])


class ResolverHonoursIt(unittest.TestCase):
    def test_an_excluded_set_is_not_chosen_again(self):
        import test_resolve_deps as t
        g = t.Graph()
        t.mathlib_line(g)
        g.commit(t.PL, "p1", manifest=t.manifest("m1"), lean_toolchain=t.lean("v4.34.0"))
        g.commit(t.PL, "p2", "p1", branch="master", lake_manifest=t.manifest("m2"))
        g.commit(t.TC, "t1", branch="main", manifest=t.manifest("m1"), lean_toolchain=t.lean("v4.34.0"))
        pins = {"mathlib": "m1", "Physlib": "p1", "TauCeti": "t1"}
        first = t.resolve(g, pins, t.lean("v4.34.0"))
        bad = {n: p["rev"] for n, p in first["pins"].items()}
        marker = be.render_marker([bad])
        second = t.resolve(g, pins, t.lean("v4.34.0"), exclude=be.read_marker(marker))
        self.assertNotEqual({n: p["rev"] for n, p in second["pins"].items()}, bad)


if __name__ == "__main__":
    unittest.main(verbosity=1)
