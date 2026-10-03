#!/usr/bin/env python3
"""End-to-end tests for scripts/check-bump.sh, the bump guard.

Run with: python3 scripts/test_check_bump.py   (needs bash, jq and python3 on PATH)

No network: a fake `gh` on PATH answers `gh api <path> [--jq EXPR]` from a table and applies
the jq expression with the real `jq -r`, as `gh` does. A path missing from the table fails like
a 404. The manifests are the real ones in bump_manifest_fixtures/three_deps: EpsilonEridani
af23eb2 (a `lake update` moving TauCeti cd742d8 -> a1fff14), its parent, and the three direct
dependencies' own manifests at the revs af23eb2 pins.
"""

import base64
import copy
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
GUARD = HERE / "check-bump.sh"
THREE = HERE / "bump_manifest_fixtures" / "three_deps"

ML, PL, TC = "leanprover-community/mathlib4", "leanprover-community/physlib", "TauCetiProject/TauCeti"
ML_REV = "db1c5741da0acf96c97584de6ccf0e3bfbc0ae99"
PL_REV = "35d1bb4313be7127a39cd6cf29f02b758b9461b9"
TC_OLD, TC_NEW = "cd742d8" + "0" * 33, "a1fff14d3219e392c7e25b0114bf5a24ba1e37bc"
ML_TAG_REV, ML_MASTER_REV = "d13f23b723b8a846827a245b89c10fc7d3f11612", "5e0c4e5239cb0a2d86d68a884bf52cfd963fce22"
LEAN = "leanprover/lean4:"

FAKE_GH = r'''#!/usr/bin/env python3
import json, os, subprocess, sys
args = sys.argv[1:]
assert args[0] == "api", args
path, jq = args[1], None
if "--jq" in args:
    jq = args[args.index("--jq") + 1]
db = json.load(open(os.environ["FAKE_GH_DB"]))
with open(os.environ["FAKE_GH_LOG"], "a") as log:
    log.write(path + "\n")
if path not in db:
    sys.stderr.write(f"gh: Not Found (HTTP 404) {path}\n")
    sys.exit(1)
body = json.dumps(db[path])
if jq is None:
    print(body)
    sys.exit(0)
out = subprocess.run(["jq", "-r", jq], input=body, capture_output=True, text=True)
sys.stdout.write(out.stdout)
sys.exit(out.returncode)
'''


def load(name):
    return json.loads((THREE / f"{name}.json").read_text())


def contents(text):
    return {"content": base64.b64encode(text.encode()).decode()}


def entry(manifest, name):
    return next(p for p in manifest["packages"] if p["name"] == name)


def master_build(success=True):
    return {"workflow_runs": [{"head_branch": "master", "status": "completed",
                               "conclusion": "success" if success else "failure"}]}


class Scenario:
    """Base and PR configs plus everything the upstreams would answer."""

    def __init__(self):
        self.base = load("base")
        self.pr = load("pr")
        entry(self.base, "TauCeti")["rev"] = TC_OLD  # the fixture's base, with a full-length sha
        self.base_toolchain = self.pr_toolchain = LEAN + "v4.34.0"
        self.lakefile = 'name = "EpsilonEridani"\n'
        self.pr_lakefile = self.lakefile
        self.gh = {}
        deps = {n: load(n) for n in ("mathlib", "Physlib", "TauCeti")}
        self.manifest(ML, ML_REV, deps["mathlib"])
        self.manifest(PL, PL_REV, deps["Physlib"])
        self.manifest(TC, TC_NEW, deps["TauCeti"])
        self.toolchain(ML, ML_REV, "v4.34.0")
        self.compare(TC, TC_OLD, TC_NEW, "ahead")
        self.compare(TC, TC_NEW, "main", "ahead")

    def manifest(self, repo, rev, manifest):
        self.gh[f"repos/{repo}/contents/lake-manifest.json?ref={rev}"] = contents(json.dumps(manifest))

    def toolchain(self, repo, rev, version):
        self.gh[f"repos/{repo}/contents/lean-toolchain?ref={rev}"] = contents(LEAN + version + "\n")

    def compare(self, repo, base, head, status):
        self.gh[f"repos/{repo}/compare/{base}...{head}"] = {"status": status}

    def move_mathlib(self, rev, version, st_fwd, st_branch="behind"):
        """Point the PR's mathlib at `rev` on Lean `version`, its own manifest unchanged."""
        entry(self.pr, "mathlib")["rev"] = rev
        self.pr_toolchain = LEAN + version
        self.manifest(ML, rev, load("mathlib"))
        self.toolchain(ML, rev, version)
        self.compare(ML, ML_REV, rev, st_fwd)
        self.compare(ML, rev, "master", st_branch)
        self.gh[f"repos/{ML}/tags?per_page=100"] = []

    def run(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            for side, manifest, tc, lakefile in (("base", self.base, self.base_toolchain, self.lakefile),
                                                 ("mergebase", self.base, self.base_toolchain, self.lakefile),
                                                 ("pr", self.pr, self.pr_toolchain, self.pr_lakefile)):
                (d / side).mkdir()
                (d / side / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
                (d / side / "lean-toolchain").write_text(tc + "\n")
                (d / side / "lakefile.toml").write_text(lakefile)
            (d / "bin").mkdir()
            (d / "bin" / "gh").write_text(FAKE_GH)
            (d / "bin" / "gh").chmod(0o755)
            (d / "db.json").write_text(json.dumps(self.gh))
            env = dict(os.environ, PATH=f"{d / 'bin'}:{os.environ['PATH']}",
                       FAKE_GH_DB=str(d / "db.json"), FAKE_GH_LOG=str(d / "log"))
            out = subprocess.run(["bash", str(GUARD), str(d / "base"), str(d / "mergebase"), str(d / "pr")],
                                 capture_output=True, text=True, env=env)
            self.calls = (d / "log").read_text().splitlines() if (d / "log").exists() else []
            return out.returncode, out.stdout + out.stderr


@unittest.skipUnless(shutil.which("jq") and shutil.which("bash"), "needs jq and bash")
class Guard(unittest.TestCase):
    def assertPass(self, s, fragment=""):
        code, out = s.run()
        self.assertEqual(code, 0, out)
        self.assertIn("BUMP-GUARD: PASS", out)
        self.assertIn(fragment, out)

    def assertFail(self, s, fragment):
        code, out = s.run()
        self.assertEqual(code, 1, out)
        self.assertIn("BUMP-GUARD: FAIL", out)
        self.assertIn(fragment, out)

    # --- a dependency other than mathlib moves ------------------------------------------------

    def test_real_tauceti_bump_passes(self):
        self.assertPass(Scenario(), "TauCeti")

    def test_dependency_must_stay_on_its_branch(self):
        s = Scenario()
        s.compare(TC, TC_NEW, "main", "diverged")
        self.assertFail(s, "TauCeti new rev")

    def test_dependency_may_not_move_backward_or_sideways(self):
        for status in ("behind", "diverged"):
            with self.subTest(status=status):
                s = Scenario()
                s.compare(TC, TC_OLD, TC_NEW, status)
                self.assertFail(s, "TauCeti rev is not a forward move")

    def test_dependency_repo_swap_is_human_owned(self):
        s = Scenario()
        entry(s.pr, "TauCeti")["url"] = "https://github.com/evil/TauCeti"
        self.assertFail(s, "TauCeti url changed")

    def test_dependency_branch_swap_is_human_owned(self):
        s = Scenario()
        entry(s.pr, "Physlib")["inputRev"] = "evil"
        self.assertFail(s, "Physlib inputRev")

    def test_inherited_pins_must_be_derived(self):
        s = Scenario()
        entry(s.pr, "MD4Lean")["rev"] = "f" * 40
        self.assertFail(s, "'MD4Lean' does not match")

    def test_a_new_direct_dependency_is_human_owned(self):
        s = Scenario()
        entry(s.pr, "MD4Lean")["inherited"] = False
        self.assertFail(s, "direct dependencies differ from base")

    def test_lakefile_edits_are_human_owned(self):
        s = Scenario()
        s.pr_lakefile += "# edit\n"
        self.assertFail(s, "lakefile.toml differs from base")

    def test_nothing_moved_but_the_manifest_changed(self):
        s = Scenario()
        entry(s.pr, "TauCeti")["rev"] = TC_OLD
        entry(s.pr, "MD4Lean")["rev"] = "f" * 40
        self.assertFail(s, "no direct dependency rev changed")

    # --- mathlib moves ---------------------------------------------------------------------------

    def test_mathlib_descendant_on_master_with_a_published_cache(self):
        s = Scenario()
        s.move_mathlib(ML_MASTER_REV, "v4.34.0", "ahead", "ahead")
        s.gh[f"repos/{ML}/actions/workflows/build.yml/runs?head_sha={ML_MASTER_REV}&event=push&per_page=20"] = master_build()
        self.assertPass(s, "forward move on 'master'")

    def test_mathlib_descendant_without_a_published_cache(self):
        s = Scenario()
        s.move_mathlib(ML_MASTER_REV, "v4.34.0", "ahead", "ahead")
        s.gh[f"repos/{ML}/actions/workflows/build.yml/runs?head_sha={ML_MASTER_REV}&event=push&per_page=20"] = master_build(False)
        self.assertFail(s, "no completed, successful master-push build")

    def release(self, cached=True, version="v4.34.1"):
        s = Scenario()
        s.move_mathlib(ML_TAG_REV, version, "diverged")
        s.gh[f"repos/{ML}/tags?per_page=100"] = [{"name": "v4.34.0", "commit": {"sha": "0" * 40}},
                                                {"name": "v4.34.1", "commit": {"sha": ML_TAG_REV}}]
        s.gh[f"repos/{ML}/actions/workflows/build.yml/runs?head_sha={ML_TAG_REV}&event=push&per_page=20"] = \
            {"workflow_runs": [{"head_branch": "stable", "status": "completed", "conclusion": "success"}]}
        s.gh[f"repos/{ML}/actions/workflows/release_cache.yml/runs?head_sha={ML_TAG_REV}&per_page=20"] = \
            {"workflow_runs": [{"head_branch": "v4.34.1", "status": "completed",
                                "conclusion": "success" if cached else "failure"}]}
        return s

    def test_mathlib_patch_release_off_master(self):
        # 2026-10-03: db1c574 (master) -> d13f23b (v4.34.1 on stable), cached by release_cache.yml.
        self.assertPass(self.release(), "is release v4.34.1")

    def test_mathlib_patch_release_needs_its_release_cache(self):
        self.assertFail(self.release(cached=False), "has no completed, successful release_cache.yml run")

    def test_mathlib_diverged_onto_the_same_toolchain_is_not_forward(self):
        self.assertFail(self.release(version="v4.34.0"), "toolchain is not newer than base's")

    def test_a_tag_that_is_not_a_release_does_not_count(self):
        s = self.release()
        s.gh[f"repos/{ML}/tags?per_page=100"] = [{"name": "nightly-v4.34.1", "commit": {"sha": ML_TAG_REV}}]
        self.assertFail(s, "neither a release tag nor on branch 'master'")

    def test_mathlib_back_to_master_from_a_patch_release(self):
        # Base on v4.34.1 (stable); master's v4.35.0-rc3 commit diverged from it but is newer.
        s = Scenario()
        s.move_mathlib(ML_MASTER_REV, "v4.35.0-rc3", "diverged", "ahead")
        s.gh[f"repos/{ML}/actions/workflows/build.yml/runs?head_sha={ML_MASTER_REV}&event=push&per_page=20"] = master_build()
        self.assertPass(s, "is on 'master', on newer toolchain")

    def test_mathlib_behind_is_never_forward(self):
        s = Scenario()
        s.move_mathlib(ML_MASTER_REV, "v4.35.0-rc3", "behind", "ahead")
        self.assertFail(s, "mathlib rev is not a forward move")

    def test_only_mathlib_may_diverge(self):
        s = Scenario()
        s.compare(TC, TC_OLD, TC_NEW, "diverged")
        self.assertFail(s, "TauCeti rev is not a forward move")
        self.assertFalse([c for c in s.calls if "tags" in c or "release_cache" in c])

    def test_the_toolchain_must_be_mathlibs(self):
        s = self.release()
        s.pr_toolchain = LEAN + "v4.35.0"
        self.assertFail(s, "!= mathlib@")


if __name__ == "__main__":
    unittest.main()
