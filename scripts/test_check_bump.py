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
import json
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import fake_gh  # noqa: E402
GUARD = HERE / "check-bump.sh"
THREE = HERE / "bump_manifest_fixtures" / "three_deps"

ML, PL, TC = "leanprover-community/mathlib4", "leanprover-community/physlib", "TauCetiProject/TauCeti"
ML_REV = "db1c5741da0acf96c97584de6ccf0e3bfbc0ae99"
PL_REV = "35d1bb4313be7127a39cd6cf29f02b758b9461b9"
TC_OLD, TC_NEW = "cd742d8cecad86d7433e37cbd60579008c567a7e", "a1fff14d3219e392c7e25b0114bf5a24ba1e37bc"
ML_TAG_REV, ML_MASTER_REV = "d13f23b723b8a846827a245b89c10fc7d3f11612", "5e0c4e5239cb0a2d86d68a884bf52cfd963fce22"
LEAN = "leanprover/lean4:"

def lakefile(*requires, tail=""):
    """A lakefile.toml with these requires in this order, as the real one declares them."""
    blocks = "".join(f'\n[[require]]\nname = "{n}"\ngit = "https://github.com/x/{n}"\nrev = "master"\n'
                     for n in requires)
    return 'name = "EpsilonEridani"\n' + blocks + tail


LAKEFILE = lakefile("Physlib", "TauCeti", "mathlib", tail='\n[[lean_lib]]\nname = "EpsilonEridani"\n')


def load(name):
    return json.loads((THREE / f"{name}.json").read_text())


def contents(text):
    return {"content": base64.b64encode(text.encode()).decode()}


def entry(manifest, name):
    return next(p for p in manifest["packages"] if p["name"] == name)


TAGS = f"repos/{ML}/git/matching-refs/tags/v"


def tags(*named):
    """What the tag listing answers for (name, commit sha) pairs: lightweight tags, as mathlib's are."""
    return [{"ref": f"refs/tags/{name}", "object": {"sha": sha, "type": "commit"}} for name, sha in named]


def master_build(success=True):
    return {"workflow_runs": [{"head_branch": "master", "status": "completed",
                               "conclusion": "success" if success else "failure"}]}


class Scenario:
    """Base and PR configs plus everything the upstreams would answer."""

    def __init__(self):
        self.base = load("base")
        self.pr = load("pr")
        self.base_toolchain = self.pr_toolchain = LEAN + "v4.34.0"
        self.lakefile = LAKEFILE
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
        self.gh[TAGS] = []

    def run(self):
        with tempfile.TemporaryDirectory() as d:
            d = Path(d)
            for side, manifest, tc, lakefile in (("base", self.base, self.base_toolchain, self.lakefile),
                                                 ("mergebase", self.base, self.base_toolchain, self.lakefile),
                                                 ("pr", self.pr, self.pr_toolchain, self.pr_lakefile)):
                (d / side).mkdir()
                (d / side / "lake-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
                (d / side / "lean-toolchain").write_text(tc + "\n")
                if lakefile is not None:
                    (d / side / "lakefile.toml").write_text(lakefile)
            env = fake_gh.install(d, self.gh)
            out = subprocess.run(["bash", str(GUARD), str(d / "base"), str(d / "mergebase"), str(d / "pr")],
                                 capture_output=True, text=True, env=env)
            self.calls = fake_gh.calls(d)
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

    def two_pin_md4lean(self, revs):
        """Physlib and TauCeti both pin MD4Lean, differently; the PR takes the rev `revs`."""
        s = Scenario()
        taucet = load("TauCeti")
        taucet["packages"].append(dict(entry(load("Physlib"), "MD4Lean"), rev="1" * 40))
        s.manifest(TC, TC_NEW, taucet)
        entry(s.pr, "MD4Lean")["rev"] = revs
        return s

    def test_a_package_two_dependencies_pin_follows_the_lakefiles_order(self):
        # lakefile.toml requires Physlib then TauCeti, so TauCeti's pin is what Lake writes. This also
        # shows the guard hands that order to step 3: base.json lists TauCeti before Physlib, which
        # is the opposite of what step 3 would assume without it.
        self.assertPass(self.two_pin_md4lean("1" * 40), "TauCeti")
        self.assertFail(self.two_pin_md4lean(entry(load("Physlib"), "MD4Lean")["rev"]),
                        "'MD4Lean' does not match TauCeti@new's, the last require")

    def test_a_manifest_that_is_not_well_formed_is_refused_through_the_shared_shape_check(self):
        # the guard validates manifests with bump_manifest.shape, which also rejects a nameless package
        s = Scenario()
        s.pr["packages"].append({"type": "git"})
        self.assertFail(s, "PR manifest has a package without a string name")
        s = Scenario()
        s.pr["packages"].append(dict(s.pr["packages"][0]))
        self.assertFail(s, "duplicate package names in PR manifest")

    def test_mathlib_must_be_the_last_require(self):
        # Lake takes the pins of the LAST require; step 3 relies on that being mathlib
        s = Scenario()
        s.lakefile = s.pr_lakefile = lakefile("mathlib", "Physlib", "TauCeti")
        self.assertFail(s, "mathlib is not the last require")

    def test_requires_are_read_as_toml_not_by_pattern(self):
        s = Scenario()
        s.lakefile = s.pr_lakefile = LAKEFILE.replace('name = "mathlib"', "name = 'mathlib'")
        self.assertPass(s, "TauCeti")

    def test_an_unreadable_lakefile_fails_closed(self):
        s = Scenario()
        s.lakefile = s.pr_lakefile = "[[require\nname = "
        self.assertFail(s, "cannot read the requires of lakefile.toml")

    def test_a_later_table_with_a_name_is_not_a_require(self):
        s = Scenario()  # the default lakefile ends with a [[lean_lib]] that has its own `name`
        self.assertPass(s, "TauCeti")

    def test_without_a_lakefile_toml_the_order_cannot_be_checked(self):
        s = Scenario()
        s.lakefile = s.pr_lakefile = None
        self.assertFail(s, "cannot check the order of the requires")

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

    def release(self, cached=True, version="v4.34.1", fwd="diverged"):
        s = Scenario()
        s.move_mathlib(ML_TAG_REV, version, fwd)
        s.gh[TAGS] = tags(("v4.34.0", "0" * 40), ("v4.34.1", ML_TAG_REV))
        s.gh[f"repos/{ML}/actions/workflows/build.yml/runs?head_sha={ML_TAG_REV}&event=push&per_page=20"] = \
            {"workflow_runs": [{"head_branch": "stable", "status": "completed", "conclusion": "success"}]}
        s.gh[f"repos/{ML}/actions/workflows/release_cache.yml/runs?head_sha={ML_TAG_REV}&per_page=20"] = \
            {"workflow_runs": [{"head_branch": "v4.34.1", "status": "completed",
                                "conclusion": "success" if cached else "failure"}]}
        return s

    def test_mathlib_patch_release_off_master(self):
        # 2026-10-03: db1c574 (master) -> d13f23b (v4.34.1 on stable), cached by release_cache.yml.
        self.assertPass(self.release(), "is release v4.34.1")

    def test_a_release_cut_after_the_pin_is_accepted_too(self):
        # the pin lags the commit `stable` branched from, so the patch release DESCENDS from it
        # (ahead) yet is off master; the resolver offers it, so the guard must accept it
        self.assertPass(self.release(fwd="ahead"), "is release v4.34.1")

    def test_a_descendant_off_master_must_still_be_a_release_on_a_newer_toolchain(self):
        self.assertFail(self.release(fwd="ahead", version="v4.34.0"), "toolchain is not newer than base's")
        s = self.release(fwd="ahead")
        s.gh[TAGS] = tags(("v4.34.1-patch1", ML_TAG_REV))
        self.assertFail(s, "neither a release tag nor on branch 'master'")

    def test_mathlib_patch_release_needs_its_release_cache(self):
        self.assertFail(self.release(cached=False), "has no published cache")

    def on_master_release(self, master_build_ok):
        """Base on v4.34.1 (stable) moving to master's v4.35.0-rc1, a tag ON master. mathlib's
        release_cache.yml skips such tags yet concludes success, so only the master build counts."""
        s = Scenario()
        s.base_toolchain = LEAN + "v4.34.1"
        s.move_mathlib(ML_MASTER_REV, "v4.35.0-rc1", "diverged", "ahead")
        s.gh[TAGS] = tags(("v4.35.0-rc1", ML_MASTER_REV))
        s.gh[f"repos/{ML}/actions/workflows/build.yml/runs?head_sha={ML_MASTER_REV}&event=push&per_page=20"] = \
            master_build(master_build_ok)
        s.gh[f"repos/{ML}/actions/workflows/release_cache.yml/runs?head_sha={ML_MASTER_REV}&per_page=20"] = \
            {"workflow_runs": [{"head_branch": "v4.35.0-rc1", "status": "completed", "conclusion": "success"}]}
        return s

    def test_a_release_tag_on_master_is_not_cached_by_a_skipped_release_cache_run(self):
        self.assertFail(self.on_master_release(master_build_ok=False), "has no published cache")

    def test_the_guard_asks_master_membership_once(self):
        # step 2 already asked whether the new rev is on master; step 2b reuses the answer
        s = self.on_master_release(master_build_ok=False)
        self.assertFail(s, "has no published cache")
        asked = [c for c in s.calls if c == f"repos/{ML}/compare/{ML_MASTER_REV}...master"]
        self.assertEqual(len(asked), 1, s.calls)

    def test_the_guard_fetches_mathlibs_toolchain_once(self):
        s = self.on_master_release(master_build_ok=True)
        self.assertPass(s, "has a successful master-push build")
        asked = [c for c in s.calls if c == f"repos/{ML}/contents/lean-toolchain?ref={ML_MASTER_REV}"]
        self.assertEqual(len(asked), 1, s.calls)

    def test_a_failed_tag_listing_is_not_read_as_no_tag(self):
        s = self.release()
        del s.gh[TAGS]
        self.assertFail(s, "cannot list the release tags")

    def test_only_v4_tags_count_as_releases(self):
        # the trust basis is mathlib's `v4.*` tag ruleset; a v5 tag is not covered by it
        s = self.release()
        s.gh[TAGS] = tags(("v5.0.0", ML_TAG_REV))
        self.assertFail(s, "neither a release tag nor on branch 'master'")

    def test_a_release_tag_on_master_is_cached_by_its_master_build(self):
        self.assertPass(self.on_master_release(master_build_ok=True), "has a successful master-push build")

    def test_mathlib_diverged_onto_the_same_toolchain_is_not_forward(self):
        self.assertFail(self.release(version="v4.34.0"), "toolchain is not newer than base's")

    def test_a_tag_that_is_not_a_release_does_not_count(self):
        s = self.release()
        s.gh[TAGS] = tags(("v4.34.1-patch1", ML_TAG_REV))
        self.assertFail(s, "neither a release tag nor on branch 'master'")

    def test_mathlib_back_to_master_from_a_patch_release(self):
        # Base on v4.34.1 (stable); master's v4.35.0-rc3 commit diverged from it but is newer.
        s = Scenario()
        s.base_toolchain = LEAN + "v4.34.1"
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
