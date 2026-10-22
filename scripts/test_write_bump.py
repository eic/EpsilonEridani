#!/usr/bin/env python3
"""Unit tests for scripts/write_bump.py.

Run with: python3 scripts/test_write_bump.py

No network: the real manifests in bump_manifest_fixtures/ and write_bump_fixtures/ stand in for
`gh api`. The writer must reproduce real `lake update` outputs and a bump the guard accepted, and
whatever it writes must pass scripts/bump_manifest.py.
"""

import copy
import io
import json
import os
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import bump_manifest  # noqa: E402
import write_bump as wb  # noqa: E402

HERE = Path(__file__).resolve().parent
REPO = HERE.parent
GUARD = HERE / "bump_manifest_fixtures"
PHYSLIB = HERE / "write_bump_fixtures" / "physlib_947b168"
ORDER = ["Physlib", "TauCeti", "mathlib"]  # lakefile.toml's
REPOS = {"mathlib": "leanprover-community/mathlib4", "Physlib": "leanprover-community/physlib",
         "TauCeti": "TauCetiProject/TauCeti"}
PHYSLIB_OLD = "bae4db68ef61fc01a190fd232f82d2ad6508164e"
PHYSLIB_NEW = "947b168970238117ecf47e570c7d640c2eae4643"


def load(path):
    return json.loads(Path(path).read_text())


def physlib_deps():
    return {n: load(PHYSLIB / f"{n}.json") for n in ORDER}


class Source:
    """Answers `file(repo, sha, path)` from fixed manifests and toolchains, like resolve_deps.GitHub."""

    def __init__(self, manifests, toolchains=None):
        self.manifests, self.toolchains, self.asked = manifests, toolchains or {}, []

    def file(self, repo, sha, path):
        self.asked.append((repo, sha, path))
        if path == "lake-manifest.json":
            return json.dumps(self.manifests[(repo, sha)])
        if path == "lean-toolchain":
            return self.toolchains.get((repo, sha), "leanprover/lean4:v4.34.1") + "\n"
        raise KeyError(path)


def physlib_source():
    deps = physlib_deps()
    base = bump_manifest.direct_packages(load(PHYSLIB / "base.json"))
    manifests = {(REPOS[n], base[n]["rev"]): deps[n] for n in ("mathlib", "TauCeti")}
    manifests[(REPOS["Physlib"], PHYSLIB_NEW)] = deps["Physlib"]
    return Source(manifests)


class Render(unittest.TestCase):
    """The rendering is Lake's own layout, so a rewrite changes only the pins that moved."""

    def test_lake_written_manifests_round_trip_byte_for_byte(self):
        for path in (REPO / "lake-manifest.json", PHYSLIB / "expected.json"):
            text = path.read_text()
            self.assertEqual(wb.render(json.loads(text)), text, path)


class Derive(unittest.TestCase):
    def test_reproduces_a_real_lake_update(self):
        # three_deps: a `lake update` moving TauCeti, requires in the order Physlib, TauCeti, mathlib
        pr, base = load(GUARD / "three_deps" / "pr.json"), load(GUARD / "three_deps" / "base.json")
        deps = {n: load(GUARD / "three_deps" / f"{n}.json") for n in ORDER}
        revs = {n: p["rev"] for n, p in bump_manifest.direct_packages(pr).items()}
        derived = wb.derive(base, deps, revs, ORDER)
        self.assertTrue(bump_manifest.same(derived, pr))
        self.assertEqual(wb.render(derived), wb.render(pr))  # the order too

    def test_the_last_require_wins_in_another_order(self):
        # mathlib_first: the same upstreams required in the order mathlib, Physlib, TauCeti
        root = load(GUARD / "mathlib_first" / "root.json")
        deps = {n: load(GUARD / "three_deps" / f"{n}.json") for n in ORDER}
        revs = {n: p["rev"] for n, p in bump_manifest.direct_packages(root).items()}
        derived = wb.derive(root, deps, revs, ["mathlib", "Physlib", "TauCeti"])
        self.assertEqual(wb.render(derived), wb.render(root))

    def test_a_dependency_dropping_packages_drops_them(self):
        # #141: Physlib 947b168 no longer requires doc-gen4, so its five packages go
        base = load(PHYSLIB / "base.json")
        derived = wb.derive(base, physlib_deps(), {"Physlib": PHYSLIB_NEW}, ORDER)
        self.assertEqual(wb.render(derived), (PHYSLIB / "expected.json").read_text())
        self.assertEqual(bump_manifest.problems(derived, base, physlib_deps(), ORDER), [])

    def test_a_package_new_to_the_set_is_appended(self):
        base = load(PHYSLIB / "expected.json")
        deps = physlib_deps()
        extra = dict(deps["Physlib"]["packages"][-1], name="NewThing",
                     url="https://github.com/example/NewThing")
        deps["Physlib"]["packages"].append(extra)
        derived = wb.derive(base, deps, {}, ORDER)
        self.assertEqual(derived["packages"][-1], dict(extra, inherited=True))
        self.assertEqual(derived["packages"][:-1], base["packages"])
        self.assertEqual(bump_manifest.problems(derived, base, deps, ORDER), [])


class Write(unittest.TestCase):
    """The command end to end, on a copy of the project at the parent of #141."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        shutil.copy(REPO / "lakefile.toml", self.root / "lakefile.toml")
        (self.root / "lake-manifest.json").write_text(wb.render(load(PHYSLIB / "base.json")))
        (self.root / "lean-toolchain").write_text("leanprover/lean4:v4.34.1\n")

    def run_main(self, argv, src):
        out, err = io.StringIO(), io.StringIO()
        with redirect_stdout(out), redirect_stderr(err):
            code = wb.main(["--root", str(self.root), *argv], src=src)
        return code, out.getvalue(), err.getvalue()

    def test_name_equals_sha_writes_the_accepted_bump(self):
        code, out, _ = self.run_main([f"Physlib={PHYSLIB_NEW}"], physlib_source())
        self.assertEqual(code, 0)
        self.assertEqual(out, f"Physlib: {PHYSLIB_OLD} -> {PHYSLIB_NEW}\n")
        self.assertEqual((self.root / "lake-manifest.json").read_text(),
                         (PHYSLIB / "expected.json").read_text())
        self.assertEqual((self.root / "lean-toolchain").read_text(), "leanprover/lean4:v4.34.1\n")

    def test_the_resolver_answer_is_read_from_its_json(self):
        result = {"pins": {"mathlib": {"rev": "d13f23b723b8a846827a245b89c10fc7d3f11612"},
                           "Physlib": {"rev": PHYSLIB_NEW},
                           "TauCeti": {"rev": "a1fff14d3219e392c7e25b0114bf5a24ba1e37bc"}}}
        resolved = self.root / "resolved.json"
        resolved.write_text(json.dumps(result))
        code, _, _ = self.run_main(["--resolved", str(resolved)], physlib_source())
        self.assertEqual(code, 0)
        self.assertEqual((self.root / "lake-manifest.json").read_text(),
                         (PHYSLIB / "expected.json").read_text())

    def test_the_toolchain_follows_mathlib(self):
        src = physlib_source()
        mathlib_rev = "d13f23b723b8a846827a245b89c10fc7d3f11612"
        src.toolchains[(REPOS["mathlib"], mathlib_rev)] = "leanprover/lean4:v4.35.0"
        code, out, _ = self.run_main([f"Physlib={PHYSLIB_NEW}"], src)
        self.assertEqual(code, 0)
        self.assertEqual((self.root / "lean-toolchain").read_text(), "leanprover/lean4:v4.35.0\n")
        self.assertIn("lean-toolchain: leanprover/lean4:v4.34.1 -> leanprover/lean4:v4.35.0", out)

    def test_nothing_moved_is_unchanged(self):
        before = (self.root / "lake-manifest.json").read_text()
        # Physlib at its current pin still pins every inherited package base has
        inherited = [p for p in load(PHYSLIB / "base.json")["packages"] if p["inherited"]]
        src = physlib_source()
        src.manifests[(REPOS["Physlib"], PHYSLIB_OLD)] = dict(physlib_deps()["Physlib"], packages=inherited)
        code, out, _ = self.run_main([f"Physlib={PHYSLIB_OLD}"], src)
        self.assertEqual(code, 0)
        self.assertEqual(out, "unchanged\n")
        self.assertEqual((self.root / "lake-manifest.json").read_text(), before)

    def test_a_bump_the_guard_would_refuse_is_not_written(self):
        before = (self.root / "lake-manifest.json").read_text()
        src = physlib_source()
        key = (REPOS["mathlib"], "d13f23b723b8a846827a245b89c10fc7d3f11612")
        mathlib = copy.deepcopy(src.manifests[key])
        mathlib["packages"][-1]["type"] = "path"  # the guard pins only git packages
        src.manifests[key] = mathlib
        code, _, err = self.run_main([f"Physlib={PHYSLIB_NEW}"], src)
        self.assertEqual(code, 2)
        self.assertIn("would fail the bump guard", err)
        self.assertEqual((self.root / "lake-manifest.json").read_text(), before)

    def test_only_direct_dependencies_can_be_moved(self):
        code, _, err = self.run_main(["batteries=" + "c" * 40], physlib_source())
        self.assertEqual(code, 2)
        self.assertIn("not direct dependencies: ['batteries']", err)


if __name__ == "__main__":
    unittest.main()
