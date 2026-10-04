"""Tests for scripts/bump_manifest.py, the whole-manifest check in check-bump.sh step 3."""

import copy
import json
import pathlib
import subprocess
import sys
import unittest

from bump_manifest import problems

FIXTURES = pathlib.Path(__file__).resolve().parent / "bump_manifest_fixtures"

REV_OLD, REV_NEW = "a" * 40, "b" * 40


def dep(name, rev, inherited, **extra):
    entry = {"url": f"https://github.com/example/{name}", "type": "git", "subDir": None,
             "scope": "leanprover-community", "rev": rev, "name": name,
             "manifestFile": "lake-manifest.json", "inputRev": "main",
             "inherited": inherited, "configFile": "lakefile.toml"}
    entry.update(extra)
    return entry


def mathlib(rev):
    return {"url": "https://github.com/leanprover-community/mathlib4", "type": "git",
            "subDir": None, "scope": "", "rev": rev, "name": "mathlib",
            "manifestFile": "lake-manifest.json", "inputRev": "master", "inherited": False,
            "configFile": "lakefile.lean"}


def top(name, **extra):
    m = {"version": "1.2.0", "packagesDir": ".lake/packages", "name": name, "lakeDir": ".lake",
         "fixedToolchain": name == "mathlib"}
    m.update(extra)
    return m


def fixture():
    ml = dict(top("mathlib"), packages=[dep("batteries", "c" * 40, False),
                                        dep("Cli", "d" * 40, True)])
    base = dict(top("EpsilonEridani"), packages=[mathlib(REV_OLD), dep("batteries", "e" * 40, True),
                                          dep("Cli", "f" * 40, True)])
    pr = dict(top("EpsilonEridani"), packages=[mathlib(REV_NEW), dep("batteries", "c" * 40, True),
                                        dep("Cli", "d" * 40, True)])
    return pr, ml, base


def check(pr, ml, base, **others):
    """The old single-dependency layout: mathlib is the only direct dependency."""
    return problems(pr, base, {"mathlib": ml, **others})


class BumpManifestTest(unittest.TestCase):
    def assertRejected(self, pr, ml, base, fragment):
        found = check(pr, ml, base)
        self.assertTrue(found, "expected a problem, got none")
        self.assertIn(fragment, " ".join(found))

    def test_genuine_bump_passes(self):
        self.assertEqual(check(*fixture()), [])

    def test_real_bump_passes(self):
        load = lambda n: json.loads((FIXTURES / f"{n}.json").read_text())
        self.assertEqual(check(load("pr"), load("mathlib"), load("base")), [])

    def test_manifest_format_version_must_be_mathlibs(self):
        pr, ml, base = fixture()
        ml["version"] = pr["version"] = "1.3.0"
        self.assertEqual(check(pr, ml, base), [])
        pr["version"] = "1.2.0"  # keeping base's format when mathlib@new moved is rejected
        self.assertRejected(pr, ml, base, "manifest version")
        pr["version"] = "9.9.9"
        self.assertRejected(pr, ml, base, "manifest version")
        del pr["version"]
        self.assertRejected(pr, ml, base, "manifest version")

    def test_comparison_distinguishes_json_types(self):
        pr, ml, base = fixture()
        pr["fixedToolchain"] = 0
        self.assertRejected(pr, ml, base, "top-level manifest fields differ from base")
        pr, ml, base = fixture()
        pr["packages"][1]["inherited"] = 1
        self.assertRejected(pr, ml, base, "does not match mathlib@new")

    def test_url_spelling_is_exact(self):
        pr, ml, base = fixture()
        pr["packages"][1]["url"] += ".git"
        self.assertRejected(pr, ml, base, "does not match mathlib@new")

    def test_top_level_field_removed(self):
        pr, ml, base = fixture()
        del pr["lakeDir"]
        self.assertRejected(pr, ml, base, "top-level manifest fields differ from base")

    def test_package_names_are_validated_in_every_manifest(self):
        for which in (0, 1, 2):
            for bad in (None, 7, ["x"], ""):
                with self.subTest(which=which, bad=bad):
                    ms = list(fixture())
                    ms[which]["packages"][-1]["name"] = bad
                    self.assertRejected(*ms, "without a string name")
        pr, ml, base = fixture()
        ml["packages"].append(copy.deepcopy(ml["packages"][0]))
        self.assertRejected(pr, ml, base, "duplicate package names in mathlib@new manifest")

    def test_cli_fails_cleanly_on_malformed_input(self):
        import tempfile
        with tempfile.TemporaryDirectory() as d:
            paths = []
            for i, content in enumerate(('{"packages": [{"name": {"a": 1}}]}', "{}", "[]")):
                path = pathlib.Path(d) / f"{i}.json"
                path.write_text(content)
                paths.append(str(path))
            paths[2] = f"mathlib={paths[2]}"
            script = pathlib.Path(__file__).resolve().parent / "bump_manifest.py"
            result = subprocess.run([sys.executable, str(script), *paths],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 1)
            self.assertNotIn("Traceback", result.stderr + result.stdout)

    def test_dependency_fields_beyond_the_old_four_are_compared(self):
        for field, value in (("subDir", "../../EpsilonEridani"), ("configFile", "evil.lean"),
                             ("manifestFile", "../x.json"), ("scope", "someone-else")):
            with self.subTest(field=field):
                pr, ml, base = fixture()
                pr["packages"][1][field] = value
                self.assertRejected(pr, ml, base, "does not match mathlib@new")

    def test_dependency_must_be_inherited(self):
        pr, ml, base = fixture()
        pr["packages"][1]["inherited"] = False
        self.assertRejected(pr, ml, base, "direct dependencies differ from base")

    def test_extra_or_missing_dependency_fields_are_rejected(self):
        pr, ml, base = fixture()
        pr["packages"][2]["extra"] = 1
        self.assertRejected(pr, ml, base, "does not match mathlib@new")
        pr, ml, base = fixture()
        del pr["packages"][2]["scope"]
        self.assertRejected(pr, ml, base, "does not match mathlib@new")

    def test_mathlib_entry_may_change_only_rev(self):
        for field, value in (("subDir", "x"), ("configFile", "lakefile.toml"),
                             ("manifestFile", "m.json"), ("scope", "s"), ("inherited", True),
                             ("url", "https://github.com/evil/mathlib4"), ("inputRev", "evil")):
            with self.subTest(field=field):
                pr, ml, base = fixture()
                pr["packages"][0][field] = value
                # an inherited mathlib is no longer a direct dependency at all
                self.assertRejected(pr, ml, base, "direct dependencies differ from base" if field == "inherited"
                                    else "mathlib entry changes fields other than `rev`")

    def test_top_level_fields_must_equal_base(self):
        for field, value in (("packagesDir", "EpsilonEridani/pkgs"), ("lakeDir", "EpsilonEridani/lake"),
                             ("fixedToolchain", True), ("name", "other"), ("newField", 1)):
            with self.subTest(field=field):
                pr, ml, base = fixture()
                pr[field] = value
                self.assertRejected(pr, ml, base, "top-level manifest fields differ from base")

    def test_package_set_must_match_mathlib(self):
        pr, ml, base = fixture()
        pr["packages"].append(dep("extra", "9" * 40, True))
        self.assertRejected(pr, ml, base, "no direct dependency at its new rev depends on")
        pr, ml, base = fixture()
        del pr["packages"][2]
        self.assertRejected(pr, ml, base, "is missing deps")

    def test_shape_checks(self):
        pr, ml, base = fixture()
        pr["packages"].append(copy.deepcopy(pr["packages"][1]))
        self.assertRejected(pr, ml, base, "duplicate package names")
        pr, ml, base = fixture()
        pr["packages"][1]["type"] = "path"
        self.assertRejected(pr, ml, base, "non-git package")
        pr, ml, base = fixture()
        pr["packages"][1]["rev"] = "main"
        self.assertRejected(pr, ml, base, "40-hex")


THREE = FIXTURES / "three_deps"


def three():
    """Real manifests: EpsilonEridani af23eb2 (TauCeti cd742d8 -> a1fff14, `lake update`), its
    parent 2a2b8dc, and mathlib, Physlib and TauCeti at the revs af23eb2 pins."""
    load = lambda n: json.loads((THREE / f"{n}.json").read_text())
    return load("pr"), load("base"), {n: load(n) for n in ("mathlib", "Physlib", "TauCeti")}


def entry(m, name):
    return next(p for p in m["packages"] if p["name"] == name)


MATHLIB_FIRST = FIXTURES / "mathlib_first"
TAUCETI_ONLY_DIFFERS = ["Cli", "LeanSearchClient", "Qq", "aesop", "batteries", "importGraph", "plausible",
                        "proofwidgets"]


class LastRequireWins(unittest.TestCase):
    """Why "a package mathlib pins is mathlib's entry": Lake takes the pins of the LAST require, and
    lakefile.toml declares mathlib last. Two real `lake update` outputs that differ only in the order of
    the requires (mathlib_first/README.md) show it, and rule out "first wins"."""

    def load(self, directory, name):
        return json.loads((directory / f"{name}.json").read_text())

    def pins(self, manifest, packages):
        by = {p["name"]: p["rev"] for p in manifest["packages"]}
        return {n: by[n] for n in packages}

    def disagreeing(self, deps):
        """The packages all three dependencies pin, with TauCeti's rev unlike mathlib's."""
        shared = [p["name"] for p in deps["mathlib"]["packages"]
                  if all(any(q["name"] == p["name"] for q in d["packages"]) for d in deps.values())]
        return sorted(n for n in shared if self.pins(deps["TauCeti"], [n]) != self.pins(deps["mathlib"], [n]))

    def mathlib_first(self):
        deps = {"mathlib": self.load(THREE, "mathlib"), "Physlib": self.load(THREE, "Physlib"),
                "TauCeti": self.load(MATHLIB_FIRST, "TauCeti")}
        return self.load(MATHLIB_FIRST, "root"), deps

    def test_the_two_orders_disagree_on_the_same_eight_packages(self):
        _, deps = self.mathlib_first()
        self.assertEqual(self.disagreeing(deps), TAUCETI_ONLY_DIFFERS)

    def test_mathlib_declared_first_lake_wrote_taucetis_pins(self):
        root, deps = self.mathlib_first()
        self.assertEqual(self.pins(root, TAUCETI_ONLY_DIFFERS), self.pins(deps["TauCeti"], TAUCETI_ONLY_DIFFERS))
        self.assertNotEqual(self.pins(root, TAUCETI_ONLY_DIFFERS), self.pins(deps["mathlib"], TAUCETI_ONLY_DIFFERS))

    def test_mathlib_declared_last_lake_wrote_mathlibs_pins(self):
        pr, _, deps = three()
        self.assertEqual(self.pins(pr, TAUCETI_ONLY_DIFFERS), self.pins(deps["mathlib"], TAUCETI_ONLY_DIFFERS))
        self.assertNotEqual(self.pins(pr, TAUCETI_ONLY_DIFFERS), self.pins(deps["TauCeti"], TAUCETI_ONLY_DIFFERS))

    def test_the_rule_is_for_the_mathlib_last_lakefile_only(self):
        # The mathlib-first manifest is genuine Lake output, and the guard rejects it: its rule holds
        # for the lakefile it keeps byte-identical to base, which declares mathlib last.
        root, deps = self.mathlib_first()
        found = problems(root, root, deps)
        for name in TAUCETI_ONLY_DIFFERS:
            self.assertTrue(any(f"dep {name!r} does not match mathlib@new's" in f for f in found), name)


class ThreeDependencies(unittest.TestCase):
    def assertRejected(self, pr, base, deps, fragment):
        found = problems(pr, base, deps)
        self.assertTrue(found, "expected a problem, got none")
        self.assertIn(fragment, " ".join(found))

    def test_real_lake_update_passes(self):
        self.assertEqual(problems(*three()), [])

    def test_a_shared_package_must_be_mathlibs_even_if_another_dependency_pins_it(self):
        # TauCeti@new pins its own batteries; taking it instead of mathlib's is rejected.
        pr, base, deps = three()
        tc = entry(deps["TauCeti"], "batteries")
        self.assertNotEqual(tc["rev"], entry(deps["mathlib"], "batteries")["rev"])
        pr["packages"][pr["packages"].index(entry(pr, "batteries"))] = dict(tc, inherited=True)
        self.assertRejected(pr, base, deps, "'batteries' does not match mathlib@new's")

    def test_a_package_only_physlib_pins_must_be_physlibs(self):
        pr, base, deps = three()
        entry(pr, "MD4Lean")["rev"] = "0" * 40
        self.assertRejected(pr, base, deps, "'MD4Lean' does not match the entry of Physlib@new")

    def test_a_package_two_dependencies_pin_may_be_either(self):
        pr, base, deps = three()
        md = entry(deps["Physlib"], "MD4Lean")
        deps["TauCeti"]["packages"].append(dict(md, rev="1" * 40))
        self.assertEqual(problems(pr, base, deps), [])
        entry(pr, "MD4Lean")["rev"] = "1" * 40
        self.assertEqual(problems(pr, base, deps), [])

    def test_a_package_nobody_pins_is_rejected(self):
        pr, base, deps = three()
        pr["packages"].append(dict(entry(pr, "MD4Lean"), name="Extra"))
        self.assertRejected(pr, base, deps, "no direct dependency at its new rev depends on: ['Extra']")

    def test_a_package_a_dependency_needs_is_required(self):
        pr, base, deps = three()
        pr["packages"].remove(entry(pr, "leansqlite"))
        self.assertRejected(pr, base, deps, "is missing deps that a direct dependency")

    def test_each_direct_entry_may_change_only_rev(self):
        for name in ("Physlib", "TauCeti", "mathlib"):
            for field, value in (("url", "https://github.com/evil/x"), ("inputRev", "evil"),
                                 ("subDir", "x"), ("inherited", True)):
                with self.subTest(name=name, field=field):
                    pr, base, deps = three()
                    entry(pr, name)[field] = value
                    self.assertRejected(pr, base, deps, "")

    def test_a_direct_dependency_cannot_be_added_or_dropped(self):
        pr, base, deps = three()
        entry(pr, "MD4Lean")["inherited"] = False
        self.assertRejected(pr, base, deps, "direct dependencies differ from base")
        pr, base, deps = three()
        del deps["TauCeti"]
        self.assertRejected(pr, base, deps, "base's direct dependencies are")

    def test_the_dependency_manifests_must_be_the_new_revs(self):
        # The PR moved TauCeti; checking against TauCeti's manifest at the OLD rev must not pass
        # by accident when the two pin different packages.
        pr, base, deps = three()
        deps["TauCeti"]["packages"].append(dict(entry(deps["TauCeti"], "batteries"), name="Only@old"))
        self.assertRejected(pr, base, deps, "is missing deps")

    def test_cli_takes_one_manifest_per_direct_dependency(self):
        script = pathlib.Path(__file__).resolve().parent / "bump_manifest.py"
        args = [str(THREE / "pr.json"), str(THREE / "base.json")]
        deps = [f"{n}={THREE / n}.json" for n in ("mathlib", "Physlib", "TauCeti")]
        ok = subprocess.run([sys.executable, str(script), *args, *deps], capture_output=True, text=True)
        self.assertEqual((ok.returncode, ok.stdout.strip()), (0, "OK"))
        short = subprocess.run([sys.executable, str(script), *args, *deps[:2]], capture_output=True, text=True)
        self.assertEqual(short.returncode, 1)
        self.assertIn("base's direct dependencies are", short.stdout)


if __name__ == "__main__":
    unittest.main()
