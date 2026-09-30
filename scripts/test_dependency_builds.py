#!/usr/bin/env python3
"""Tests for scripts/dependency_builds.py.

Run with:

    python3 scripts/test_dependency_builds.py
"""

import io
import json
import pathlib
import sys
import tarfile
import tempfile
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
import dependency_builds as db  # noqa: E402


def manifest(path: pathlib.Path, names) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps({"packages": [{"name": n} for n in names]}))


class Project:
    """A fake workspace: root manifest, a fetched Mathlib manifest, dependency checkouts."""

    def __init__(self, root: pathlib.Path):
        self.root = root
        manifest(root / "lake-manifest.json", ["mathlib", "Physlib", "TauCeti", "batteries"])
        manifest(root / ".lake/packages/mathlib/lake-manifest.json", ["batteries", "aesop"])
        for name in ("mathlib", "Physlib", "TauCeti", "batteries"):
            (root / ".lake/packages" / name).mkdir(parents=True, exist_ok=True)

    def build_file(self, package: str, rel: str, text: str = "olean") -> pathlib.Path:
        path = self.root / ".lake/packages" / package / ".lake/build" / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        return path


class CoveredPackagesTest(unittest.TestCase):
    def test_excludes_mathlib_and_its_own_dependencies(self):
        with tempfile.TemporaryDirectory() as tmp:
            project = Project(pathlib.Path(tmp))
            self.assertEqual(db.covered_packages(project.root), ["Physlib", "TauCeti"])

    def test_quoted_package_names_map_to_their_directories(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            manifest(root / "lake-manifest.json", ["mathlib", "«doc-gen4»"])
            self.assertEqual(db.covered_packages(root), ["doc-gen4"])

    def test_without_a_fetched_mathlib_only_mathlib_is_excluded(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = pathlib.Path(tmp)
            manifest(root / "lake-manifest.json", ["mathlib", "Physlib", "batteries"])
            self.assertEqual(db.covered_packages(root), ["Physlib", "batteries"])


class RoundTripTest(unittest.TestCase):
    def test_pack_then_unpack_restores_only_covered_builds(self):
        with tempfile.TemporaryDirectory() as src, tempfile.TemporaryDirectory() as dst:
            source = Project(pathlib.Path(src))
            source.build_file("Physlib", "lib/lean/Physlib/A.olean", "physlib-a")
            source.build_file("batteries", "lib/lean/Batteries.olean", "not ours")
            # TauCeti has no build directory: nothing imports it, so it is never compiled.
            archive = pathlib.Path(src) / "deps.tar"
            self.assertEqual(db.pack(source.root, archive), ["Physlib"])

            target = Project(pathlib.Path(dst))
            self.assertEqual(db.unpack(target.root, archive), {"Physlib": 1})
            restored = target.root / ".lake/packages/Physlib/.lake/build/lib/lean/Physlib/A.olean"
            self.assertEqual(restored.read_text(), "physlib-a")
            self.assertFalse((target.root / ".lake/packages/batteries/.lake/build").exists())

    def test_members_of_a_package_no_longer_in_the_manifest_are_skipped(self):
        with tempfile.TemporaryDirectory() as src, tempfile.TemporaryDirectory() as dst:
            source = Project(pathlib.Path(src))
            source.build_file("TauCeti", "lib/lean/TauCeti.olean")
            archive = pathlib.Path(src) / "deps.tar"
            db.pack(source.root, archive)

            target = Project(pathlib.Path(dst))
            manifest(target.root / "lake-manifest.json", ["mathlib", "Physlib"])
            self.assertEqual(db.unpack(target.root, archive), {})
            self.assertFalse((target.root / ".lake/packages/TauCeti/.lake/build").exists())

    def test_pack_refuses_a_symlink(self):
        with tempfile.TemporaryDirectory() as src:
            source = Project(pathlib.Path(src))
            target = source.build_file("Physlib", "lib/lean/A.olean")
            (target.parent / "link.olean").symlink_to(target)
            with self.assertRaises(SystemExit):
                db.pack(source.root, pathlib.Path(src) / "deps.tar")


def archive_with(tmp: pathlib.Path, members) -> pathlib.Path:
    """Build an archive from `(TarInfo, bytes-or-None)` pairs."""
    path = tmp / "evil.tar"
    with tarfile.open(path, "w") as tar:
        for info, data in members:
            if data is None:
                tar.addfile(info)
            else:
                info.size = len(data)
                tar.addfile(info, io.BytesIO(data))
    return path


class RefusalTest(unittest.TestCase):
    def assert_refused(self, members):
        with tempfile.TemporaryDirectory() as tmp:
            project = Project(pathlib.Path(tmp))
            archive = archive_with(pathlib.Path(tmp), members)
            with self.assertRaises(SystemExit):
                db.unpack(project.root, archive)
            # Nothing at all was extracted, not even the valid members.
            self.assertFalse((project.root / ".lake/packages/Physlib/.lake").exists())

    def valid(self):
        return (tarfile.TarInfo("Physlib/.lake/build/ok.olean"), b"ok")

    def test_parent_traversal(self):
        self.assert_refused([self.valid(), (tarfile.TarInfo("Physlib/.lake/build/../../x"), b"x")])

    def test_absolute_path(self):
        self.assert_refused([self.valid(), (tarfile.TarInfo("/etc/passwd"), b"x")])

    def test_path_outside_a_build_directory(self):
        self.assert_refused([self.valid(), (tarfile.TarInfo("Physlib/lakefile.toml"), b"x")])

    def test_symlink_member(self):
        link = tarfile.TarInfo("Physlib/.lake/build/link")
        link.type, link.linkname = tarfile.SYMTYPE, "/etc/passwd"
        self.assert_refused([self.valid(), (link, None)])

    def test_hardlink_member(self):
        link = tarfile.TarInfo("Physlib/.lake/build/link")
        link.type, link.linkname = tarfile.LNKTYPE, "Physlib/.lake/build/ok.olean"
        self.assert_refused([self.valid(), (link, None)])


if __name__ == "__main__":
    unittest.main()
