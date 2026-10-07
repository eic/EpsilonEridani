#!/usr/bin/env python3
"""Pack and unpack the build outputs of EpsilonEridani's non-Mathlib dependencies.

Mathlib's cache tool (`lake exe cache get`) restores Mathlib and the packages Mathlib itself
depends on, but nothing else: every other dependency (Physlib, TauCeti, and whatever is added
to the manifest later) is compiled from source on every build. This script lets a trusted
build on main save those compiled outputs into one archive for the GitHub Actions cache, and
lets later builds restore them. Lake still decides what to reuse: it compares each module's
trace hash, so a stale output (after a pin bump) is rebuilt rather than trusted.

    dependency_builds.py packages PROJECT   # names of the packages this script covers
    dependency_builds.py pack PROJECT ARCHIVE
    dependency_builds.py unpack PROJECT ARCHIVE

The archive holds `<package>/.lake/build/...` only. `unpack` refuses the whole archive before
extracting anything if any member is not a regular file or directory under such a path, so an
archive cannot write outside `PROJECT/.lake/packages/<package>/.lake/build`. Members for a
package that is not (or no longer) in the manifest are skipped.

Pure standard library, so CI needs no `pip install`.
"""

import argparse
import json
import pathlib
import sys
import tarfile

BUILD = (".lake", "build")


def _manifest_names(path: pathlib.Path) -> set[str]:
    """Package directory names in a Lake manifest.

    Lake checks a package out under `.lake/packages/<name>` with any `«»` quoting removed, so
    `«doc-gen4»` lives in `doc-gen4`.
    """
    data = json.loads(path.read_text(encoding="utf-8"))
    return {p["name"].strip("«»") for p in data.get("packages", [])}


def covered_packages(project: pathlib.Path) -> list[str]:
    """Directory names of the dependencies whose builds Mathlib's cache tool does not restore.

    Every package in the project's manifest except `mathlib` and the packages in Mathlib's own
    manifest. Mathlib's manifest is read from the fetched checkout; when it is absent (nothing
    fetched yet) only `mathlib` itself is excluded.
    """
    names = _manifest_names(project / "lake-manifest.json")
    mathlib_manifest = project / ".lake" / "packages" / "mathlib" / "lake-manifest.json"
    mathlib_deps = _manifest_names(mathlib_manifest) if mathlib_manifest.is_file() else set()
    return sorted(names - {"mathlib"} - mathlib_deps)


def pack(project: pathlib.Path, archive: pathlib.Path) -> list[str]:
    """Archive each covered package's `.lake/build`; return the packages included."""
    packages_dir = project / ".lake" / "packages"
    included = []
    with tarfile.open(archive, "w") as tar:
        for name in covered_packages(project):
            build = packages_dir / name / pathlib.Path(*BUILD)
            if not build.is_dir():
                continue
            for path in sorted(build.rglob("*")):
                if path.is_symlink():
                    raise SystemExit(f"refusing to archive a symlink: {path}")
            tar.add(build, arcname=f"{name}/{'/'.join(BUILD)}", recursive=True)
            included.append(name)
    return included


def _check_member(member: tarfile.TarInfo) -> tuple[str, bool]:
    """Return `(package, ok)` for one archive member; `ok` is False if it must be refused."""
    parts = member.name.split("/")
    if member.name.startswith("/") or any(p in ("", ".", "..") for p in parts):
        return "", False
    if not (member.isfile() or member.isdir()):
        return "", False
    if len(parts) < 3 or tuple(parts[1:3]) != BUILD:
        return "", False
    return parts[0], True


def unpack(project: pathlib.Path, archive: pathlib.Path) -> dict[str, int]:
    """Validate the whole archive, then extract the members of covered packages.

    Returns the number of files extracted per package. Raises SystemExit, having extracted
    nothing, if any member is refused.
    """
    allowed = set(covered_packages(project))
    packages_dir = project / ".lake" / "packages"
    with tarfile.open(archive, "r") as tar:
        members = tar.getmembers()
        keep = []
        for member in members:
            package, ok = _check_member(member)
            if not ok:
                raise SystemExit(f"refusing the archive: unexpected member {member.name!r}")
            if package in allowed and (packages_dir / package).is_dir():
                keep.append(member)
        counts: dict[str, int] = {}
        for member in keep:
            if member.isfile():
                package = member.name.split("/", 1)[0]
                counts[package] = counts.get(package, 0) + 1
        tar.extractall(packages_dir, members=keep, filter="data")
    return counts


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("packages")
    p.add_argument("project", type=pathlib.Path)
    for cmd in ("pack", "unpack"):
        p = sub.add_parser(cmd)
        p.add_argument("project", type=pathlib.Path)
        p.add_argument("archive", type=pathlib.Path)
    args = ap.parse_args(argv)

    if args.cmd == "packages":
        print("\n".join(covered_packages(args.project)))
    elif args.cmd == "pack":
        included = pack(args.project, args.archive)
        print(f"packed {', '.join(included) or 'nothing'} into {args.archive}")
    else:
        counts = unpack(args.project, args.archive)
        summary = ", ".join(f"{name} ({n} files)" for name, n in sorted(counts.items()))
        print(f"restored {summary or 'nothing'} from {args.archive}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
