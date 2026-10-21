#!/usr/bin/env python3
"""Write a dependency bump into lake-manifest.json and lean-toolchain: the inverse of the guard.

scripts/resolve_deps.py chooses new revs for the direct dependencies (mathlib, Physlib, TauCeti);
this script turns that choice into the two pin files, deriving everything else exactly as
scripts/bump_manifest.py requires it, so that the bump guard (scripts/check-bump.sh) accepts the
result:

* each direct dependency keeps base's entry with only its `rev` moved;
* every other entry is inherited: the package set is the union of the direct dependencies' own
  manifests at their new revs, and a package several of them pin is the entry of the one
  lakefile.toml requires LAST (Lake takes the pins of the last require), with `inherited: true`;
* the format `version` is mathlib@new's, every other top-level field is base's;
* `lean-toolchain` is mathlib's at its new rev.

Moving a rev is not enough on its own: when a dependency drops or adds a package, the inherited
entries must follow, or the guard rejects the bump (Physlib 947b168 dropped doc-gen4 and its five
packages; see #141). The derived manifest is checked with bump_manifest.problems before anything
is written, so this script never writes a bump the guard would refuse on step 3.

Entries keep base's order; a package new to the set is appended, in the order the dependencies
are required, last first. Lake's own order is not reproduced (it depends on its resolution walk),
nothing reads the order, and the file is rendered in Lake's layout, so the diff is only the pins
that moved.

## Usage

    write_bump.py [--root DIR] --resolved RESULT.json   # the chosen set of `resolve_deps.py --json`
    write_bump.py [--root DIR] NAME=SHA ...              # move the named direct dependencies

A direct dependency not named keeps its rev. Prints what moved, or `unchanged`. Reads upstream
manifests and toolchains through `gh api` (GH_TOKEN / GITHUB_TOKEN), and runs nothing.
"""

import argparse
import json
import sys
from pathlib import Path

import bump_manifest
import resolve_deps
from bump_manifest import MATHLIB


def render(manifest):
    """lake-manifest.json text in Lake's own layout, so a rewrite changes only what moved."""
    def value(v):
        return json.dumps(v, ensure_ascii=False)

    def entry(p):
        return "{" + ",\n   ".join(f"{value(k)}: {value(v)}" for k, v in p.items()) + "}"

    fields = []
    for k, v in manifest.items():
        if k == "packages":
            body = ",\n  ".join(entry(p) for p in v)
            fields.append(f'{value(k)}:\n [{body}]')
        else:
            fields.append(f"{value(k)}: {value(v)}")
    return "{" + ",\n ".join(fields) + "}\n"


def derive(base, deps, revs, order):
    """The manifest a bump to `revs` ({direct dependency: rev}) must carry. `deps` maps each direct
    dependency to its own manifest at its new rev; `order` is lakefile.toml's require order."""
    direct = bump_manifest.direct_packages(base)
    owners = {}  # package -> the entry of the last require that pins it
    for d in order:
        for q in deps[d]["packages"]:
            if q["name"] not in direct:
                owners[q["name"]] = dict(q, inherited=True)

    packages, seen = [], set()
    for p in base["packages"]:
        name = p["name"]
        if name in direct:
            packages.append(dict(p, rev=revs.get(name, p["rev"])))
        elif name in owners:
            packages.append(owners[name])
        else:
            continue  # no dependency at its new rev pins it any more
        seen.add(name)
    for d in reversed(order):
        for q in deps[d]["packages"]:
            if q["name"] in owners and q["name"] not in seen:
                packages.append(owners[q["name"]])
                seen.add(q["name"])

    out = {k: v for k, v in base.items()}
    out["version"] = deps[MATHLIB]["version"]
    out["packages"] = packages
    return out


def write(root, revs, src):
    """Move the direct dependencies of the project at `root` to `revs` and rewrite its pin files.
    `src` answers `file(repo, sha, path)` like resolve_deps.GitHub. Returns {name: (old, new)}."""
    requires, pins, toolchain = resolve_deps.read_project(root)
    unknown = sorted(set(revs) - set(pins))
    if unknown:
        raise RuntimeError(f"not direct dependencies: {unknown}")
    base = json.loads((root / "lake-manifest.json").read_text())
    order = [name for name, _, _ in requires]
    repos = {name: repo for name, repo, _ in requires}
    new_revs = {name: revs.get(name, pins[name]) for name in pins}

    deps = {name: json.loads(src.file(repos[name], rev, "lake-manifest.json"))
            for name, rev in new_revs.items()}
    manifest = derive(base, deps, new_revs, order)
    found = bump_manifest.problems(manifest, base, deps, order)
    if found:
        raise RuntimeError(f"the derived manifest would fail the bump guard: {found[0]}")
    new_toolchain = src.file(repos[MATHLIB], new_revs[MATHLIB], "lean-toolchain").strip()

    (root / "lake-manifest.json").write_text(render(manifest))
    if new_toolchain != toolchain:
        (root / "lean-toolchain").write_text(new_toolchain + "\n")
    moved = {name: (pins[name], rev) for name, rev in new_revs.items() if rev != pins[name]}
    if new_toolchain != toolchain:
        moved["lean-toolchain"] = (toolchain, new_toolchain)
    return moved


def revs_of(args):
    if args.resolved:
        result = json.loads(args.resolved.read_text())
        return {name: pin["rev"] for name, pin in result["pins"].items()}
    revs = {}
    for arg in args.revs:
        name, sep, sha = arg.partition("=")
        if not sep or not name or not sha:
            raise RuntimeError(f"expected NAME=SHA, got {arg!r}")
        revs[name] = sha
    return revs


def main(argv=None, src=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--resolved", type=Path)
    ap.add_argument("revs", nargs="*", metavar="NAME=SHA")
    args = ap.parse_args(argv)
    if bool(args.resolved) == bool(args.revs):
        ap.error("give either --resolved FILE or NAME=SHA arguments")
    try:
        moved = write(args.root, revs_of(args), src or resolve_deps.GitHub())
    except RuntimeError as exc:
        print(f"write_bump: {exc}", file=sys.stderr)
        return 2
    if not moved:
        print("unchanged")
    for name, (old, new) in moved.items():
        print(f"{name}: {old} -> {new}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
