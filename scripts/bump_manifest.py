"""Whole-manifest check for a dependency bump, used by scripts/check-bump.sh (step 3).

check-bump.sh has already established that each direct dependency (every package base's
manifest does not mark `inherited`: mathlib, Physlib, TauCeti) either keeps its `rev` or moves
it forward on its nominated branch. This module checks that nothing ELSE in the PR's
lake-manifest.json differs from what those facts determine:

* every top-level field (`name`, `packagesDir`, `lakeDir`, `fixedToolchain`, ...) equals the base
  manifest's, with the same set of keys, and the format `version` equals mathlib@new's (Lake decodes
  entries according to `version`, and the shared entries are mathlib@new's);
* the direct dependencies are exactly base's, and each entry equals base's in every field except
  `rev` (so `inherited` stays `false`, and the url, `inputRev`, `subDir`, ... cannot move);
* every other entry is inherited: the package set is exactly the union of the direct
  dependencies' own manifests at their new revs, minus the direct dependencies themselves, and
  each entry equals the same-named entry of one of those manifests in every field, except that
  `inherited` is `true` (Lake marks a dependency's dependencies as inherited when it writes a
  downstream manifest). A package mathlib@new pins must be mathlib@new's entry: the lakefile
  orders its requires so that mathlib's pins win, and mathlib's cache was built against them. A
  package only another dependency pins (Physlib's doc-gen4, say) must be that dependency's entry.

Comparing whole entries matters: Lake also reads `subDir`, `configFile`, `manifestFile` and
`scope` from these entries, and `packagesDir`/`lakeDir` from the top level, before any sandbox
runs. A four-field comparison would let a bump that passes every other check change them.

Usage: bump_manifest.py <pr-manifest> <base-manifest> <name>=<its-manifest-at-new-rev> ...
with one <name>= argument per direct dependency, mathlib included.
Prints OK and exits 0, or prints the first problem and exits 1.
"""

import json
import re
import sys

MATHLIB = "mathlib"


def same(a, b) -> bool:
    """JSON equality that distinguishes types (Python's `==` has `True == 1` and `0 == False`)."""
    if type(a) is not type(b):
        return False
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    return a == b


def differing(a: dict, b: dict, skip=()) -> list[str]:
    return [k for k in sorted(set(a) | set(b), key=str)
            if k not in skip and not same(a.get(k, ...), b.get(k, ...))]


def shape(name: str, m) -> list[str]:
    if not isinstance(m, dict) or not isinstance(m.get("packages"), list):
        return [f"{name} manifest is not an object with a `packages` list"]
    if not all(isinstance(p, dict) for p in m["packages"]):
        return [f"{name} manifest has a package entry that is not an object"]
    names = [p.get("name") for p in m["packages"]]
    if not all(isinstance(n, str) and n for n in names):
        return [f"{name} manifest has a package without a string name"]
    dups = sorted({n for n in names if names.count(n) > 1})
    if dups:
        return [f"duplicate package names in {name} manifest: {dups}"]
    return []


def problems(pr: dict, base: dict, deps: dict) -> list[str]:
    """`deps` maps each direct dependency's name to its own manifest at the PR's rev."""
    if not isinstance(deps, dict) or MATHLIB not in deps:
        return ["no manifest given for mathlib@new"]
    for name, m in (("PR", pr), ("base", base), *((f"{n}@new", d) for n, d in deps.items())):
        found = shape(name, m)
        if found:
            return found
    ml = deps[MATHLIB]
    out: list[str] = []

    # `version` is the manifest format. Lake decodes every entry according to it, and the shared
    # entries are mathlib@new's, so it must be mathlib@new's. Every other top-level field equals base.
    changed = differing(pr, base, skip=("packages", "version"))
    if changed:
        out.append(f"top-level manifest fields differ from base: {changed}")
    if "version" not in pr or not same(pr.get("version"), ml.get("version")):
        out.append(f"manifest version {pr.get('version')!r} is not mathlib@new's "
                   f"({ml.get('version')!r})")

    for p in pr["packages"]:
        if p.get("type") != "git":
            out.append(f"PR pins non-git package {p.get('name')!r} (type {p.get('type')!r})")
        if not re.fullmatch(r"[0-9a-f]{40}", str(p.get("rev") or "")):
            out.append(f"PR dep {p.get('name')!r} rev is not a 40-hex commit SHA")
    if out:
        return out

    # The direct dependencies: base's, and only their `rev` may move.
    base_direct = {p["name"]: p for p in base["packages"] if p.get("inherited") is False}
    if MATHLIB not in base_direct:
        return ["base manifest has no direct `mathlib` package"]
    if set(deps) != set(base_direct):
        return [f"manifests given for {sorted(deps)}, but base's direct dependencies are "
                f"{sorted(base_direct)}"]
    pr_by = {p["name"]: p for p in pr["packages"]}
    pr_direct = {n for n, p in pr_by.items() if p.get("inherited") is False}
    if pr_direct != set(base_direct):
        return [f"direct dependencies differ from base: {sorted(pr_direct)} != {sorted(base_direct)}"]
    for n in sorted(base_direct):
        changed = differing(pr_by[n], base_direct[n], skip=("rev",))
        if changed:
            out.append(f"the {n} entry changes fields other than `rev`: {changed}")

    # Everything else is inherited from the direct dependencies at their new revs.
    owners: dict[str, list[tuple[str, dict]]] = {}
    for d in sorted(deps, key=lambda n: n != MATHLIB):  # mathlib first
        for q in deps[d]["packages"]:
            if q["name"] not in base_direct:
                owners.setdefault(q["name"], []).append((d, q))
    inherited = {n: p for n, p in pr_by.items() if n not in base_direct}
    only_pr, only_deps = sorted(set(inherited) - set(owners)), sorted(set(owners) - set(inherited))
    if only_pr:
        out.append(f"PR pins deps that no direct dependency at its new rev depends on: {only_pr}")
    if only_deps:
        out.append(f"PR is missing deps that a direct dependency at its new rev depends on: {only_deps}")
    for n in sorted(set(inherited) & set(owners)):
        ml_entry = [q for d, q in owners[n] if d == MATHLIB]
        candidates = ml_entry or [q for _, q in owners[n]]  # mathlib's pin wins where it has one
        if not any(same(inherited[n], dict(q, inherited=True)) for q in candidates):
            whose = "mathlib@new's" if ml_entry else \
                "the entry of " + " or ".join(f"{d}@new" for d, _ in owners[n])
            changed = differing(inherited[n], dict(candidates[0], inherited=True))
            out.append(f"dep {n!r} does not match {whose} (fields {changed})")
    return out


def main(argv: list[str]) -> int:
    if len(argv) < 4 or not all("=" in a for a in argv[3:]):
        print(__doc__.strip().splitlines()[-3])
        return 2
    try:
        pr, base = (json.load(open(path)) for path in argv[1:3])
        deps = {}
        for arg in argv[3:]:
            name, path = arg.split("=", 1)
            deps[name] = json.load(open(path))
    except Exception as e:
        print(f"cannot parse manifest: {e}")
        return 1
    try:
        found = problems(pr, base, deps)
    except Exception as e:  # malformed input must fail closed with a message, not a traceback
        print(f"cannot validate manifest: {type(e).__name__}: {e}")
        return 1
    if found:
        print(found[0])
        return 1
    print("OK")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
