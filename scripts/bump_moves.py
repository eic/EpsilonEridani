"""How a direct dependency's new rev relates to its pin: the one rule, for the guard and the resolver.

scripts/check-bump.sh (step 2) judges every moved dependency, and `Resolver.forward` in
scripts/resolve_deps.py decides which mathlib revs to propose. They must classify a move the same
way, or the resolver proposes a pin the guard refuses. Both call `mathlib_move` (this module's
command line, for the guard's bash).

A move is classified from facts about it:
  status      `compare/<pin>...<new>`: "ahead" (a descendant), "diverged", "behind" or "identical"
  on_branch   whether the new rev is on the dependency's nominated branch's history
  order       toolchain_order(pin's toolchain, new rev's): "older", "same", "newer" or None
  tag         whether the new rev carries a trusted release tag (lean_versions.release_tag_of)

Any direct dependency may move forward along its branch ("descendant"). Mathlib alone may also move
off it onto a strictly newer toolchain: at a `v4.*` release tag whether the rev descends from the pin
or diverged from it (a patch release is cut off master, after or before the pin) ("release"), or, for
a diverged rev, on the branch (the way back to master from a patch release) ("toolchain").

Only python3's standard library, apart from the guard's command line, which reads GitHub through
scripts/pr_status/core.py.
"""

import base64
import sys

import lean_versions
import mathlib_cache

MATHLIB = "mathlib"


def dependency_move(status, on_branch):
    """(kind, refusal) for any direct dependency: "descendant" when it moved forward along its branch;
    otherwise no kind and why not, "off-branch" (a descendant not on the branch) or "not-forward"."""
    if status == "ahead":
        return ("descendant", None) if on_branch else (None, "off-branch")
    return None, "not-forward"


def mathlib_move(status, on_branch, order, is_release_tag):
    """(kind, refusal) for mathlib: "descendant", "release" or "toolchain" (see the module docstring),
    else no kind and why not: "not-forward", "toolchain-not-newer" or "neither-release-nor-branch".

    `order` and `is_release_tag` are no-argument callables, called only if the rule reaches them, so
    the guard fetches the toolchain and lists the tags only for a move that needs them."""
    if status not in ("ahead", "diverged"):
        return None, "not-forward"
    if status == "ahead" and on_branch:
        return "descendant", None
    if order() != "newer":
        return None, "toolchain-not-newer"
    if is_release_tag():
        return "release", None
    if status == "diverged" and on_branch:
        return "toolchain", None
    return None, "neither-release-nor-branch"


# --- the guard's command line -----------------------------------------------------------------

def decide(name, status, st_branch, branch, old_toolchain, rev_old, rev_new, slug, gh):
    """Judge one moved dependency as check-bump.sh reports it. Returns (ok, message, details): on
    success the guard's one-line verdict and (new toolchain, tag, on_branch) for later steps; on
    refusal the reason. `gh(path, jq=None)` is a `gh api` wrapper; it raises when the call fails."""
    on_branch = mathlib_cache.is_on_master(st_branch)
    fetched = {"toolchain": "", "tag": ""}

    def order():
        try:
            content = gh(f"repos/{slug}/contents/lean-toolchain?ref={rev_new}", jq=".content")
            fetched["toolchain"] = "".join(base64.b64decode(content).decode().split())
        except Exception as exc:
            raise RuntimeError(f"cannot fetch mathlib lean-toolchain at {rev_new}: {exc}") from exc
        return lean_versions.toolchain_order(old_toolchain, fetched["toolchain"])

    def is_release_tag():
        try:
            fetched["tag"] = lean_versions.release_tag_of(gh, slug, rev_new) or ""
        except Exception as exc:
            raise RuntimeError(f"cannot list the release tags of {slug}: {exc}") from exc
        return bool(fetched["tag"])

    if name == MATHLIB:
        kind, why = mathlib_move(status, on_branch, order, is_release_tag)
    else:
        kind, why = dependency_move(status, on_branch)
    toolchain, tag = fetched["toolchain"], fetched["tag"]
    if kind == "descendant":
        message = f"{name} {rev_old} -> {rev_new} is a forward move on '{branch}'."
    elif kind == "release":
        message = f"mathlib {rev_old} -> {rev_new} is release {tag}, on newer toolchain {toolchain}."
    elif kind == "toolchain":
        message = f"mathlib {rev_old} -> {rev_new} is on '{branch}', on newer toolchain {toolchain}."
    elif why == "off-branch":
        message = f"{name} new rev {rev_new} is not on branch '{branch}' (compare status: {st_branch or 'unknown'})"
    elif why == "toolchain-not-newer":
        message = (f"mathlib rev is not a forward move from base: it is {status} of {rev_old}, not a move along "
                   f"'{branch}', and its toolchain is not newer than base's "
                   f"({lean_versions.why_not_newer(old_toolchain, toolchain)})")
    elif why == "neither-release-nor-branch":
        message = (f"mathlib new rev {rev_new} is {status} of {rev_old} and is neither a release tag nor "
                   f"on branch '{branch}' (compare status: {st_branch or 'unknown'})")
    else:
        message = f"{name} rev is not a forward move from base (compare status: {status or 'unknown'}); " \
                  f"old={rev_old} new={rev_new}"
    return kind is not None, message, (toolchain, tag, on_branch)


def main(argv):
    if len(argv) != 10 or argv[1] != "move":
        print("usage: bump_moves.py move NAME STATUS ST_BRANCH BRANCH OLD_TOOLCHAIN REV_OLD REV_NEW SLUG")
        return 2
    from pr_status.core import gh_api
    name, status, st_branch, branch, old_toolchain, rev_old, rev_new, slug = argv[2:]
    try:
        ok, message, (toolchain, tag, on_branch) = decide(
            name, status, st_branch, branch, old_toolchain, rev_old, rev_new, slug,
            lambda path, jq=None: gh_api(path, jq).strip())
    except Exception as exc:
        print(f"ERROR: {exc}")
        return 2
    print(message)
    if not ok:
        return 1
    print(toolchain)
    print(tag)
    print("1" if on_branch else "0")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
