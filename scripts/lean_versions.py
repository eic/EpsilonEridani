"""Lean release names and toolchain pins, parsed and ordered one way for every script.

The bump guard (scripts/check-bump.sh), the toolchain tags (scripts/toolchain_tags.py) and the
dependency resolver (scripts/resolve_deps.py) must agree on which toolchain move is forward, or
the resolver would propose pins the guard rejects. So the rule lives here once.

Only python3's standard library.
"""

import math
import re

RELEASE_RE = re.compile(r"\Av(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?\Z")
TOOLCHAIN_PREFIX = "leanprover/lean4:"


def parse_release(name):
    """(major, minor, patch, rc) for a Lean release name, else None.

    A final release sorts after every rc of the same version, so rc-lessness is `inf`."""
    match = RELEASE_RE.match(name or "")
    if not match:
        return None
    major, minor, patch, rc = match.groups()
    return (int(major), int(minor), int(patch), int(rc) if rc is not None else math.inf)


def release_key(name):
    return parse_release(name) or (math.inf,) * 4


def release_of_toolchain(toolchain):
    """The release a `leanprover/lean4:vX` pin names, or None for anything else: a
    nightly, a fork channel, a local build. Only releases get tags."""
    text = (toolchain or "").strip()
    if not text.startswith(TOOLCHAIN_PREFIX):
        return None
    name = text[len(TOOLCHAIN_PREFIX):]
    return name if parse_release(name) else None


def parse_toolchain(toolchain):
    """`parse_release` of the release a toolchain pin names; None for anything else."""
    return parse_release(release_of_toolchain(toolchain))


def show_toolchain(toolchain):
    return (toolchain or "?").strip().removeprefix(TOOLCHAIN_PREFIX)


def release_refs(gh, repo):
    """{release name: (object sha, object type)} for a repository's vX.Y.Z[-rcN] tags, in one
    request. `gh(path, jq=...)` is the caller's `gh api` wrapper; it may answer None."""
    raw = gh(f"repos/{repo}/git/matching-refs/tags/v",
             jq='.[] | [.ref, .object.sha, .object.type] | @tsv') or ""
    out = {}
    for line in raw.splitlines():
        ref, sha, kind = line.split("\t")
        name = ref.removeprefix("refs/tags/")
        if parse_release(name):
            out[name] = (sha, kind)
    return out


def tag_commit(gh, repo, sha, kind):
    """The commit a tag ref names: an annotated tag's ref names the tag object, not the commit."""
    return gh(f"repos/{repo}/git/tags/{sha}", jq=".object.sha") if kind == "tag" else sha


def release_tags(gh, repo):
    """{release name: commit sha} for a repository's vX.Y.Z[-rcN] tags."""
    return {name: tag_commit(gh, repo, sha, kind) for name, (sha, kind) in release_refs(gh, repo).items()}
