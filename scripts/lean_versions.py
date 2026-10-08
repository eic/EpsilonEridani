"""Lean release names and toolchain pins, parsed and ordered one way for every script.

The bump guard (scripts/check-bump.sh), the toolchain tags (scripts/toolchain_tags.py) and the
dependency resolver (scripts/resolve_deps.py) must agree on which toolchain move is forward, or
the resolver would propose pins the guard rejects. So the rule lives here once.

Only python3's standard library. Run as a script, `lean_versions.py newer OLD NEW` is the guard's
toolchain check: exit 0 when NEW is a strictly newer release than OLD, else say why and exit 1.
"""

import math
import re

# ASCII digits, no leading zeros: `v04.34.1` or `v٤.34.1` must not read as `v4.34.1`, because the
# guard trusts a tag by its name (mathlib's tag ruleset covers the literal `v4.*`), not by its value
_NUMBER = r"(0|[1-9][0-9]*)"
RELEASE_RE = re.compile(rf"\Av{_NUMBER}\.{_NUMBER}\.{_NUMBER}(?:-rc{_NUMBER})?\Z")
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
    """Sort key for release names; a name that is not a release sorts after every release."""
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
    """A toolchain pin for display, without its `leanprover/lean4:` prefix; `?` when there is no pin."""
    return (toolchain or "?").strip().removeprefix(TOOLCHAIN_PREFIX)


TRUSTED_MAJOR = 4  # mathlib restricts `v4.*` tags to release managers and makes them immutable


def is_trusted_release_tag(name):
    """Whether `name` is a release tag trusted as the bump guard does: a Lean release name of the
    `v4.*` series, the tags mathlib's tag ruleset restricts to release managers and makes immutable."""
    parsed = parse_release(name)
    return parsed is not None and parsed[0] == TRUSTED_MAJOR


def toolchain_order(old, new):
    """How toolchain `new` compares with `old`: "older", "same" or "newer"; None when either is
    not a release toolchain. The one comparison the guard and the resolver both read."""
    parsed_old, parsed_new = parse_toolchain(old), parse_toolchain(new)
    if parsed_old is None or parsed_new is None:
        return None
    return "older" if parsed_new < parsed_old else "same" if parsed_new == parsed_old else "newer"


def why_not_newer(old, new):
    """None when toolchain `new` is a strictly newer release than `old`; otherwise why not, in the
    words check-bump.sh reports."""
    order = toolchain_order(old, new)
    if order == "newer":
        return None
    if order is None:
        bad = old if parse_toolchain(old) is None else new
        return f"toolchain '{bad}' is not a leanprover/lean4 vX.Y.Z[-rcN] release"
    return f"toolchain moved backward ({old} -> {new})" if order == "older" else f"{new} is not newer than {old}"


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


def release_tags_by_commit(gh, repo):
    """{commit sha: its newest trusted release tag}. A commit that carries two (`v4.35.0-rc1` and
    `v4.35.0`) maps to the later release, so the guard and the resolver, which both read this, look
    for its cache under the same tag."""
    best = {}
    for name, commit in release_tags(gh, repo).items():
        if is_trusted_release_tag(name) and (commit not in best or release_key(name) > release_key(best[commit])):
            best[commit] = name
    return best


def release_tag_of(gh, repo, sha):
    """The newest trusted release tag (`is_trusted_release_tag`) naming commit `sha`, or None."""
    return release_tags_by_commit(gh, repo).get(sha)


def release_tags(gh, repo, resolve=None):
    """{release name: commit sha} for a repository's vX.Y.Z[-rcN] tags. `resolve` is the `gh` that
    dereferences annotated tags, when the listing's `gh` is a lenient one that may answer None."""
    resolve = resolve or gh
    return {name: tag_commit(resolve, repo, sha, kind) for name, (sha, kind) in release_refs(gh, repo).items()}


if __name__ == "__main__":
    import sys

    if len(sys.argv) != 4 or sys.argv[1] != "newer":
        sys.exit("usage: lean_versions.py newer OLD NEW")
    reason = why_not_newer(sys.argv[2], sys.argv[3])
    if reason:
        print(reason)
        sys.exit(1)
