"""Whether mathlib's olean cache is published for a commit: the one definition for every script.

scripts/check-bump.sh (step 2b) and scripts/resolve_deps.py must ask this question the same way, or
the resolver proposes a pin the guard then rejects. Both call `cache_source` / `cache_published`,
which with `newest_master_build` are this module's whole surface: the underscored functions are the
parts they are made of, not other ways to ask the question.

Mathlib publishes its cache from two places, and only these:

  * a successful master-push `build.yml` run on the exact commit: its `upload_cache` job writes to the
    master container because `cache_application_id` / `cache_environment` resolve to the master writer
    when `ref_name == 'master'`. Restricting to `event=push` is this module's own narrowing: it names
    the build of a batch's final commit, the one run whose oleans are all there;
  * for a release tag whose commit is NOT on master (patch releases, which live on `bump_to_*` and
    `stable` branches), a successful `release_cache.yml` run on the tag.

`release_cache.yml` is no evidence for a tag that IS on master (plain release candidates and `.0`
releases): its `gate` job skips the build for those and the run still concludes `success`, so for them
only the master-push build counts.

`gh` is a callable `gh(path, jq=None) -> str` over `gh api`; it raises when the call fails. Only python3's
standard library.
"""

import json

import bump_moves

BRANCH = "master"


def _runs(gh, repo, workflow, sha, query=""):
    """{event, head_branch} of the completed, successful runs of `workflow` on exactly `sha`."""
    out = gh(f"repos/{repo}/actions/workflows/{workflow}/runs?head_sha={sha}{query}&per_page=20",
             jq='[.workflow_runs[] | select(.status == "completed" and .conclusion == "success")'
                ' | {event, head_branch}]')
    return json.loads(out)


def _master_build_published(gh, repo, sha):
    """Whether a master-push build of `sha` completed successfully, so its oleans were uploaded."""
    return any(run["head_branch"] == BRANCH for run in _runs(gh, repo, "build.yml", sha, "&event=push"))


def newest_master_build(gh, repo):
    """The commit of master's newest completed, successful master-push build (its cache is
    published), or None before there is one. The listing form of `_master_build_published`: a renamed
    `build.yml` answers 404 and `gh` raises, as for the per-commit question."""
    out = gh(f"repos/{repo}/actions/workflows/build.yml/runs?branch={BRANCH}&event=push&status=success&per_page=1",
             jq=".workflow_runs[0].head_sha // empty")
    return out.strip() or None


def _on_master(gh, repo, sha):
    """Whether `sha` is on master's history, so the master-push build covers its cache."""
    return bump_moves.is_on_branch(gh(f"repos/{repo}/compare/{sha}...{BRANCH}", jq=".status").strip())


def _release_cache_published(gh, repo, sha, tag, known_on_master=None):
    """Whether `release_cache.yml` published `tag`'s cache: a successful run on the tag, for a tag
    whose commit is off master. On master it publishes nothing, whatever the run concluded.
    `known_on_master` is a no-argument callable for a caller that already holds the compare answer."""
    if (known_on_master or (lambda: _on_master(gh, repo, sha)))():
        return False
    return any(run["head_branch"] == tag for run in _runs(gh, repo, "release_cache.yml", sha))


def cache_source(gh, repo, sha, tag=None, known_on_master=None):
    """What publishes the cache for `sha`, `tag` being the release tag it carries, if any: "master"
    (a master-push build), "release" (release_cache.yml, for a tag off master), or None. The one
    composition of the two signals: callers that report which one applied read it here."""
    if _master_build_published(gh, repo, sha):
        return "master"
    if tag and _release_cache_published(gh, repo, sha, tag, known_on_master):
        return "release"
    return None


def cache_published(gh, repo, sha, tag=None, known_on_master=None):
    """Whether the cache for `sha` is published; see `cache_source`."""
    return cache_source(gh, repo, sha, tag, known_on_master) is not None
