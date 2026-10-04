"""Whether mathlib's olean cache is published for a commit: the one definition for every script.

scripts/check-bump.sh (step 2b) and scripts/resolve_deps.py must ask this question the same way, or
the resolver proposes a pin the guard then rejects. Both call these functions.

Mathlib publishes its cache from two places, and only these:

  * a successful master-push `build.yml` run on the exact commit (`publish_cache` is gated on
    `event_name == 'push' && ref == 'refs/heads/master'`);
  * for a release tag whose commit is NOT on master (patch releases, which live on `bump_to_*` and
    `stable` branches), a successful `release_cache.yml` run on the tag.

`release_cache.yml` is no evidence for a tag that IS on master (plain release candidates and `.0`
releases): its `gate` job skips the build for those and the run still concludes `success`, so for them
only the master-push build counts.

`gh` is a callable `gh(path, jq=None) -> str` over `gh api`; it raises when the call fails. Only python3's
standard library.
"""

import json

BRANCH = "master"


def _runs(gh, repo, workflow, sha, query=""):
    """{event, head_branch} of the completed, successful runs of `workflow` on exactly `sha`."""
    out = gh(f"repos/{repo}/actions/workflows/{workflow}/runs?head_sha={sha}{query}&per_page=20",
             jq='[.workflow_runs[] | select(.status == "completed" and .conclusion == "success")'
                ' | {event, head_branch}]')
    return json.loads(out)


def master_build_published(gh, repo, sha):
    """Whether a master-push build of `sha` completed successfully, so its oleans were uploaded."""
    return any(run["head_branch"] == BRANCH for run in _runs(gh, repo, "build.yml", sha, "&event=push"))


def on_master(gh, repo, sha):
    """Whether `sha` is on master's history, so the master-push build covers its cache."""
    return gh(f"repos/{repo}/compare/{sha}...{BRANCH}", jq=".status").strip() in ("ahead", "identical")


def release_cache_published(gh, repo, sha, tag):
    """Whether `release_cache.yml` published `tag`'s cache: a successful run on the tag, for a tag
    whose commit is off master. On master it publishes nothing, whatever the run concluded."""
    if on_master(gh, repo, sha):
        return False
    return any(run["head_branch"] == tag for run in _runs(gh, repo, "release_cache.yml", sha))


def cache_published(gh, repo, sha, tag=None):
    """Whether the cache for `sha` is published, `tag` being the release tag it carries, if any."""
    return master_build_published(gh, repo, sha) or (bool(tag) and release_cache_published(gh, repo, sha, tag))
