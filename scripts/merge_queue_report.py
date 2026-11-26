#!/usr/bin/env python3
"""Report a failed merge-group `pr-build` run on the PR it was building.

When the merge queue's build of a PR fails, GitHub only records "removed from the merge queue" on
the PR; the failing run, and the `build` status that links to it, sit on the queue's temporary
`gh-readonly-queue/...` commit, which the PR page never shows. This posts that information as a PR
comment: a link to the run, the failed jobs and steps, the first error lines of each failed job's
log, the `main` commit the group was built on, and the other PRs in the group (a failure in a
batched group may be caused by a PR ahead of this one).

One comment per PR head, edited in place when the queue fails the same head again, so repeated
evictions of one head do not flood the thread; a new head gets a new comment.

Env:
  REPO           owner/name
  RUN_ID         the failed pr-build workflow run
  HEAD_BRANCH    the run's head branch, gh-readonly-queue/<base>/pr-<N>-<base sha>
  HEAD_SHA       the merge-group commit the run built
  GH_TOKEN       read token (actions: read, contents: read, pull-requests: read)
  COMMENT_TOKEN  token that may comment on pull requests (defaults to GH_TOKEN)
  DRY_RUN=1      print the comment instead of posting it

Log contents come from building untrusted PR code: they are only ever quoted inside a fenced code
block, with any fence in them defused, and never interpreted.
"""

from __future__ import annotations

import os
import re
import sys

import merge_group_prs
from gh_utils import gh, gh_json, upsert_marked_comment

MARKER = "<!--merge-queue-failure:v1 {head}-->"
MARKER_RE = re.compile(r"<!--merge-queue-failure:v1 ([0-9a-f]{40})-->")
BRANCH_RE = re.compile(r"^gh-readonly-queue/(?P<base>.+)/pr-(?P<pr>\d+)-(?P<sha>[0-9a-f]{40})$")
# A GitHub log line is "<ISO timestamp> <text>"; strip the stamp and ANSI colour codes.
STAMP_RE = re.compile(r"^\d{4}-\d\d-\d\dT[\d:.]+Z ?")
ANSI_RE = re.compile(r"\x1b\[[0-9;]*m")
# Lean/Lake errors ("error: <file>:<l>:<c>: ...", "error: build failed"), the build's own `::error::`
# annotations as rendered in the log, and lines Lake marks as a failed module.
ERROR_RE = re.compile(r"^(error(\[[^\]]*\])?:|##\[error\]|✖ )")
# Exit-code noise that every failed step prints and that says nothing about the cause.
NOISE_RE = re.compile(r"^##\[error\]Process completed with exit code \d+\.?$")

MAX_JOBS = 3
MAX_LINES = 25
MAX_LINE_CHARS = 400


def parse_branch(branch):
    """(base branch, PR number, base sha) of a merge-queue head branch, or None."""
    m = BRANCH_RE.match(branch or "")
    return (m["base"], int(m["pr"]), m["sha"]) if m else None


def extract_errors(log, max_lines=MAX_LINES):
    """(the distinct error lines of a job log, in order, without timestamps or colour codes;
    whether yet more distinct error lines followed past the cap)."""
    seen, out, more = set(), [], False
    for raw in log.splitlines():
        line = ANSI_RE.sub("", STAMP_RE.sub("", raw)).rstrip()
        if not ERROR_RE.match(line) or NOISE_RE.match(line) or line in seen:
            continue
        seen.add(line)
        if len(out) >= max_lines:
            more = True
            break
        out.append(line if len(line) <= MAX_LINE_CHARS else line[:MAX_LINE_CHARS] + " …")
    return out, more


def defuse(text):
    """Text that cannot close the code fence it is quoted in."""
    return text.replace("```", "ʼʼʼ")


def group_prs(subjects, this_pr):
    """PR numbers of the squash commits in the group, other than this PR, in queue order.
    A subject that carries no number is skipped — this report only names the group's other
    PRs — while scripts/lint-scope.sh fails closed on the same case; the shared convention
    lives in scripts/merge_group_prs.py."""
    seen = []
    for n in merge_group_prs.pr_numbers(subjects):
        if n is not None and n != this_pr and n not in seen:
            seen.append(n)
    return seen


def render(*, pr_head, run_url, base_branch, base_sha, group_sha, jobs, others,
           total_failed=None):
    """The comment body. `jobs` is a list of {name, url, steps, errors, truncated}: the
    first MAX_JOBS of the run's `total_failed` failed jobs, each holding at most MAX_LINES
    error lines; where a cap bites, the body says so."""
    lines = [
        f"### Merge queue: build failed for head `{pr_head[:7]}`",
        "",
        f"The merge-group build of this PR on top of `{base_branch}` @ `{base_sha[:7]}` "
        f"(merge-group commit `{group_sha[:7]}`) failed: **[pr-build run]({run_url})**.",
        "",
    ]
    if others:
        lines += ["This group also contained "
                  + ", ".join(f"#{n}" for n in others)
                  + " ahead of this PR; the failure may come from one of them.", ""]
    if not jobs:
        lines += ["No failed job was found in the run; see the run for details.", ""]
    for j in jobs:
        steps = ", ".join(f"`{s}`" for s in j["steps"]) or "unknown step"
        lines += [f"**[{j['name']}]({j['url']})** failed in {steps}.", ""]
        if j["errors"]:
            lines += ["```text", *(defuse(e) for e in j["errors"]), "```"]
            if j.get("truncated"):
                lines += [f"(first {MAX_LINES} error lines; see the job log for the rest)"]
            lines += [""]
        else:
            lines += ["No error lines were found in the job log; see the job for details.", ""]
    if total_failed and total_failed > len(jobs):
        lines += [f"And {total_failed - len(jobs)} more failed job(s); see the "
                  f"[pr-build run]({run_url}).", ""]
    lines += [
        "A PR's own `pr-build` builds its exact head, not head + current "
        f"`{base_branch}`; if `{base_branch}` has moved (for example a dependency bump), merge it "
        "into this branch to reproduce the failure in the PR's checks.",
        "",
        MARKER.format(head=pr_head),
    ]
    return "\n".join(lines)


def failed_jobs(repo, run_id):
    """(the first MAX_JOBS failed jobs of the run, each {name, url, steps, errors, truncated},
    and the run's total number of failed jobs)."""
    jobs = []
    pages = gh_json(["api", "--paginate", "--slurp",
                     f"repos/{repo}/actions/runs/{run_id}/jobs?per_page=100"]) or []
    for page in pages:
        jobs += page.get("jobs") or []
    failed = [j for j in jobs if j.get("conclusion") == "failure"]
    out = []
    for j in failed[:MAX_JOBS]:
        steps = [s["name"] for s in j.get("steps") or [] if s.get("conclusion") == "failure"]
        try:
            errors, truncated = extract_errors(
                gh(["api", f"repos/{repo}/actions/jobs/{j['id']}/logs"]))
        except RuntimeError as e:
            print(f"::warning::could not read the log of job {j['id']}: {e}", file=sys.stderr)
            errors, truncated = [], False
        out.append({"name": j.get("name") or str(j["id"]), "url": j.get("html_url") or "",
                    "steps": steps, "errors": errors, "truncated": truncated})
    return out, len(failed)


def group_subjects(repo, base_sha, group_sha):
    """The subjects of the group's squash commits, in queue order."""
    cmp = gh_json(["api", f"repos/{repo}/compare/{base_sha}...{group_sha}"]) or {}
    return merge_group_prs.commit_subjects(cmp)


def upsert_comment(repo, pr, head, body, token):
    """Edit this head's report if one exists, else create it: the marker-keyed upsert is
    scripts/gh_utils.py's, keyed here by the PR head."""
    action, _ = upsert_marked_comment(repo, pr, re.compile(re.escape(MARKER.format(head=head))),
                                      body, token)
    return action


def main():
    repo, run_id = os.environ["REPO"], os.environ["RUN_ID"]
    parsed = parse_branch(os.environ.get("HEAD_BRANCH", ""))
    if not parsed:
        print(f"not a merge-queue branch: {os.environ.get('HEAD_BRANCH')!r}; nothing to report")
        return 0
    base_branch, pr, base_sha = parsed
    group_sha = os.environ["HEAD_SHA"]
    pr_info = gh_json(["api", f"repos/{repo}/pulls/{pr}"]) or {}
    if pr_info.get("state") != "open":
        print(f"#{pr} is not open; nothing to report")
        return 0
    pr_head = pr_info["head"]["sha"]
    try:
        others = group_prs(group_subjects(repo, base_sha, group_sha), pr)
    except RuntimeError as e:
        print(f"::warning::could not list the group's commits: {e}", file=sys.stderr)
        others = []
    jobs, total_failed = failed_jobs(repo, run_id)
    body = render(pr_head=pr_head, run_url=f"https://github.com/{repo}/actions/runs/{run_id}",
                  base_branch=base_branch, base_sha=base_sha, group_sha=group_sha,
                  jobs=jobs, others=others, total_failed=total_failed)
    if os.environ.get("DRY_RUN") == "1":
        print(body)
        return 0
    token = os.environ.get("COMMENT_TOKEN") or None
    print(f"#{pr}: report {upsert_comment(repo, pr, pr_head, body, token)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
