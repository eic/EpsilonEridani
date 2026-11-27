#!/usr/bin/env python3
"""Shared `gh` plumbing for the scripts that post one marked PR comment each.

`gh` and `gh_json` run one `gh` call, reading the token from the environment (`GH_TOKEN`)
unless one is passed. `upsert_marked_comment` is the one copy of the marker-keyed comment
upsert: `scripts/structure_nudge.py` and `scripts/merge_queue_report.py` each keep at most
one comment per PR, recognized by a hidden HTML marker in its body, and edit that comment
in place instead of posting again. The marker is the caller's — a fixed string (structure
nudge) or one carrying the PR head SHA, so a repeated failure of the same head edits the
same comment (merge-queue report) — passed as `marker_re`, which makes the head keying a
parameter of one mechanism rather than a second mechanism.
"""

from __future__ import annotations

import json
import os
import subprocess


def gh(args, token=None, stdin=None):
    """Run one `gh` command and return its stdout; `token` overrides GH_TOKEN when given."""
    env = dict(os.environ)
    if token:
        env["GH_TOKEN"] = token
    r = subprocess.run(["gh", *args], capture_output=True, text=True, env=env, input=stdin,
                       timeout=120)
    if r.returncode != 0:
        raise RuntimeError(f"gh {' '.join(args[:2])} failed: {r.stderr.strip()[:500]}")
    return r.stdout


def gh_json(args, token=None):
    """`gh` with the output parsed as JSON (None when the call printed nothing)."""
    out = gh(args, token)
    return json.loads(out) if out.strip() else None


def upsert_marked_comment(repo, pr, marker_re, body, token=None):
    """Edit the PR comment whose body matches `marker_re`, else post `body` as a new comment.

    Returns ("edited", comment id) when a matching comment was edited, ("created", None) when
    `body` was posted.
    """
    comments = gh_json(["api", "--paginate", "--slurp",
                        f"repos/{repo}/issues/{pr}/comments?per_page=100"], token) or []
    for c in (c for page in comments for c in page):
        if marker_re.search(c.get("body") or ""):
            gh(["api", "-X", "PATCH", f"repos/{repo}/issues/comments/{c['id']}",
                "--input", "-"], token, stdin=json.dumps({"body": body}))
            return "edited", c["id"]
    gh(["api", "-X", "POST", f"repos/{repo}/issues/{pr}/comments", "--input", "-"], token,
        stdin=json.dumps({"body": body}))
    return "created", None
