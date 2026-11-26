#!/usr/bin/env python3
"""The squash-title convention a merge group's PRs are read through.

Every PR lands on `main` as one squashed commit whose subject (the first line of its commit
message) ends with its number: `... (#N)`. Two scripts read a merge group's PRs out of that
convention, and both go through this module so it cannot drift between them:

* `scripts/lint-scope.sh`, which decides what the environment lint covers, calls the CLI
  below with the `repos/$REPO/compare/$BASE...$HEAD` response on stdin;
* `scripts/merge_queue_report.py`, which names the other PRs of a failed group, imports
  `commit_subjects` and `pr_numbers`.

CLI: read one compare response on stdin and print one PR number per commit, in order. Exit
1 when a subject carries no number or a number repeats — the caller then cannot tell which
PRs the group holds, and lint-scope.sh fails closed (lints the whole library) on that.
"""

from __future__ import annotations

import json
import re
import sys

# The subject of a squash-landed PR ends with its number: `... (#N)`.
SQUASH_PR_RE = re.compile(r"\(#([0-9]+)\)\s*$")


def commit_subjects(compare):
    """The subjects (first lines of the commit messages) of a compare response, in order."""
    return [(c.get("commit") or {}).get("message", "").split("\n", 1)[0]
            for c in compare.get("commits") or []]


def pr_numbers(subjects):
    """The PR number of each subject, in order; None where the subject carries none."""
    out = []
    for s in subjects:
        m = SQUASH_PR_RE.search(s or "")
        out.append(int(m[1]) if m else None)
    return out


def main():
    numbers = pr_numbers(commit_subjects(json.load(sys.stdin)))
    if None in numbers or len(set(numbers)) != len(numbers):
        print("not every commit subject carries a unique `(#N)` PR number", file=sys.stderr)
        return 1
    print("\n".join(str(n) for n in numbers))
    return 0


if __name__ == "__main__":
    sys.exit(main())
