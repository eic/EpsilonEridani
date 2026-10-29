# PR status and merge readiness

GitHub lifecycle labels and the pipeline-health report use
[`readiness.py`](readiness.py), which calls the **same pinned EpsilonEridaniReview
merge gate as Auto-merge**. The label is a presentation of that decision, not an
independent approximation based on a green build and a scoreboard heading.

The adapter reads all comments and current commit statuses through GraphQL, fetches
the diff for otherwise approved PRs, and checks
that the PR's head, base, lifecycle and hold state have not changed before
reporting readiness. The gate selects the newest completed current-head review,
requires every configured rubric, handles legacy scoreboard tables and live
review markers, and enforces build, scope, allowed paths and pin-validation rules.
Drafts, held PRs and stacked bases are reported separately.

| Label | Meaning |
| --- | --- |
| `awaiting-CI` | A required check is missing or pending |
| `ci-failed` | The build failed |
| `merge-check-failed` | A scope or pin-validation check failed |
| `awaiting-review` | Current-head reviews are absent or incomplete |
| `review-in-progress` | A live review delays enqueueing |
| `awaiting-author` | A current review requests changes or the PR conflicts |
| `needs-human-review` | Approved changes include human-owned files |
| `awaiting-dependency` | The PR targets a stacked branch rather than main |
| `on-hold` | The PR is a draft or has an explicit hold label |
| `ready-to-merge` | All per-PR automated merge prerequisites pass |

`on-hold` is a generated status. Use an explicit `hold` or `keep` label to hold a
PR; setting `on-hold` manually does not hold it. Failed scope/pin checks do not
receive `ci-failed`, preserving the existing failed-build housekeeping rules.

Queue membership and a Mathlib reservation **do not change** `ready-to-merge`.
The health report separately shows verified eligible PRs, which are queued,
which are not, and any reservation holder. It rechecks PRs instead of trusting
labels, reports label disagreements, and preserves failed reads as unknown.
Historical stage rates still describe label transitions; current verified depths
and recorded label depths are separate fields. A snapshot without a readiness
audit cannot establish a merge bottleneck from its ready-label count.

[`labels.py`](labels.py) is the sole label writer. It sets one lifecycle label
for an open PR and removes them on close. `pr-labels.yml` handles PR changes,
review-comment creation/edit/deletion, and completed builds. Its scheduled sweep
reconciles all open PRs, including stale ready labels. Dispatch it with `pr=all`
for a policy migration/backfill or with a PR number for a single reconciliation.
The backfill updates label descriptions once, continues after individual errors,
and reports failures. A rate limit stops the remaining pass visibly.

The workflows check out the exact policy revision used by Auto-merge, without
persisting credentials. The workflow-pin tests require labels, the health report,
and their tests to use that same revision. For local commands, check out that
revision of EpsilonEridaniReview and set:

```sh
export TAUCETI_REVIEW_RUNNER=/path/to/EpsilonEridaniReview/runner
python3 scripts/pr_status/labels.py reconcile 123
python3 scripts/pipeline_health.py --data snapshot.json --verify-readiness
```

Without `--verify-readiness`, `--data` remains an offline replay and uses the
readiness audit stored in the snapshot, if present. A live health report always
performs the audit. Use `--dump-data` to save the evidence for offline replay.

[`core.py`](core.py) supplies GitHub-reading helpers and the separate build/review
signals used for Zulip reactions. A green build/review reaction is not a claim
that a PR passes all merge prerequisites. Destructive housekeeping continues to
use its stricter OWNER/MEMBER/COLLABORATOR comment policy.

## Mattermost reactions

[`mattermost.py`](mattermost.py) finds-or-creates the PR's announcement post in the **ε Eri**
Mattermost channel (identified by a hidden `[PR-###-ANNOUNCEMENT]` tag) and reconciles two
independent reaction groups on it from `core.derive`:

| Group | State | Emoji |
| --- | --- | --- |
| **CI (build)** | waiting / running | 🟡 `large_yellow_circle` |
| | passed | ✅ `white_check_mark` |
| | failed | ❌ `x` |
| **Review / lifecycle** | review in progress | 👀 `eyes` |
| | waiting for review | *(none)* |
| | changes requested / blocked | ✍️ `writing_hand` |
| | all review done, all green | ✅ `white_check_mark` |
| | merged | 🎉 `tada` |
| | closed, not merged | 📕 `closed_book` |

Only the bot's *own* reactions are touched (they are selected by the bot's user id), so a human
reacting on a status post never confuses reconciliation.

Four workflows drive it:

- [`mattermost-pr.yml`](../../.github/workflows/mattermost-pr.yml): on PR
  `opened`/`reopened`/`closed` and label changes. Creates the post, keeps its roadmap
  metadata current, and owns the merged/closed ending.
- [`mattermost-pr-status.yml`](../../.github/workflows/mattermost-pr-status.yml): on CI and
  review status changes. Refreshes the CI and review groups.
- [`mattermost-healthcheck.yml`](../../.github/workflows/mattermost-healthcheck.yml): a
  schedule (every six hours) that runs `check` to probe the credentials, so a broken token
  is caught even during quiet periods with no PR activity.
- [`mattermost-pr-backfill.yml`](../../.github/workflows/mattermost-pr-backfill.yml): manual;
  see [Backfill](#backfill-run-locally).

[`zulip.py`](zulip.py) is the same sink for a Zulip channel and topic. Epsilon Eridani has no
Zulip, so no workflow runs it for PR reactions; it stays because `stuck_alerts.py` and
`toolchain_tags.py` reuse its client and helpers, and its unit tests still run in CI.

## Merge conflicts

A PR becomes conflicted because **its base moved**, not because its author did
anything, which makes it the one transition nothing else here can see. Every other
trigger is scoped to the PR (`pull_request_target`, a `pr-build` / `Review`
`workflow_run`, an `issue_comment`), and the base moving fires none of them.
Before [`merge-conflicts.yml`](../../.github/workflows/merge-conflicts.yml) a PR
could pick up a conflict and *nothing anywhere said so* — no label, no comment, no
alert. `stuck_alerts.py` deliberately skips a conflicting PR (it is not being
wrongly withheld by the merge path) and `housekeeping.py` only retires PRs that
are blocking under review, so a conflicted-but-approved PR was reaped by nothing
either. It rotted silently.

[`conflicts.py`](conflicts.py) runs every fifteen minutes: one GraphQL query reads
the whole open queue, `merge-conflict` goes on a PR that has stopped merging and
comes off when it merges again, and the author is told once per episode. The label
is provisioned on first use, like the status labels.

Two properties are why this is a couple of hundred lines rather than a package.

**The label is orthogonal to the status labels.** It is deliberately *not* part of
the mutually-exclusive set [`labels.py`](labels.py) maintains, and nothing else
reads or writes it. A PR can be awaiting review *and* conflicting, and saying both
is more useful than having one hide the other; keeping them separate also means
conflict state never enters `core.derive`, never has to win a precedence argument
against CI or review state, and cannot interfere with what a review harness reads.

**The label is also the state.** Whether an episode is open is just "is the label
on the PR", so there is no marker to parse and no way to fail to recognise our own
bookkeeping — a wrong label self-heals on the next run. It also makes the problem
measurable without writing anything extra, since GitHub timestamps label changes:

```bash
gh api --paginate "/repos/eic/EpsilonEridani/issues/N/timeline?per_page=100" \
  --jq '.[] | select(.label.name == "merge-conflict") | "\(.event) \(.created_at) \(.actor.login)"'
```

Read those as **observed label intervals**, not exact conflict durations: the
boundaries are quantised by the fifteen-minute poll and by GitHub's scheduling, a
conflict that arises and clears between two runs is never seen at all, and a PR
closed while labelled has no closing event. The actor distinguishes the bot's own
transitions from a human's.

Two ordering decisions carry the weight:

- **The comment is posted before the label.** The label is what suppresses a
  repeat, so writing it first would mean a comment that then failed was never
  retried — the notice lost silently, which is the one failure this must not have.
  This way the risk is a duplicate comment instead, which is merely annoying.
- **UNKNOWN is skipped per PR, never per run.** GitHub computes `mergeable`
  lazily, so a read just after the base moved answers UNKNOWN and only schedules
  the merge. Those are re-read a few times; whatever stays unknown is left exactly
  as it is, neither labelled nor cleared, while every PR whose state we do know is
  still processed. This is why we do not use
  [`eps1lon/actions-label-merge-conflict`](https://github.com/eps1lon/actions-label-merge-conflict),
  which mathlib4 uses for the same job: on UNKNOWN it returns from the middle of
  its loop, and once its retries are spent returns an empty result, abandoning
  that page of PRs and every later one. A PR whose head has diverged from its
  branch tip sits at `mergeable: null` indefinitely — precisely what
  `stuck_alerts.py`'s `diverged-head` detector exists to catch — so one such PR
  could stop every other conflict being labelled.

A PR carrying a hold label (`keep`/`hold`/`wip`/`human`/`do-not-close`/`blocked`,
matching `stuck_alerts.py`) is left entirely alone rather than labelled-but-silent:
the label means "the author has been told", so labelling without commenting would
leave the conflict silent for good once the hold came off. Only open PRs are read,
so a PR closed while labelled keeps the label — accurate, but it means that
episode has no closing event in the timeline.

Note that labelling and commenting both bump the PR's `updatedAt`, which
`housekeeping.py` treats as freshness — so a conflict episode resets that PR's
seven-day stale-close clock. That is the intended trade: a PR that just learned it
conflicts should get its week to act on it.

## Stuck-automation alerts (Mattermost "ε Eri")

[`stuck_alerts.py`](stuck_alerts.py), driven by
[`stuck-alerts.yml`](../../.github/workflows/stuck-alerts.yml) hourly, reports whenever
Epsilon Eridani's own automation wedges and cannot recover on its own. When at least one alert
is active it posts one "🚨 Active Stuck Alerts" message listing them to the **ε Eri** Mattermost
channel; when none is, it posts nothing. (Its Zulip path, one idempotent message per alert in a
"Stuck PRs" topic edited to ✅ when the situation clears, runs only when `ZULIP_*` secrets are
set; Epsilon Eridani sets none, so it logs a warning and is skipped.)

This is an **emergency channel, not a help queue.** Every alert means a piece of
infrastructure needs fixing so the wedge cannot recur, not that a human should
hand-hold one PR. It fires on: a red, stale last-known-good bump PR; a mathlib pin
that has stopped advancing; an in-scope, fully-green PR the merge path never
merged; an open `Review stuck: PR #…` issue; a scheduled workflow that is disabled
or overdue; `main` gone red; and a long-open mathlib-incompatibility issue. It
**deliberately does not** alert on normal backlog (a PR awaiting its first review
verdict, changes-requested nobody addressed, open roadmap issues); the module
docstring lists the full catalogue and the reasoning.

Run `python3 scripts/pr_status/stuck_alerts.py --dry-run` (with `gh` authenticated)
to print the alerts it would post without posting anywhere. A failed Mattermost post makes
the run red; a Zulip configuration problem only warns.

## One-time setup

1. **Create a dedicated Mattermost bot account** and add it to the **ε Eri** channel: a bot
   can only post and react in channels it belongs to.
2. **Add repository secrets** on `eic/EpsilonEridani`:
   - `MATTERMOST_BOT_TOKEN`: the bot's access token
   - `MATTERMOST_CHANNEL_ID`: the channel's id (not its name)

   and the repository **variable** `MATTERMOST_URL`: the server's base URL. Then confirm:

   ```bash
   export MATTERMOST_URL=... MATTERMOST_BOT_TOKEN=... MATTERMOST_CHANNEL_ID=...
   python3 scripts/pr_status/mattermost.py check   # exits 0 and prints OK when healthy
   ```

The Zulip sink, unused here, takes `ZULIP_API_KEY` and `ZULIP_EMAIL` (the site is hard-coded to
`https://leanprover.zulipchat.com` in the workflows). If it is ever configured, set the key with
`gh secret set ZULIP_API_KEY --body "$KEY"` rather than piping `echo`, so no trailing newline
rides into the auth header and gets rejected as `Malformed API key`.

The labels need no secret: `pr-labels.yml` uses the same GitHub App
(`APP_ID` / `APP_PRIVATE_KEY`) already configured for the roadmap and merge
workflows, scoped to this repo, and provisions lifecycle labels on first use.

## Failure modes (Mattermost)

The Mattermost integration is quiet about cosmetic problems and loud about real ones,
because the two are easy to confuse from the outside:

- A **transient** hiccup (one failed reaction, a network blip, a PR with no post
  yet) is cosmetic and self-heals on the next reconcile. The script logs it and
  exits 0, so the workflow run stays green.
- A **configuration** break (`MATTERMOST_URL` or `MATTERMOST_BOT_TOKEN` unset, a rejected
  token, or the bot unable to access the channel) breaks *every* PR and will not fix itself.
  The script raises a config error and exits non-zero, so the workflow run goes **red**; the
  six-hourly healthcheck surfaces it even when no PR is active.

When a run is red, re-set the secrets, then confirm with `mattermost.py check` as above.

## Backfill (run locally)

To seed labels and/or Mattermost posts for PRs that predate this integration, run
the reconcilers over the open PRs with `gh` authenticated:

```bash
# Labels: needs only an authenticated gh with issues:write.
python3 scripts/pr_status/labels.py reconcile-all

# Mattermost: needs the status bot credentials exported. This paginates the complete
# PR history in one low-request stream and edits existing posts in place.
export MATTERMOST_URL=... MATTERMOST_BOT_TOKEN=... MATTERMOST_CHANNEL_ID=...
gh api --paginate \
  'repos/eic/EpsilonEridani/pulls?state=all&sort=created&direction=asc&per_page=100' \
  --jq '.[] | {
    number,
    state,
    merged: (.merged_at != null),
    head: .head.sha,
    title,
    author: .user.login,
    roadmaps: [.labels[].name | select(startswith("roadmap/"))]
  }' | python3 scripts/pr_status/mattermost.py backfill --dry-run --strict

# After reviewing the dry-run summary, omit --dry-run to apply it.
```

Re-running either is safe: it converges to current GitHub state and changes
nothing else. The `Mattermost PR backfill` workflow runs the same full-history post
update with the repository's status-bot secrets, so old posts can be migrated
without copying credentials locally. It takes a `dry_run` input, continues past
individual failures and reports them together (`--strict` turns those into a failed run).
`pr-labels.yml` also has a `workflow_dispatch` that reconciles one PR or all open PRs from
the Actions tab.

## Unit tests

```bash
cd scripts/pr_status
python3 -m unittest test_pr_labels test_readiness test_zulip test_stuck_alerts
```

`test_pr_labels` covers the derivation (`core.review_state`, `core.inprogress_from`,
`core.derive`), metadata plumbing, and label reconciliation. `test_readiness`
runs the pinned merge gate on current/stale/incomplete reviews, live markers,
human paths, CI and pin guards, and head-move races. It needs the pinned engine
checkout described above. `test_zulip` covers review reactions, PR post
rendering, legacy-message rewriting, batch continuation, dry runs, and rate-limit
retry. All GitHub and Zulip reads and writes are stubbed, so these need no
network.
