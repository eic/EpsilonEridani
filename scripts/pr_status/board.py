#!/usr/bin/env python3
"""Keep a GitHub Projects board of the open PRs, ranked by how close each is to passing every rubric.

The lifecycle labels (labels.py) say whose court a PR is in; the Mattermost reactions say whether
the build and the review are green. Neither answers the question a maintainer deciding where to
spend the next hour actually asks: *which PRs are nearly through review, and what is left on each?*
That is in the scoreboard comments -- one state per rubric, hidden in the `epsiloneridani-meta`
block -- but reading ten rubric states off forty PRs by hand is the work this board does instead.

Each open PR is one item on a Projects (v2) board. Its **Status** column is a band of distance
from merge, so the board reads left to right as "closest first":

    All rubrics green  >  1-2 to go  >  3-5 to go  >  6+ to go  >  Blocked  >
    No review at head  >  Waiting on CI  >  On hold

and its fields carry the evidence the band was read from, so a list view sorted by
**Rubrics green** is the same ranking as a flat score:

    Rubrics green   how many of the rubrics approve the CURRENT head (empty: no review at head)
    Prior green     for a PR whose newest review is of an earlier head: how many rubrics approved
                    then, so the "No review at head" column still ranks by how far each had got
    Not green       the rubrics still to satisfy, each with its state (changes / BLOCK / stale /
                    not run / error) -- what is left to do on this PR
    Lifecycle       the readiness category labels.py would apply (whose court it is)
    Roadmap         the PR's roadmap/<Area> label(s)
    Review head     which commit the newest completed review judged, and whether that is the
                    current head; a superseded review shows its score so a PR with "9/10 green,
                    one push ago" is not confused with one never reviewed
    Reviewed        the date of that review

The rubric states come from the SAME scoreboard selection the merge gate uses (the newest completed
scoreboard naming the current head and its merge base; readiness.py), so the board can never show a
PR as greener than Auto-merge would judge it. A head-matching scoreboard that reviewed a different
merge base (the PR was retargeted or its base rewritten) is shown as superseded, not current.

Writes are confined to the project: items are added for open PRs, their fields set when they
differ from what is already there (an unchanged board costs no mutations), and the item of a PR
that closed or merged is archived (unarchived if it reopens). Nothing here comments, labels, or
touches the PR itself, and no PR code is executed; PR contents are API data.

    board.py sync                  # every open PR (the hourly backstop, and the backfill)
    board.py sync --pr 183         # one PR, after an event about it
    board.py sync --dry-run        # plan and print the ranking, mutate nothing

Env: GH_TOKEN (App token with organization projects write, pull-requests and issues read),
GH_REPO (owner/name), PR_BOARD_PROJECT (the project's number under PR_BOARD_OWNER, default the
repository owner), TAUCETI_REVIEW_RUNNER (the pinned engine, as for labels.py). Without
PR_BOARD_PROJECT the ranking is still computed and printed, so the board can be previewed (and the
job summary read) before the project exists. The ranking is always written to GITHUB_STEP_SUMMARY
when that is set.
"""

import argparse
import datetime
import json
import os
import subprocess
import sys
import time

import core
import labels
import readiness

REPO = core.REPO

# ----- the board's vocabulary --------------------------------------------------------------------

# Status options, in board order (closest to merge first). Projects allows these option colours:
# GRAY, BLUE, GREEN, YELLOW, ORANGE, RED, PINK, PURPLE.
COLUMNS = [
    ("All rubrics green", "GREEN", "Every rubric approves the current head; see Lifecycle for the merge gate"),
    ("1\u20132 to go", "YELLOW", "8 or 9 of the rubrics approve the current head; none blocked"),
    ("3\u20135 to go", "ORANGE", "5 to 7 of the rubrics approve the current head; none blocked"),
    ("6+ to go", "RED", "At most 4 of the rubrics approve the current head; none blocked"),
    ("Blocked", "PURPLE", "An integrity rubric blocked the current head; it needs rework, not polish"),
    ("No review at head", "BLUE", "The build is green but no completed review names the current head"),
    ("Waiting on CI", "GRAY", "The build has not passed on the current head, so review cannot run"),
    ("On hold", "GRAY", "A draft, held by a keep/hold/wip/human/do-not-close label, or stacked on another branch"),
]
COLUMN_ORDER = {name: index for index, (name, _, _) in enumerate(COLUMNS)}

# Lifecycle options mirror labels.LABELS (same names, same descriptions) so the board and the PR
# list agree; only the colours differ, since Projects has a fixed palette.
LIFECYCLE_COLORS = {
    "awaiting-CI": "YELLOW", "awaiting-review": "BLUE", "review-in-progress": "PURPLE",
    "ci-failed": "RED", "awaiting-author": "PINK", "merge-check-failed": "RED",
    "needs-human-review": "PURPLE", "awaiting-dependency": "GRAY", "on-hold": "GRAY",
    "ready-to-merge": "GREEN",
}
LIFECYCLE_OPTIONS = [(name, LIFECYCLE_COLORS[name], labels.LABELS[name][1]) for name in labels.STATUS_LABELS]

# Field name -> (Projects data type, single-select options or None). "Status" is the built-in
# field every project has; it is never created, only given the options it lacks.
FIELDS = {
    "Status": ("SINGLE_SELECT", COLUMNS),
    "Rubrics green": ("NUMBER", None),
    "Prior green": ("NUMBER", None),
    "Not green": ("TEXT", None),
    "Lifecycle": ("SINGLE_SELECT", LIFECYCLE_OPTIONS),
    "Roadmap": ("TEXT", None),
    "Review head": ("TEXT", None),
    "Reviewed": ("DATE", None),
}

# How a non-green rubric state reads in the "Not green" field.
STATE_WORD = {"blocking_request": "changes", "blocking_block": "BLOCK", "stale": "stale",
              "absent": "not run", "error": "error"}
NOT_GREEN_SEPARATOR = " \u00b7 "

# Bands of the Status column by how many rubrics are green out of the required set.
NEARLY_GREEN_FLOOR = 8   # 8 or 9 of 10 -> "1-2 to go"
HALFWAY_FLOOR = 5        # 5 to 7 of 10 -> "3-5 to go"


def log(msg):
    print(msg, flush=True)


# ----- GraphQL (Projects v2 is GraphQL-only) ------------------------------------------------------

def graphql(query, variables=None):
    """One GraphQL call through `gh`, variables as JSON on stdin so nested inputs (a field value,
    an option list) keep their types. Shares core's rate-limit breaker: a limit established by any
    read in this run refuses every later call instead of waiting again for each one."""
    if time.time() < core._BLOCKED_UNTIL:
        raise core.RateLimited("GitHub calls paused after a rate limit")
    body = json.dumps({"query": query, "variables": variables or {}})
    out = subprocess.run(["gh", "api", "graphql", "--input", "-"], input=body,
                         text=True, capture_output=True)
    try:
        payload = json.loads(out.stdout or "{}")
    except ValueError:
        payload = {}
    errors = payload.get("errors") or []
    if core._rate_limited(out.stderr) or any(e.get("type") == "RATE_LIMITED" for e in errors):
        core._block_for(core.RATE_LIMIT_MAX_WAIT_SECONDS)
        raise core.RateLimited("GitHub rate limited the board sync; retry on the next run")
    if out.returncode or errors or payload.get("data") is None:
        detail = "; ".join(e.get("message", "") for e in errors) or out.stderr.strip()
        raise RuntimeError(f"GraphQL failed: {detail}")
    return payload["data"]


PROJECT_QUERY = """
query($owner: String!, $number: Int!, $cursor: String) {
  OWNER_TYPE(login: $owner) {
    projectV2(number: $number) {
      id title url
      fields(first: 50) {
        nodes {
          ... on ProjectV2FieldCommon { id name dataType }
          ... on ProjectV2SingleSelectField { options { id name color description } }
        }
      }
      items(first: 100, after: $cursor) {
        pageInfo { hasNextPage endCursor }
        nodes {
          id isArchived
          content {
            __typename
            ... on PullRequest { number state repository { nameWithOwner } }
            ... on Issue { number repository { nameWithOwner } }
          }
          fieldValues(first: 20) {
            nodes {
              ... on ProjectV2ItemFieldTextValue { text field { ... on ProjectV2FieldCommon { name } } }
              ... on ProjectV2ItemFieldNumberValue { number field { ... on ProjectV2FieldCommon { name } } }
              ... on ProjectV2ItemFieldDateValue { date field { ... on ProjectV2FieldCommon { name } } }
              ... on ProjectV2ItemFieldSingleSelectValue { name field { ... on ProjectV2FieldCommon { name } } }
            }
          }
        }
      }
    }
  }
}
"""


def load_project(owner, number, owner_type="organization"):
    """The project's id, fields (name -> {id, type, options: name -> id}) and items (one per PR of
    this repository: pr number -> {id, archived, values: field name -> current value}). Items whose
    content is not a pull request of `REPO` are ignored, never touched."""
    query = PROJECT_QUERY.replace("OWNER_TYPE", owner_type)
    fields, items, cursor = {}, {}, None
    project = None
    while True:
        data = graphql(query, {"owner": owner, "number": number, "cursor": cursor})
        node = (data.get(owner_type) or {}).get("projectV2")
        if not node:
            raise RuntimeError(f"No project #{number} under {owner_type} {owner} "
                               "(or the token cannot read it)")
        if project is None:
            project = {"id": node["id"], "title": node["title"], "url": node["url"]}
            for f in node["fields"]["nodes"]:
                if not f or not f.get("name"):
                    continue   # a field type this query does not spell out (iteration, etc.)
                fields[f["name"]] = {
                    "id": f["id"], "type": f["dataType"],
                    "options": {o["name"]: o["id"] for o in (f.get("options") or [])},
                    "option_details": f.get("options") or [],
                }
        for item in node["items"]["nodes"]:
            content = item.get("content") or {}
            if content.get("__typename") != "PullRequest":
                continue
            if (content.get("repository") or {}).get("nameWithOwner", "").lower() != REPO.lower():
                continue
            values = {}
            for v in item["fieldValues"]["nodes"]:
                name = (v.get("field") or {}).get("name")
                if not name:
                    continue
                for key in ("text", "number", "date", "name"):
                    if key in v:
                        values[name] = v[key]
            items[content["number"]] = {"id": item["id"], "archived": bool(item.get("isArchived")),
                                        "values": values}
        page = node["items"]["pageInfo"]
        if not page["hasNextPage"]:
            break
        cursor = page["endCursor"]
    project.update(fields=fields, items=items)
    return project


def ensure_fields(project, dry_run=False):
    """Create the fields the board needs and give each single-select field the options it lacks.

    Options are added, never removed or recoloured: `updateProjectV2Field` replaces the whole option
    list, so the existing options are re-sent as they are (name, colour, description) with the
    missing ones appended. A human-added option therefore survives, and an item parked in it is left
    where it is. Returns the names of fields that could not be made ready (dry run only)."""
    missing = []
    for name, (data_type, options) in FIELDS.items():
        field = project["fields"].get(name)
        if field is None:
            if name == "Status":
                raise RuntimeError("The project has no Status field; it is built in to every project")
            if dry_run:
                log(f"would create field {name!r} ({data_type})")
                missing.append(name)
                continue
            field = create_field(project["id"], name, data_type, options)
            project["fields"][name] = field
            log(f"created field {name!r}")
        if options:
            wanted = [(n, c, d) for n, c, d in options if n not in field["options"]]
            if not wanted:
                continue
            if dry_run:
                log(f"would add options to {name!r}: {', '.join(n for n, _, _ in wanted)}")
                missing.append(name)
                continue
            field["options"] = add_options(field, wanted)
            log(f"added options to {name!r}: {', '.join(n for n, _, _ in wanted)}")
    return missing


def _option_inputs(options):
    return [{"name": n, "color": c, "description": d} for n, c, d in options]


def create_field(project_id, name, data_type, options):
    query = """
mutation($project: ID!, $name: String!, $type: ProjectV2CustomFieldType!,
         $options: [ProjectV2SingleSelectFieldOptionInput!]) {
  createProjectV2Field(input: {projectId: $project, name: $name, dataType: $type,
                               singleSelectOptions: $options}) {
    projectV2Field {
      ... on ProjectV2FieldCommon { id name dataType }
      ... on ProjectV2SingleSelectField { options { id name color description } }
    }
  }
}"""
    variables = {"project": project_id, "name": name, "type": data_type}
    if options:
        variables["options"] = _option_inputs(options)
    node = graphql(query, variables)["createProjectV2Field"]["projectV2Field"]
    return {"id": node["id"], "type": node["dataType"],
            "options": {o["name"]: o["id"] for o in (node.get("options") or [])},
            "option_details": node.get("options") or []}


def add_options(field, wanted):
    """Append `wanted` options to a single-select field, keeping every existing option as it is.
    Returns the new name -> id map."""
    existing = [{"name": o["name"], "color": o.get("color") or "GRAY",
                 "description": o.get("description") or ""} for o in field["option_details"]]
    query = """
mutation($field: ID!, $options: [ProjectV2SingleSelectFieldOptionInput!]!) {
  updateProjectV2Field(input: {fieldId: $field, singleSelectOptions: $options}) {
    projectV2Field { ... on ProjectV2SingleSelectField { options { id name color description } } }
  }
}"""
    node = graphql(query, {"field": field["id"], "options": existing + _option_inputs(wanted)})
    details = node["updateProjectV2Field"]["projectV2Field"]["options"]
    field["option_details"] = details
    return {o["name"]: o["id"] for o in details}


def add_item(project_id, content_id):
    query = """
mutation($project: ID!, $content: ID!) {
  addProjectV2ItemById(input: {projectId: $project, contentId: $content}) { item { id } }
}"""
    return graphql(query, {"project": project_id, "content": content_id})["addProjectV2ItemById"]["item"]["id"]


def set_value(project_id, item_id, field, value):
    """Set one field on one item; `value` None or "" clears it (Projects has no empty text)."""
    if value is None or value == "":
        query = """
mutation($project: ID!, $item: ID!, $field: ID!) {
  clearProjectV2ItemFieldValue(input: {projectId: $project, itemId: $item, fieldId: $field}) {
    projectV2Item { id } } }"""
        graphql(query, {"project": project_id, "item": item_id, "field": field["id"]})
        return
    kind = field["type"]
    if kind == "SINGLE_SELECT":
        payload = {"singleSelectOptionId": field["options"][value]}
    elif kind == "NUMBER":
        payload = {"number": value}
    elif kind == "DATE":
        payload = {"date": value}
    else:
        payload = {"text": value}
    query = """
mutation($project: ID!, $item: ID!, $field: ID!, $value: ProjectV2FieldValue!) {
  updateProjectV2ItemFieldValue(input: {projectId: $project, itemId: $item, fieldId: $field,
                                        value: $value}) { projectV2Item { id } } }"""
    graphql(query, {"project": project_id, "item": item_id, "field": field["id"], "value": payload})


def set_archived(project_id, item_id, archived):
    verb = "archiveProjectV2Item" if archived else "unarchiveProjectV2Item"
    query = ("mutation($project: ID!, $item: ID!) { " + verb +
             "(input: {projectId: $project, itemId: $item}) { item { id } } }")
    graphql(query, {"project": project_id, "item": item_id})


# ----- reading a PR into a card -------------------------------------------------------------------

def open_pulls(repo):
    """Every open PR as {number, node_id, title, draft, labels}; one paginated REST read."""
    out = core.gh_api(
        f"/repos/{repo}/pulls?state=open&per_page=100",
        jq='.[] | {number: .number, node_id: .node_id, title: .title, html_url: .html_url, '
           'labels: [.labels[].name]}',
        paginate=True)
    rows = []
    for line in out.splitlines():
        line = line.strip()
        if line:
            rows.append(json.loads(line))
    return rows


def pull(repo, number):
    """One PR, open or not, in the same shape as `open_pulls` plus `state`."""
    d = json.loads(core.gh_api(f"/repos/{repo}/pulls/{number}"))
    return {"number": d["number"], "node_id": d["node_id"], "title": d.get("title") or "",
            "html_url": d.get("html_url") or "", "state": d["state"],
            "labels": [label["name"] for label in d.get("labels") or []]}


def completed_scoreboards(comments, gate):
    """Every completed scoreboard (any head) as (comment, meta), oldest first by update time."""
    out = []
    for index, comment in enumerate(comments):
        body = comment.get("body") or ""
        if gate.SCOREBOARD_MARKER not in body:
            continue
        meta = gate.parse_meta(body)
        if not meta or meta.get("mode") == "init" or not meta.get("head_sha"):
            continue
        out.append(((comment.get("updated_at") or comment.get("created_at") or meta.get("ts") or "",
                     index), comment, meta))
    out.sort(key=lambda row: row[0])
    return [(comment, meta) for _, comment, meta in out]


def _states(board, meta, gate):
    states = meta.get("states")
    if not isinstance(states, dict) or not states:
        states = gate.states_from_table(board.get("body"))
    return {r: (states.get(r) or "absent") for r in gate.DEFAULT_RUBRICS}


def review_summary(comments, head, merge_base):
    """What the newest completed review says, or None when the PR was never reviewed.

    `current` is true only for the scoreboard the merge gate itself would select: the newest
    completed one naming the current head AND the current merge base (readiness.classify treats a
    head-matching board for another merge base as judging a different diff). Otherwise the newest
    completed scoreboard of any head is summarised as superseded, so the board still shows how far
    the PR had got before the last push."""
    gate = readiness.engine()
    latest = gate.latest_current_scoreboard(comments, head)
    if latest and latest[1].get("mode") != "init" and merge_base \
            and latest[1].get("merge_base_sha") == merge_base:
        board, meta = latest
        return _summary(board, meta, gate, current=True)
    boards = completed_scoreboards(comments, gate)
    if not boards:
        return None
    board, meta = boards[-1]
    return _summary(board, meta, gate, current=False)


def _summary(board, meta, gate, current):
    states = _states(board, meta, gate)
    not_green = {r: s for r, s in states.items() if s != "green"}
    return {"current": current, "head": meta.get("head_sha") or "", "states": states,
            "green": len(states) - len(not_green), "total": len(states), "not_green": not_green,
            "blocked": any(s == "blocking_block" for s in states.values()),
            "ts": meta.get("ts") or board.get("updated_at") or ""}


def column(category, review, build):
    """The Status column for a PR. A current review decides the band; without one, the build
    decides whether review could even run; a hold trumps both."""
    if category in {"on-hold", "awaiting-dependency"}:
        return "On hold"
    if review and review["current"]:
        if review["blocked"]:
            return "Blocked"
        green, total = review["green"], review["total"]
        if green == total:
            return "All rubrics green"
        if green >= NEARLY_GREEN_FLOOR:
            return "1\u20132 to go"
        if green >= HALFWAY_FLOOR:
            return "3\u20135 to go"
        return "6+ to go"
    if (build or "").lower() == "success":
        return "No review at head"
    return "Waiting on CI"


def roadmap_of(label_names):
    return ", ".join(name[len("roadmap/"):] for name in sorted(label_names)
                     if name.startswith("roadmap/"))


def review_head_text(review, head):
    if review is None:
        return "never reviewed"
    short = review["head"][:7] or "?"
    score = f"{review['green']}/{review['total']} green"
    if review["current"]:
        return f"{short} (current head)"
    if review["head"] == head:
        # Same head, but the gate wants a review of the current diff: the base moved under it.
        return f"{short} (current head, older merge base; was {score})"
    return f"{short} (superseded; was {score})"


def review_date(review):
    if review is None or not review["ts"]:
        return None
    try:
        return datetime.datetime.fromisoformat(review["ts"].replace("Z", "+00:00")).date().isoformat()
    except ValueError:
        return None


def not_green_text(review):
    if review is None or not review["current"]:
        return ""
    return NOT_GREEN_SEPARATOR.join(f"{rubric}: {STATE_WORD.get(state, state)}"
                                    for rubric, state in review["not_green"].items())


def card(pr, repo, now=None):
    """Everything the board shows for one open PR, from one evidence fetch."""
    current, comments, statuses = readiness.evidence(pr["number"], repo)
    status = readiness.assess_evidence(current, comments, statuses, repo, now=now)
    review = review_summary(comments, status["head"], status.get("merge_base", ""))
    category = status["category"]
    values = {
        "Status": column(category, review, statuses.get("build", "")),
        "Rubrics green": review["green"] if review and review["current"] else None,
        "Prior green": review["green"] if review and not review["current"] else None,
        "Not green": not_green_text(review),
        "Lifecycle": category,
        "Roadmap": roadmap_of(pr.get("labels") or []),
        "Review head": review_head_text(review, status["head"]),
        "Reviewed": review_date(review),
    }
    return {"number": pr["number"], "node_id": pr["node_id"], "title": pr.get("title") or "",
            "url": pr.get("html_url") or "", "head": status["head"], "values": values,
            "reason": status["reason"]}


# ----- planning and applying ---------------------------------------------------------------------

def _same(field_type, have, want):
    if want is None or want == "":
        return have in (None, "")
    if field_type == "NUMBER":
        try:
            return have is not None and float(have) == float(want)
        except (TypeError, ValueError):
            return False
    return have == want


def changes(project, item, values):
    """The (field name, value) pairs whose stored value differs from `values`."""
    out = []
    for name, want in values.items():
        field = project["fields"].get(name)
        if field is None:
            continue   # dry run with a field not yet created
        if field["type"] == "SINGLE_SELECT" and want is not None and want not in field["options"]:
            continue   # option not yet created (dry run)
        have = (item or {}).get("values", {}).get(name)
        if not _same(field["type"], have, want):
            out.append((name, want))
    return out


def apply_card(project, a_card, dry_run=False):
    """Make the project's item for this PR match the card; returns the number of mutations."""
    number = a_card["number"]
    item = project["items"].get(number)
    mutations = 0
    if item is None:
        if dry_run:
            log(f"#{number}: would add to the board")
            item = {"id": None, "archived": False, "values": {}}
        else:
            item = {"id": add_item(project["id"], a_card["node_id"]), "archived": False, "values": {}}
            project["items"][number] = item
            log(f"#{number}: added to the board")
        mutations += 1
    elif item["archived"]:
        if not dry_run:
            set_archived(project["id"], item["id"], False)
        item["archived"] = False
        log(f"#{number}: {'would unarchive' if dry_run else 'unarchived'} (reopened)")
        mutations += 1
    for name, want in changes(project, item, a_card["values"]):
        if not dry_run:
            set_value(project["id"], item["id"], project["fields"][name], want)
        item["values"][name] = want
        mutations += 1
        log(f"#{number}: {'would set' if dry_run else 'set'} {name} = {want!r}")
    return mutations


def archive_closed(project, open_numbers, dry_run=False):
    """Archive the item of every PR that is no longer open. Returns how many."""
    count = 0
    for number, item in sorted(project["items"].items()):
        if number in open_numbers or item["archived"]:
            continue
        if not dry_run:
            set_archived(project["id"], item["id"], True)
        item["archived"] = True
        log(f"#{number}: {'would archive' if dry_run else 'archived'} (closed)")
        count += 1
    return count


# ----- the ranking as text ------------------------------------------------------------------------

def sort_key(a_card):
    values = a_card["values"]
    green = values.get("Rubrics green")
    prior = values.get("Prior green")
    return (COLUMN_ORDER.get(values["Status"], len(COLUMNS)),
            -(green if green is not None else -1), -(prior if prior is not None else -1),
            a_card["number"])


def render_markdown(cards, failures=(), project=None):
    """The ranking as a Markdown table, closest to merge first."""
    lines = []
    title = "PR review board"
    if project:
        title += f" \u2014 [{project['title']}]({project['url']})"
    lines.append(f"## {title}")
    lines.append("")
    lines.append("| PR | Status | Green | Not green | Lifecycle | Roadmap | Review head |")
    lines.append("|---|---|---|---|---|---|---|")
    total = len(readiness.engine().DEFAULT_RUBRICS)
    for a_card in sorted(cards, key=sort_key):
        v = a_card["values"]
        green = "" if v["Rubrics green"] is None else f"{v['Rubrics green']}/{total}"
        link = f"[#{a_card['number']}]({a_card['url']})" if a_card["url"] else f"#{a_card['number']}"
        lines.append(f"| {link} {_cell(a_card['title'])} | {v['Status']} | {green} | "
                     f"{_cell(v['Not green'])} | {v['Lifecycle'] or ''} | {_cell(v['Roadmap'])} | "
                     f"{_cell(v['Review head'])} |")
    if failures:
        lines.append("")
        lines.append("Not assessed this run:")
        for number, reason in failures:
            lines.append(f"- #{number}: {_cell(reason)}")
    return "\n".join(lines) + "\n"


def _cell(text):
    return str(text or "").replace("|", "\\|").replace("\n", " ")


def write_summary(markdown):
    path = os.environ.get("GITHUB_STEP_SUMMARY")
    if path:
        with open(path, "a") as handle:
            handle.write(markdown)


# ----- entry point --------------------------------------------------------------------------------

def sync(repo, project_number, owner, owner_type, pr=None, dry_run=False, now=None):
    readiness.engine()   # fail once, before any write, if the pinned policy is missing
    project = None
    if project_number:
        project = load_project(owner, project_number, owner_type)
        ensure_fields(project, dry_run=dry_run)
    else:
        log("PR_BOARD_PROJECT is not set: computing the ranking without a board to write to")

    if pr is None:
        pulls = open_pulls(repo)
    else:
        one = pull(repo, pr)
        pulls = [one] if one["state"] == "open" else []
    open_numbers = {p["number"] for p in pulls}

    cards, failures, mutations = [], [], 0
    for p in pulls:
        try:
            a_card = card(p, repo, now=now)
        except core.RateLimited as exc:
            failures.append((p["number"], str(exc)))
            log(f"stopping: {exc}")
            break
        except (RuntimeError, subprocess.CalledProcessError, KeyError, ValueError) as exc:
            failures.append((p["number"], str(exc)))
            log(f"#{p['number']}: not assessed: {exc}")
            continue
        cards.append(a_card)
        if project is not None:
            mutations += apply_card(project, a_card, dry_run=dry_run)

    if project is not None:
        if pr is None:
            mutations += archive_closed(project, open_numbers, dry_run=dry_run)
        elif not pulls:
            mutations += archive_closed(project, set(project["items"]) - {pr}, dry_run=dry_run)

    markdown = render_markdown(cards, failures, project)
    print(markdown)
    write_summary(markdown)
    log(f"{len(cards)} PRs ranked, {len(failures)} not assessed, "
        f"{mutations} {'planned' if dry_run else 'applied'} board changes")
    return failures


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n", 1)[0])
    sub = ap.add_subparsers(dest="command", required=True)
    s = sub.add_parser("sync", help="bring the board in line with GitHub")
    s.add_argument("--pr", type=int, default=None, help="one PR number instead of every open PR")
    s.add_argument("--dry-run", action="store_true", help="plan and print, mutate nothing")
    s.add_argument("--project", type=int, default=None,
                   help="project number (default: PR_BOARD_PROJECT)")
    s.add_argument("--owner", default=None,
                   help="project owner login (default: PR_BOARD_OWNER, else the repository owner)")
    s.add_argument("--owner-type", choices=("organization", "user"), default=None,
                   help="whether the owner is an organization or a user (default: PR_BOARD_OWNER_TYPE, else organization)")
    a = ap.parse_args(argv)

    env_project = os.environ.get("PR_BOARD_PROJECT", "").strip()
    project_number = a.project if a.project is not None else (int(env_project) if env_project else None)
    owner = a.owner or os.environ.get("PR_BOARD_OWNER") or REPO.split("/", 1)[0]
    owner_type = a.owner_type or os.environ.get("PR_BOARD_OWNER_TYPE") or "organization"
    dry_run = a.dry_run or os.environ.get("DRY_RUN") == "1"
    failures = sync(REPO, project_number, owner, owner_type, pr=a.pr, dry_run=dry_run)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
