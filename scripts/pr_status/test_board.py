#!/usr/bin/env python3
"""Tests for the review board: the ranking logic against the pinned engine, and the Projects
writes against a fake GraphQL endpoint. No network. Run with:

    TAUCETI_REVIEW_RUNNER=/path/to/EpsilonEridaniReview/runner python3 scripts/pr_status/test_board.py
"""

import json
import os
import sys
import unittest
from unittest.mock import patch

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import board  # noqa: E402
import core  # noqa: E402
import readiness  # noqa: E402

RUBRICS = readiness.engine().DEFAULT_RUBRICS
HEAD = "33e6bc2183ee910af0fb72eaf7f5078c3ed54b40"
OLD_HEAD = "a1b2c3d4e5f60718293a4b5c6d7e8f9012345678"
MERGE_BASE = "ab17c414332350586ed47a36137399ac425457c4"


def scoreboard(states=None, head=HEAD, merge_base=MERGE_BASE, mode="commit",
               updated="2026-11-01T09:00:00Z", ts="2026-11-01T08:57:49Z"):
    if states is None:
        states = {r: "green" for r in RUBRICS}
    meta = {"kind": "scoreboard", "head_sha": head, "merge_base_sha": merge_base, "mode": mode,
            "states": states, "ts": ts}
    return {"body": "<!--epsiloneridani-scoreboard-->\n## AI review\n<!--epsiloneridani-meta:v1 "
                    + json.dumps(meta) + "-->", "updated_at": updated, "created_at": updated}


def states_with(**overrides):
    states = {r: "green" for r in RUBRICS}
    states.update(overrides)
    return states


class ReviewSummary(unittest.TestCase):
    def test_never_reviewed(self):
        self.assertIsNone(board.review_summary([], HEAD, MERGE_BASE))
        self.assertIsNone(board.review_summary([scoreboard(mode="init")], HEAD, MERGE_BASE))

    def test_current_head_counts_green_and_lists_the_rest(self):
        comments = [scoreboard(states_with(reuse="blocking_request", naming="blocking_request",
                                           **{"proof-quality": "absent"}))]
        summary = board.review_summary(comments, HEAD, MERGE_BASE)
        self.assertTrue(summary["current"])
        self.assertEqual(summary["green"], 7)
        self.assertEqual(summary["total"], 10)
        self.assertEqual(summary["not_green"], {"reuse": "blocking_request",
                                                "naming": "blocking_request",
                                                "proof-quality": "absent"})
        self.assertFalse(summary["blocked"])
        self.assertEqual(summary["ts"], "2026-11-01T08:57:49Z")

    def test_block_is_flagged(self):
        summary = board.review_summary([scoreboard(states_with(scope="blocking_block"))], HEAD, MERGE_BASE)
        self.assertTrue(summary["blocked"])
        self.assertEqual(summary["green"], 9)

    def test_review_of_an_older_head_is_superseded(self):
        comments = [scoreboard(states_with(reuse="blocking_request"), head=OLD_HEAD)]
        summary = board.review_summary(comments, HEAD, MERGE_BASE)
        self.assertFalse(summary["current"])
        self.assertEqual(summary["head"], OLD_HEAD)
        self.assertEqual(summary["green"], 9)

    def test_newest_completed_scoreboard_wins_whatever_the_head(self):
        comments = [scoreboard(states_with(reuse="blocking_request"), head=OLD_HEAD,
                               updated="2026-10-30T00:00:00Z"),
                    scoreboard(states_with(), head=HEAD, updated="2026-10-31T00:00:00Z")]
        self.assertTrue(board.review_summary(comments, HEAD, MERGE_BASE)["current"])
        # A later review of the SAME head supersedes an earlier one of that head.
        comments.append(scoreboard(states_with(naming="blocking_request"), head=HEAD,
                                   updated="2026-11-01T00:00:00Z"))
        self.assertEqual(board.review_summary(comments, HEAD, MERGE_BASE)["green"], 9)

    def test_head_match_with_another_merge_base_is_not_current(self):
        comments = [scoreboard(states_with(), merge_base="deadbeef")]
        summary = board.review_summary(comments, HEAD, MERGE_BASE)
        self.assertFalse(summary["current"])
        self.assertEqual(summary["head"], HEAD)
        self.assertIn("older merge base", board.review_head_text(summary, HEAD))
        self.assertFalse(board.review_summary(comments, HEAD, "")["current"])

    def test_legacy_table_scoreboard_is_read_from_its_rows(self):
        body = ("<!--epsiloneridani-scoreboard-->\n| | rubric | state | judge | summary |\n|---|---|---|---|---|\n"
                + "".join(f"| ✅ | [{r}](u) | approved | `m` | ok |\n" for r in RUBRICS if r != "naming")
                + "| 🟡 | [naming](u) | changes requested | `m` | no |\n"
                + "<!--epsiloneridani-meta:v1 " + json.dumps({"head_sha": HEAD, "merge_base_sha": MERGE_BASE,
                                                            "mode": "commit"}) + "-->")
        summary = board.review_summary([{"body": body, "updated_at": "2026-11-01T00:00:00Z"}],
                                       HEAD, MERGE_BASE)
        self.assertEqual(summary["not_green"], {"naming": "blocking_request"})


class Columns(unittest.TestCase):
    def summary(self, green, blocked=False, current=True):
        return {"current": current, "green": green, "total": 10, "blocked": blocked,
                "head": HEAD, "not_green": {}, "states": {}, "ts": ""}

    def test_bands_by_green_count(self):
        bands = {10: "All rubrics green", 9: "1–2 to go", 8: "1–2 to go",
                 7: "3–5 to go", 5: "3–5 to go", 4: "6+ to go", 0: "6+ to go"}
        for green, expected in bands.items():
            with self.subTest(green=green):
                self.assertEqual(board.column("awaiting-author", self.summary(green), "success"), expected)

    def test_a_block_outranks_the_count(self):
        self.assertEqual(board.column("awaiting-author", self.summary(9, blocked=True), "success"), "Blocked")

    def test_a_current_review_decides_even_when_ci_is_pending(self):
        self.assertEqual(board.column("awaiting-CI", self.summary(10), "pending"), "All rubrics green")

    def test_without_a_current_review_the_build_decides(self):
        self.assertEqual(board.column("awaiting-review", None, "success"), "No review at head")
        self.assertEqual(board.column("awaiting-review", self.summary(9, current=False), "success"),
                         "No review at head")
        self.assertEqual(board.column("awaiting-CI", None, "pending"), "Waiting on CI")
        self.assertEqual(board.column("ci-failed", self.summary(9, current=False), "failure"),
                         "Waiting on CI")
        self.assertEqual(board.column("awaiting-CI", None, ""), "Waiting on CI")

    def test_a_hold_trumps_everything(self):
        self.assertEqual(board.column("on-hold", self.summary(10), "success"), "On hold")
        self.assertEqual(board.column("awaiting-dependency", None, "success"), "On hold")

    def test_every_column_and_lifecycle_is_a_declared_option(self):
        names = {name for name, _, _ in board.COLUMNS}
        for green in range(11):
            for blocked in (False, True):
                self.assertIn(board.column("awaiting-author", self.summary(green, blocked), "success"), names)
        self.assertIn(board.column("awaiting-review", None, "success"), names)
        self.assertIn(board.column("awaiting-CI", None, ""), names)
        self.assertIn(board.column("on-hold", None, ""), names)
        for name, _, _ in board.LIFECYCLE_OPTIONS:
            self.assertIn(name, board.labels.LABELS)


class CardText(unittest.TestCase):
    def test_not_green_lists_each_rubric_with_a_word(self):
        summary = {"current": True, "not_green": {"reuse": "blocking_request", "scope": "blocking_block",
                                                  "naming": "stale", "placement": "absent",
                                                  "documentation": "error"}}
        self.assertEqual(board.not_green_text(summary),
                         "reuse: changes · scope: BLOCK · naming: stale · "
                         "placement: not run · documentation: error")
        self.assertEqual(board.not_green_text(dict(summary, current=False)), "")
        self.assertEqual(board.not_green_text(None), "")

    def test_review_head_and_date(self):
        self.assertEqual(board.review_head_text(None, HEAD), "never reviewed")
        current = {"current": True, "head": HEAD, "green": 7, "total": 10, "ts": "2026-11-01T08:57:49Z"}
        self.assertEqual(board.review_head_text(current, HEAD), "33e6bc2 (current head)")
        self.assertEqual(board.review_date(current), "2026-11-01")
        old = dict(current, current=False, head=OLD_HEAD)
        self.assertEqual(board.review_head_text(old, HEAD), "a1b2c3d (superseded; was 7/10 green)")
        self.assertIsNone(board.review_date(dict(current, ts="")))
        self.assertIsNone(board.review_date(dict(current, ts="yesterday")))

    def test_roadmap_from_labels(self):
        self.assertEqual(board.roadmap_of(["awaiting-review", "roadmap/LightNuclei"]), "LightNuclei")
        self.assertEqual(board.roadmap_of(["roadmap/B", "roadmap/A"]), "A, B")
        self.assertEqual(board.roadmap_of([]), "")


PR = {"number": 199, "node_id": "PR_node", "title": "feat: spin density", "html_url": "https://x/199",
      "labels": ["awaiting-author", "roadmap/LightNuclei"]}
CURRENT = {"number": 199, "state": "open", "draft": False, "head": {"sha": HEAD},
           "base": {"ref": "main", "sha": "tip"}, "labels": [{"name": "roadmap/LightNuclei"}],
           "mergeable": True}
STATUSES = {"build": "success", "scope": "success"}


def assessed(category, head=HEAD, merge_base=MERGE_BASE):
    return {"head": head, "number": 199, "category": category, "reason": "r", "eligible": False,
            "gate": None, "merge_base": merge_base, "checked_at": 0}


class Cards(unittest.TestCase):
    def test_card_reads_evidence_once_and_fills_every_field(self):
        comments = [scoreboard(states_with(reuse="blocking_request", naming="blocking_request"))]
        with patch.object(readiness, "evidence", return_value=(CURRENT, comments, STATUSES)) as ev, \
                patch.object(readiness, "assess_evidence", return_value=assessed("awaiting-author")) as asm:
            a_card = board.card(PR, "eic/EpsilonEridani")
        ev.assert_called_once_with(199, "eic/EpsilonEridani")
        asm.assert_called_once()
        self.assertEqual(a_card["values"], {
            "Status": "1–2 to go", "Rubrics green": 8, "Prior green": None,
            "Not green": "reuse: changes · naming: changes", "Lifecycle": "awaiting-author",
            "Roadmap": "LightNuclei", "Review head": "33e6bc2 (current head)", "Reviewed": "2026-11-01"})
        self.assertEqual((a_card["number"], a_card["node_id"], a_card["head"]), (199, "PR_node", HEAD))

    def test_card_for_an_unreviewed_pr_leaves_the_score_empty(self):
        with patch.object(readiness, "evidence", return_value=(CURRENT, [], STATUSES)), \
                patch.object(readiness, "assess_evidence", return_value=assessed("awaiting-review")):
            values = board.card(PR, "eic/EpsilonEridani")["values"]
        self.assertEqual(values["Status"], "No review at head")
        self.assertIsNone(values["Rubrics green"])
        self.assertIsNone(values["Prior green"])
        self.assertIsNone(values["Reviewed"])
        self.assertEqual(values["Review head"], "never reviewed")

    def test_the_head_the_assessment_settled_on_is_the_one_scored(self):
        """assess_evidence can report a moved head; the review summary must follow it."""
        comments = [scoreboard(states_with())]
        with patch.object(readiness, "evidence", return_value=(CURRENT, comments, STATUSES)), \
                patch.object(readiness, "assess_evidence", return_value=assessed("awaiting-CI", head="moved")):
            values = board.card(PR, "eic/EpsilonEridani")["values"]
        self.assertEqual(values["Status"], "No review at head")
        self.assertEqual(values["Review head"], "33e6bc2 (superseded; was 10/10 green)")
        self.assertIsNone(values["Rubrics green"])
        self.assertEqual(values["Prior green"], 10)


# ----- the Projects side, against a scripted GraphQL ---------------------------------------------

def field(name, kind, fid=None, options=()):
    return {"id": fid or f"F_{name}", "type": kind,
            "options": {o: f"O_{name}_{o}" for o in options},
            "option_details": [{"name": o, "color": "GRAY", "description": ""} for o in options]}


def project_with(items=None, fields=None):
    if fields is None:
        fields = {name: field(name, kind, options=[o for o, _, _ in (opts or [])])
                  for name, (kind, opts) in board.FIELDS.items()}
    return {"id": "PVT_1", "title": "Board", "url": "https://github.com/orgs/eic/projects/1",
            "fields": fields, "items": items or {}}


class FakeGraphQL:
    """Records every mutation; answers the few queries the writes read back."""

    def __init__(self):
        self.calls = []

    def __call__(self, query, variables=None):
        self.calls.append((query, variables or {}))
        if "addProjectV2ItemById" in query:
            return {"addProjectV2ItemById": {"item": {"id": "ITEM_" + variables["content"]}}}
        if "createProjectV2Field" in query:
            opts = [{"id": f"O_{variables['name']}_{o['name']}", **o} for o in variables.get("options", [])]
            return {"createProjectV2Field": {"projectV2Field": {
                "id": "F_" + variables["name"], "name": variables["name"],
                "dataType": variables["type"], "options": opts}}}
        if "updateProjectV2Field" in query:
            opts = [{"id": f"O_x_{o['name']}", **o} for o in variables["options"]]
            return {"updateProjectV2Field": {"projectV2Field": {"options": opts}}}
        return {"ok": True}

    def mutations(self, name):
        return [v for q, v in self.calls if name in q]


class Writes(unittest.TestCase):
    def setUp(self):
        self.gql = FakeGraphQL()
        patcher = patch.object(board, "graphql", self.gql)
        patcher.start()
        self.addCleanup(patcher.stop)

    def card_values(self, **overrides):
        values = {"Status": "1–2 to go", "Rubrics green": 8, "Prior green": None, "Not green": "reuse: changes",
                  "Lifecycle": "awaiting-author", "Roadmap": "LightNuclei",
                  "Review head": "33e6bc2 (current head)", "Reviewed": "2026-11-01"}
        values.update(overrides)
        return {"number": 199, "node_id": "PR_node", "title": "t", "url": "u", "head": HEAD,
                "values": values, "reason": ""}

    def test_a_new_pr_is_added_and_every_field_set(self):
        project = project_with()
        n = board.apply_card(project, self.card_values())
        self.assertEqual(n, 1 + len(board.FIELDS) - 1, "the add, then every field but the empty Prior green")
        self.assertEqual(self.gql.mutations("addProjectV2ItemById"), [{"project": "PVT_1", "content": "PR_node"}])
        sets = self.gql.mutations("updateProjectV2ItemFieldValue")
        by_field = {v["field"]: v["value"] for v in sets}
        self.assertEqual(by_field["F_Status"], {"singleSelectOptionId": "O_Status_1–2 to go"})
        self.assertEqual(by_field["F_Rubrics green"], {"number": 8})
        self.assertEqual(by_field["F_Not green"], {"text": "reuse: changes"})
        self.assertEqual(by_field["F_Lifecycle"], {"singleSelectOptionId": "O_Lifecycle_awaiting-author"})
        self.assertEqual(by_field["F_Reviewed"], {"date": "2026-11-01"})
        self.assertTrue(all(v["item"] == "ITEM_PR_node" for v in sets))
        self.assertEqual(project["items"][199]["values"]["Rubrics green"], 8)

    def test_an_unchanged_item_costs_no_mutation(self):
        stored = dict(self.card_values()["values"], **{"Rubrics green": 8.0})   # numbers come back as floats
        project = project_with(items={199: {"id": "I", "archived": False, "values": stored}})
        self.assertEqual(board.apply_card(project, self.card_values()), 0)
        self.assertEqual(self.gql.calls, [])

    def test_only_the_changed_fields_are_written(self):
        stored = dict(self.card_values()["values"])
        project = project_with(items={199: {"id": "I", "archived": False, "values": stored}})
        n = board.apply_card(project, self.card_values(**{"Status": "All rubrics green", "Rubrics green": 10,
                                                          "Not green": ""}))
        self.assertEqual(n, 3)
        fields = sorted(v["field"] for _, v in self.gql.calls)
        self.assertEqual(fields, ["F_Not green", "F_Rubrics green", "F_Status"])
        clear = [q for q, _ in self.gql.calls if "clearProjectV2ItemFieldValue" in q]
        self.assertEqual(len(clear), 1, "an empty text clears the field rather than writing ''")

    def test_an_empty_score_clears_the_number(self):
        stored = dict(self.card_values()["values"])
        project = project_with(items={199: {"id": "I", "archived": False, "values": stored}})
        board.apply_card(project, self.card_values(**{"Rubrics green": None, "Reviewed": None}))
        cleared = [v["field"] for q, v in self.gql.calls if "clearProjectV2ItemFieldValue" in q]
        self.assertEqual(sorted(cleared), ["F_Reviewed", "F_Rubrics green"])

    def test_a_reopened_pr_is_unarchived(self):
        stored = dict(self.card_values()["values"])
        project = project_with(items={199: {"id": "I", "archived": True, "values": stored}})
        self.assertEqual(board.apply_card(project, self.card_values()), 1)
        self.assertEqual(len(self.gql.mutations("unarchiveProjectV2Item")), 1)
        self.assertFalse(project["items"][199]["archived"])

    def test_closed_prs_are_archived_once(self):
        project = project_with(items={1: {"id": "A", "archived": False, "values": {}},
                                      2: {"id": "B", "archived": True, "values": {}},
                                      3: {"id": "C", "archived": False, "values": {}}})
        self.assertEqual(board.archive_closed(project, {3}), 1)
        self.assertEqual(self.gql.mutations("archiveProjectV2Item"), [{"project": "PVT_1", "item": "A"}])
        self.assertTrue(project["items"][1]["archived"])

    def test_dry_run_plans_but_never_calls(self):
        project = project_with(items={1: {"id": "A", "archived": False, "values": {}}})
        board.apply_card(project, self.card_values(), dry_run=True)
        board.archive_closed(project, {199}, dry_run=True)
        self.assertEqual(self.gql.calls, [])

    def test_missing_fields_are_created_and_status_options_appended(self):
        existing_status = field("Status", "SINGLE_SELECT", options=["Todo", "Done"])
        project = project_with(fields={"Status": existing_status, "Roadmap": field("Roadmap", "TEXT")})
        board.ensure_fields(project)
        created = {v["name"]: v for v in self.gql.mutations("createProjectV2Field")}
        self.assertEqual(set(created), set(board.FIELDS) - {"Status", "Roadmap"})
        self.assertEqual(created["Rubrics green"]["type"], "NUMBER")
        self.assertEqual([o["name"] for o in created["Lifecycle"]["options"]],
                         [n for n, _, _ in board.LIFECYCLE_OPTIONS])
        updates = self.gql.mutations("updateProjectV2Field")
        self.assertEqual(len(updates), 1)
        names = [o["name"] for o in updates[0]["options"]]
        self.assertEqual(names[:2], ["Todo", "Done"], "existing options are kept, in place")
        self.assertEqual(names[2:], [n for n, _, _ in board.COLUMNS])
        self.assertIn("1–2 to go", project["fields"]["Status"]["options"])
        self.assertEqual(set(project["fields"]), set(board.FIELDS))

    def test_a_complete_project_needs_no_field_writes(self):
        board.ensure_fields(project_with())
        self.assertEqual(self.gql.calls, [])

    def test_dry_run_tolerates_fields_that_do_not_exist_yet(self):
        project = project_with(fields={"Status": field("Status", "SINGLE_SELECT", options=["Todo"])})
        board.ensure_fields(project, dry_run=True)
        n = board.apply_card(project, self.card_values(), dry_run=True)
        self.assertEqual(n, 1, "only the add is planned; no field can be set yet")
        self.assertEqual(self.gql.calls, [])


class Ranking(unittest.TestCase):
    def mk(self, number, status, green, title="t", prior=None):
        return {"number": number, "title": title, "url": f"https://x/{number}", "head": HEAD,
                "values": {"Status": status, "Rubrics green": green, "Prior green": prior,
                           "Not green": "a | b", "Lifecycle": "awaiting-review", "Roadmap": "",
                           "Review head": ""}, "reason": ""}

    def test_sorted_by_column_then_score_then_prior_score_then_number(self):
        cards = [self.mk(5, "6+ to go", 2), self.mk(3, "All rubrics green", 10),
                 self.mk(9, "1–2 to go", 8), self.mk(4, "1–2 to go", 9),
                 self.mk(7, "No review at head", None), self.mk(8, "No review at head", None, prior=3),
                 self.mk(6, "No review at head", None, prior=9), self.mk(2, "On hold", None)]
        order = [c["number"] for c in sorted(cards, key=board.sort_key)]
        self.assertEqual(order, [3, 4, 9, 5, 6, 8, 7, 2])

    def test_markdown_escapes_pipes_and_lists_failures(self):
        text = board.render_markdown([self.mk(3, "All rubrics green", 10, title="a|b")],
                                     failures=[(8, "rate limited")],
                                     project={"title": "Board", "url": "https://p"})
        self.assertIn("[Board](https://p)", text)
        self.assertIn("[#3](https://x/3) a\\|b | All rubrics green | 10/10 | a \\| b |", text)
        self.assertIn("- #8: rate limited", text)


class Sync(unittest.TestCase):
    def test_without_a_project_the_ranking_is_still_printed(self):
        pulls = [dict(PR, number=1, node_id="n1"), dict(PR, number=2, node_id="n2")]
        cards = {1: {"number": 1, "node_id": "n1", "title": "", "url": "https://x/1", "head": HEAD, "reason": "",
                     "values": {"Status": "6+ to go", "Rubrics green": 2, "Not green": "", "Lifecycle": "x",
                                "Roadmap": "", "Review head": "", "Reviewed": None}}}

        def fake_card(pr, repo, now=None):
            if pr["number"] == 2:
                raise RuntimeError("no merge base")
            return cards[pr["number"]]

        with patch.object(board, "open_pulls", return_value=pulls), \
                patch.object(board, "card", side_effect=fake_card), \
                patch.object(board, "load_project") as load, \
                patch.object(board, "write_summary") as summary, \
                patch("builtins.print"):
            failures = board.sync("eic/EpsilonEridani", None, "eic", "organization")
        load.assert_not_called()
        self.assertEqual(failures, [(2, "no merge base")])
        self.assertIn("| [#1]", summary.call_args[0][0])
        self.assertIn("- #2: no merge base", summary.call_args[0][0])

    def test_a_rate_limit_stops_the_pass_and_is_reported(self):
        pulls = [dict(PR, number=1), dict(PR, number=2)]
        with patch.object(board, "open_pulls", return_value=pulls), \
                patch.object(board, "card", side_effect=core.RateLimited("paused")) as card, \
                patch.object(board, "write_summary"), patch("builtins.print"):
            failures = board.sync("eic/EpsilonEridani", None, "eic", "organization")
        self.assertEqual(card.call_count, 1)
        self.assertEqual(failures, [(1, "paused")])

    def test_single_closed_pr_is_archived_and_nothing_else_touched(self):
        project = project_with(items={5: {"id": "I5", "archived": False, "values": {}},
                                      6: {"id": "I6", "archived": False, "values": {}}})
        gql = FakeGraphQL()
        with patch.object(board, "graphql", gql), patch.object(board, "load_project", return_value=project), \
                patch.object(board, "pull", return_value=dict(PR, number=5, state="closed")), \
                patch.object(board, "write_summary"), patch("builtins.print"):
            board.sync("eic/EpsilonEridani", 1, "eic", "organization", pr=5)
        self.assertEqual(gql.mutations("archiveProjectV2Item"), [{"project": "PVT_1", "item": "I5"}])
        self.assertFalse(project["items"][6]["archived"])

    def test_graphql_errors_are_raised_not_swallowed(self):
        bad = type("R", (), {"stdout": json.dumps({"errors": [{"message": "Could not resolve"}]}),
                             "stderr": "", "returncode": 0})()
        with patch.object(board.subprocess, "run", return_value=bad):
            with self.assertRaises(RuntimeError):
                board.graphql("query { x }")

    def test_graphql_rate_limit_trips_the_shared_breaker(self):
        core._BLOCKED_UNTIL = 0.0
        self.addCleanup(setattr, core, "_BLOCKED_UNTIL", 0.0)
        limited = type("R", (), {"stdout": json.dumps({"errors": [{"type": "RATE_LIMITED", "message": "x"}]}),
                                 "stderr": "", "returncode": 0})()
        with patch.object(board.subprocess, "run", return_value=limited):
            with self.assertRaises(core.RateLimited):
                board.graphql("query { x }")
        with self.assertRaises(core.RateLimited):
            board.graphql("query { y }")   # refused without a call


if __name__ == "__main__":
    unittest.main()
