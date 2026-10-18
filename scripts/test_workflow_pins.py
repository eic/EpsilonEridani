"""Ensure every EpsilonEridaniReview checkout follows the pinned reusable-workflow commit.

Dependabot rewrites only `uses: owner/repo/...@sha` lines. Every other reference to the
EpsilonEridaniReview commit (a reusable call's `review_ref`, a checkout's `ref`) is therefore read
at run time from a `uses:` line by .github/actions/review-pin, never written as a literal SHA.

Run with: python3 scripts/test_workflow_pins.py
"""

import os
import pathlib
import re
import subprocess
import tempfile
import unittest


ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOW_DIR = ROOT / ".github/workflows"
ACTION = ROOT / ".github/actions/review-pin/action.yml"
WORKFLOWS = (
    WORKFLOW_DIR / "auto-merge.yml",
    WORKFLOW_DIR / "merge-sweep.yml",
    WORKFLOW_DIR / "review.yml",
)
# Workflows that check EpsilonEridaniReview out directly, with their number of checkouts. They
# follow auto-merge.yml's pin, the merge policy whose readiness rule they report on or test.
STATUS_READERS = (("pr-labels.yml", 3), ("pages.yml", 1), ("ci.yml", 1))
CALL_PIN = re.compile(
    r"uses:\s+eic/EpsilonEridaniReview/\.github/workflows/[^@\s]+@([0-9a-f]{40})"
)
# The reusable call's `review_ref` input (not the pin job's `review_ref` output, which reads the action).
REVIEW_REF = re.compile(r"^\s+review_ref:\s+(?!\$\{\{ steps\.review-pin\.)(.+?)\s*$", re.MULTILINE)
CHECKOUT_REF = re.compile(r"repository: eic/EpsilonEridaniReview\s+ref: (.+?)\s*$", re.MULTILINE)
# A review-pin step with no `with:`, i.e. reading the default workflow (auto-merge.yml).
PIN_STEP = re.compile(
    r"id: review-pin\n(?:\s+continue-on-error: true\n)?\s+uses: ./.github/actions/review-pin\n(?!\s+with:)"
)
PIN_STEP_FOR = "id: review-pin\n        uses: ./.github/actions/review-pin\n        with:\n          workflow: {}\n"


def action_script():
    """The shell body of the review-pin action's single `run: |` step."""
    lines = ACTION.read_text().splitlines()
    start = next(i for i, line in enumerate(lines) if line.strip() == "run: |") + 1
    indent = len(lines[start]) - len(lines[start].lstrip())
    body = []
    for line in lines[start:]:
        if line.strip() and len(line) - len(line.lstrip()) < indent:
            break
        body.append(line[indent:])
    return "\n".join(body) + "\n"


def run_action(workflow, workspace=ROOT):
    """Run the action's script as Actions would; return (exit code, outputs dict)."""
    with tempfile.NamedTemporaryFile("r") as out:
        env = dict(os.environ, GITHUB_WORKSPACE=str(workspace), GITHUB_OUTPUT=out.name, WORKFLOW=workflow)
        proc = subprocess.run(["bash", "-c", action_script()], env=env, capture_output=True, text=True)
        outputs = dict(line.split("=", 1) for line in out.read().splitlines() if "=" in line)
    return proc.returncode, outputs


class WorkflowPins(unittest.TestCase):
    def test_status_readers_and_tests_use_the_auto_merge_policy(self):
        for name, count in STATUS_READERS:
            with self.subTest(workflow=name):
                text = (WORKFLOW_DIR / name).read_text()
                refs = CHECKOUT_REF.findall(text)
                self.assertEqual(refs, ["${{ steps.review-pin.outputs.sha }}"] * count, name)
                self.assertEqual(len(PIN_STEP.findall(text)), count, name)

    def test_workflow_and_checkout_pins_match(self):
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                text = workflow.read_text()
                self.assertEqual(len(CALL_PIN.findall(text)), 1, f"expected one pinned reusable call in {workflow}")
                self.assertEqual(len(REVIEW_REF.findall(text)), 1, f"expected one review_ref in {workflow}")
                self.assertRegex(
                    REVIEW_REF.findall(text)[0],
                    r"^\$\{\{ needs\.\w+\.outputs\.review_ref \}\}$",
                    f"{workflow.name} must derive review_ref from its own pin, not a literal SHA",
                )
                self.assertIn(PIN_STEP_FOR.format(workflow.name), text,
                              f"{workflow.name} must read the pin from its own file")
                self.assertIn("ref: ${{ github.workflow_sha }}", text,
                              f"{workflow.name} must read its pin from the trusted workflow commit")

    def test_action_reads_each_pin(self):
        for workflow in WORKFLOWS:
            with self.subTest(workflow=workflow.name):
                code, outputs = run_action(workflow.name)
                self.assertEqual(code, 0)
                self.assertEqual(outputs.get("sha"), CALL_PIN.findall(workflow.read_text())[0])

    def test_action_rejects_missing_or_conflicting_pins(self):
        sha = "0123456789abcdef0123456789abcdef01234567"
        cases = {
            "none.yml": "jobs: {}\n",
            "two.yml": (f"    uses: eic/EpsilonEridaniReview/.github/workflows/a.yml@{sha}\n"
                        f"    uses: eic/EpsilonEridaniReview/.github/workflows/b.yml@{sha[::-1]}\n"),
        }
        with tempfile.TemporaryDirectory() as tmp:
            (pathlib.Path(tmp) / ".github/workflows").mkdir(parents=True)
            for name, text in cases.items():
                (pathlib.Path(tmp) / ".github/workflows" / name).write_text(text)
                with self.subTest(case=name):
                    code, outputs = run_action(name, tmp)
                    self.assertNotEqual(code, 0)
                    self.assertNotIn("sha", outputs)

    def test_no_literal_review_sha_outside_uses_lines(self):
        for path in sorted(WORKFLOW_DIR.glob("*.yml")):
            for line in path.read_text().splitlines():
                if ("EpsilonEridaniReview" in line or "review_ref" in line) and re.search(r"[0-9a-f]{40}", line):
                    self.assertRegex(line, CALL_PIN, f"{path.name}: literal SHA outside a `uses:` pin")


if __name__ == "__main__":
    unittest.main()
