"""Tests for scripts/lint-scope.sh, with a fake `gh` that serves canned API responses."""

import os
import pathlib
import shlex
import shutil
import subprocess
import sys
import tempfile
import unittest

import yaml

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))

import fake_gh  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "scripts" / "lint-scope.sh"
SHA_A, SHA_B = "a" * 40, "b" * 40


def pr(head_ref="feature", labels=()):
    return {"head": {"ref": head_ref}, "labels": [{"name": n} for n in labels]}


def f(status, filename):
    return {"status": status, "filename": filename}


@unittest.skipUnless(shutil.which("jq"), "needs jq")
class LintScopeTest(unittest.TestCase):
    def run_scope(self, env, responses):
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            github_env = d / "github_env"
            full_env = dict(fake_gh.install(d, responses),
                            GITHUB_ENV=str(github_env), GH_TOKEN="x", REPO="o/r", **env)
            out = subprocess.run(["bash", str(SCRIPT), str(d / "scope")], env=full_env,
                                 capture_output=True, text=True)
            self.assertEqual(out.returncode, 0, out.stderr)
            setting = github_env.read_text().strip()
            self.assertTrue(setting.startswith("LINT_ONLY_MODULES="), setting)
            if setting == "LINT_ONLY_MODULES=":
                return None
            return pathlib.Path(setting.split("=", 1)[1]).read_text().split()

    PR_ENV = {"EVENT": "pull_request_target", "NUM": "12", "BASE": SHA_A, "HEAD": SHA_B,
              "HEAD_REPO": "fork/r"}
    PR_COMPARE = f"repos/o/r/compare/{SHA_A}...fork:{SHA_B}"

    def test_pull_request_lints_changed_epsiloneridani_modules(self):
        # The scope comes from comparing the exact commits being built, across the fork.
        modules = self.run_scope(
            self.PR_ENV,
            {self.PR_COMPARE: {"files": [f("modified", "EpsilonEridani/A/B.lean"),
                                         f("added", "EpsilonEridani/C.lean"),
                                         f("renamed", "EpsilonEridani/D'.lean"),
                                         f("removed", "EpsilonEridani/Gone.lean"),
                                         f("modified", "README.md"),
                                         f("modified", "EpsilonEridani/notes.md")]},
             "repos/o/r/pulls/12": pr()})
        self.assertEqual(modules, ["EpsilonEridani.A.B", "EpsilonEridani.C", "EpsilonEridani.D'"])

    def test_no_epsiloneridani_change_lints_nothing(self):
        self.assertEqual(self.run_scope(
            self.PR_ENV,
            {self.PR_COMPARE: {"files": [f("modified", "lake-manifest.json")]},
             "repos/o/r/pulls/12": pr()}), [])

    def test_pull_request_without_commits_lints_everything(self):
        for missing in ("BASE", "HEAD", "HEAD_REPO"):
            with self.subTest(missing=missing):
                self.assertIsNone(self.run_scope(dict(self.PR_ENV, **{missing: ""}), {}))

    def test_compare_cap_lints_everything(self):
        self.assertIsNone(self.run_scope(
            self.PR_ENV,
            {self.PR_COMPARE: {"files": [f("modified", f"EpsilonEridani/M{i}.lean") for i in range(300)]},
             "repos/o/r/pulls/12": pr()}))

    def test_full_lint_label_and_repair_branch_lint_everything(self):
        files = {self.PR_COMPARE: {"files": [f("modified", "EpsilonEridani/A.lean")]}}
        for info in (pr(labels=["roadmap/none", "full-lint"]), pr(head_ref="lint-repair/main")):
            with self.subTest(info=info):
                self.assertIsNone(self.run_scope(
                    self.PR_ENV, dict(files, **{"repos/o/r/pulls/12": info})))

    def test_merge_group_reads_prs_from_squash_titles(self):
        compare = {"commits": [{"commit": {"message": "feat: x (#7)\n\nbody"}},
                               {"commit": {"message": "fix: y (#8)"}}],
                   "files": [f("modified", "EpsilonEridani/X.lean")]}
        responses = {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare,
                     "repos/o/r/pulls/7": pr(), "repos/o/r/pulls/8": pr()}
        env = {"EVENT": "merge_group", "BASE": SHA_A, "HEAD": SHA_B}
        self.assertEqual(self.run_scope(env, responses), ["EpsilonEridani.X"])
        responses["repos/o/r/pulls/8"] = pr(labels=["full-lint"])
        self.assertIsNone(self.run_scope(env, responses))

    def test_unattributable_commits_lint_everything(self):
        compare = {"commits": [{"commit": {"message": "feat: x (#7)"}},
                               {"commit": {"message": "Merge branch main"}}],
                   "files": [f("modified", "EpsilonEridani/X.lean")]}
        self.assertIsNone(self.run_scope(
            {"EVENT": "push", "BASE": SHA_A, "HEAD": SHA_B},
            {f"repos/o/r/compare/{SHA_A}...{SHA_B}": compare, "repos/o/r/pulls/7": pr()}))

    def test_missing_base_lints_everything(self):
        self.assertIsNone(self.run_scope({"EVENT": "push", "BASE": "0" * 40, "HEAD": SHA_B}, {}))


class PrBuildWiringTest(unittest.TestCase):
    def test_scope_is_decided_before_the_sandbox_and_mounted_read_only(self):
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        (job,) = [j for j in wf["jobs"].values()
                  if any("Build exact candidate under bwrap" in s.get("name", "")
                         for s in j.get("steps", []))]
        names = [s.get("name", "") for s in job["steps"]]
        scope = names.index("Decide the environment-lint scope")
        sandbox = next(i for i, n in enumerate(names) if "Build exact candidate under bwrap" in n)
        self.assertLess(scope, sandbox)
        run = job["steps"][sandbox]["run"]
        self.assertIn('--ro-bind "$LINT_SCOPE_DIR" "$LINT_SCOPE_DIR"', run)
        self.assertIn('--setenv LINT_ONLY_MODULES "${LINT_ONLY_MODULES:-}"', run)

    def repair_exemption(self, event, files, env=None, api=None):
        """Run pr-build's empty-repair-PR exemption, extracted from the Scope guard step, with a fake
        `gh` that prints `api` (or fails when it is None). Returns (repair_pr, routed_to_human)."""
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        (job,) = [j for j in wf["jobs"].values()
                  if any("Build exact candidate under bwrap" in s.get("name", "")
                         for s in j.get("steps", []))]
        run = next(s["run"] for s in job["steps"] if s.get("name", "").startswith("Scope guard"))
        start = run.index("repair_pr=0")
        end = run.index('elif [ -n "$files" ]; then', start)
        block = run[start:end] + "fi\necho \"repair_pr=$repair_pr\"\n"
        block = (block.replace("${{ github.event_name }}", event)
                      .replace("${{ github.repository }}", "o/r")
                      .replace("${{ steps.pr.outputs.num }}", "12"))
        with tempfile.TemporaryDirectory() as d:
            d = pathlib.Path(d)
            gh = d / "gh"
            gh.write_text("#!/usr/bin/env bash\n" + ("exit 1\n" if api is None else
                                                    f"printf '%s\\n' {shlex.quote(api)}\n"))
            gh.chmod(0o755)
            github_env = d / "github_env"
            github_env.write_text("")
            out = subprocess.run(
                ["bash", "-c", f"set -uo pipefail\nfiles={shlex.quote(files)}\n{block}"],
                env={**os.environ, "PATH": f"{d}:{os.environ['PATH']}", "GITHUB_ENV": str(github_env),
                     "PR_HEAD_REF": "", "PR_HEAD_REPO": "", "PR_USER": "", **(env or {})},
                capture_output=True, text=True)
            self.assertEqual(out.returncode, 0, out.stderr)
            return ("repair_pr=1" in out.stdout, "INFRA=1" in github_env.read_text())

    BOT = "epsiloneridani-review-bot[bot]"

    def test_dispatched_empty_repair_pr_is_built(self):
        self.assertEqual(self.repair_exemption(
            "workflow_dispatch", "", api=f"lint-repair/main\to/r\t{self.BOT}"), (True, False))

    def test_pull_request_empty_repair_pr_is_built(self):
        env = {"PR_HEAD_REF": "lint-repair/main", "PR_HEAD_REPO": "o/r", "PR_USER": self.BOT}
        self.assertEqual(self.repair_exemption("pull_request_target", "", env=env), (True, False))

    def test_other_dispatched_empty_prs_go_to_a_human(self):
        for api in (f"feature\to/r\t{self.BOT}", f"lint-repair/main\tfork/r\t{self.BOT}",
                    "lint-repair/main\to/r\tsomeone", ""):
            with self.subTest(api=api):
                self.assertEqual(self.repair_exemption("workflow_dispatch", "", api=api),
                                 (False, True))

    def test_api_failure_goes_to_a_human(self):
        self.assertEqual(self.repair_exemption("workflow_dispatch", "", api=None), (False, True))

    def test_nonempty_diff_is_not_exempted(self):
        self.assertEqual(self.repair_exemption(
            "workflow_dispatch", "EpsilonEridani/A.lean", api=f"lint-repair/main\to/r\t{self.BOT}"),
            (False, False))

    def test_only_the_full_lint_label_rebuilds(self):
        # pr-build does not run on label changes; a separate workflow dispatches it for full-lint.
        pr_build = yaml.safe_load((ROOT / ".github" / "workflows" / "pr-build.yml").read_text())
        self.assertNotIn("labeled", pr_build[True]["pull_request_target"]["types"])
        self.assertIn("workflow_dispatch", pr_build[True])
        wf = yaml.safe_load((ROOT / ".github" / "workflows" / "full-lint-label.yml").read_text())
        self.assertEqual(wf[True]["pull_request_target"]["types"], ["labeled"])
        (job,) = wf["jobs"].values()
        self.assertEqual(job["if"], "${{ github.event.label.name == 'full-lint' }}")
        self.assertIn("gh workflow run pr-build.yml", job["steps"][0]["run"])

if __name__ == "__main__":
    unittest.main()
