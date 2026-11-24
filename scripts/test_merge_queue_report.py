"""Run with python3 scripts/test_merge_queue_report.py."""

import unittest

import merge_queue_report as mqr

SHA = "6abfc81dfe86638f850566b671287b97f8d34fc0"
HEAD = "349d6b762cdaa0ae6ba40c7dcc056072336f22fc"

LOG = """\
2026-11-24T13:35:32.8298103Z ✖ [19086/19088] Building EpsilonEridani.QFT.Lattice.Data.Basic (1.4s)
2026-11-24T13:35:32.8300000Z trace: .> LEAN_PATH=...
2026-11-24T13:35:32.8311892Z error: EpsilonEridani/QFT/Lattice/Data/Basic.lean:156:27: `Matrix.posSemidef_is_closed` has been deprecated: Use `isClosed_setOfPred_posSemidef` instead
2026-11-24T13:35:33.0303795Z error: build failed
2026-11-24T13:35:33.0686174Z ##[error]Process completed with exit code 1.
2026-11-24T13:35:34.0000000Z \x1b[31merror: build failed\x1b[0m
"""


class MergeQueueReport(unittest.TestCase):
    def test_parse_branch(self):
        self.assertEqual(mqr.parse_branch(f"gh-readonly-queue/main/pr-203-{SHA}"),
                         ("main", 203, SHA))
        self.assertIsNone(mqr.parse_branch("main"))
        self.assertIsNone(mqr.parse_branch(f"gh-readonly-queue/main/pr-x-{SHA}"))
        self.assertIsNone(mqr.parse_branch(None))

    def test_extract_errors_drops_noise_and_duplicates(self):
        self.assertEqual(mqr.extract_errors(LOG), [
            "✖ [19086/19088] Building EpsilonEridani.QFT.Lattice.Data.Basic (1.4s)",
            "error: EpsilonEridani/QFT/Lattice/Data/Basic.lean:156:27: "
            "`Matrix.posSemidef_is_closed` has been deprecated: "
            "Use `isClosed_setOfPred_posSemidef` instead",
            "error: build failed",
        ])

    def test_extract_errors_caps(self):
        log = "\n".join(f"error: e{i}" for i in range(100))
        self.assertEqual(len(mqr.extract_errors(log, max_lines=5)), 5)
        long = mqr.extract_errors("error: " + "x" * 1000)[0]
        self.assertTrue(long.endswith(" …"))
        self.assertLess(len(long), mqr.MAX_LINE_CHARS + 5)

    def test_group_prs(self):
        subjects = ["feat: a (#10)", "fix: b (#203)", "chore: no number", "feat: c (#10)"]
        self.assertEqual(mqr.group_prs(subjects, 203), [10])

    def test_render_defuses_fences_and_carries_marker(self):
        body = mqr.render(pr_head=HEAD, run_url="https://x/run", base_branch="main",
                          base_sha=SHA, group_sha="62b5327d2818970e04a9273075cead5596eb97ff",
                          jobs=[{"name": "build", "url": "https://x/job", "steps": ["Build"],
                                 "errors": ["error: ```oops"]}],
                          others=[10])
        self.assertIn("[pr-build run](https://x/run)", body)
        self.assertIn("#10", body)
        self.assertEqual(body.count("```"), 2)
        self.assertEqual(mqr.MARKER_RE.search(body)[1], HEAD)

    def test_render_without_jobs(self):
        body = mqr.render(pr_head=HEAD, run_url="u", base_branch="main", base_sha=SHA,
                          group_sha=SHA, jobs=[], others=[])
        self.assertIn("No failed job was found", body)
        self.assertNotIn("also contained", body)


if __name__ == "__main__":
    unittest.main()
