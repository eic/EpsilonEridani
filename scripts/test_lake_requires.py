#!/usr/bin/env python3
"""Unit tests for scripts/lake_requires.py. Run with: python3 scripts/test_lake_requires.py"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import lake_requires as lr  # noqa: E402

LAKEFILE = '''name = "EpsilonEridani"

[[require]]
name = "Physlib"
git = "https://github.com/x/physlib"
rev = "master"

# a comment between the requires
[[require]]
name = 'TauCeti'
git = "https://github.com/x/TauCeti"

[[require]]
name = "mathlib"
path = "../mathlib"

[[lean_lib]]
name = "EpsilonEridani"
'''


class Requires(unittest.TestCase):
    def test_the_names_are_in_declaration_order(self):
        self.assertEqual(lr.names(LAKEFILE), ["Physlib", "TauCeti", "mathlib"])

    def test_another_table_with_a_name_is_not_a_require(self):
        self.assertNotIn("EpsilonEridani", lr.names(LAKEFILE))

    def test_each_require_is_its_whole_table(self):
        self.assertEqual([r.get("git") for r in lr.parse(LAKEFILE)],
                         ["https://github.com/x/physlib", "https://github.com/x/TauCeti", None])

    def test_no_requires(self):
        self.assertEqual(lr.names('name = "x"\n'), [])

    def test_a_lakefile_that_is_not_toml_is_an_error(self):
        with self.assertRaises(Exception):
            lr.names("[[require\nname = ")


class RepoSlug(unittest.TestCase):
    def test_every_spelling_of_a_github_url_gives_owner_repo(self):
        for url in ("https://github.com/leanprover-community/mathlib4", "https://github.com/leanprover-community/mathlib4/",
                    "https://github.com/leanprover-community/mathlib4.git", "http://github.com/leanprover-community/mathlib4.git/",
                    " https://github.com/leanprover-community/mathlib4 \n", "leanprover-community/mathlib4"):
            self.assertEqual(lr.repo_slug(url), "leanprover-community/mathlib4", url)

    def test_another_host_is_left_whole_so_a_repo_swap_still_differs(self):
        self.assertNotEqual(lr.repo_slug("https://evil.example/leanprover-community/mathlib4"),
                            lr.repo_slug("https://github.com/leanprover-community/mathlib4"))

    def test_nothing(self):
        self.assertEqual(lr.repo_slug(None), "")


if __name__ == "__main__":
    unittest.main()
