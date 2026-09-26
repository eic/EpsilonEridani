#!/usr/bin/env python3
"""Compile real independent Lean modules, then exercise the declaration audit."""

import os
from pathlib import Path
import subprocess
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
DRIVER = ROOT / "scripts/DuplicateDeclarations.lean"
LEAN = os.environ.get("LEAN", "lean")


class DuplicateDeclarationsTest(unittest.TestCase):
    def fixture(self, modules, *, missing=None, missing_part=None):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "EpsilonEridani").mkdir()
            env = os.environ.copy()
            # Fixtures need only Lean's sysroot; never pick up real EpsilonEridani artifacts.
            env["LEAN_PATH"] = tmp
            sources = {"EpsilonEridani": "module\n", **modules}
            for module, body in sources.items():
                path = root / (module.replace(".", "/") + ".lean")
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(body)
                built = subprocess.run(
                    [LEAN, "-o", str(path.with_suffix(".olean")), str(path)],
                    cwd=root, env=env, text=True, capture_output=True,
                )
                self.assertEqual(built.returncode, 0, built.stdout + built.stderr)
            if missing:
                (root / (missing.replace(".", "/") + ".olean")).unlink()
            if missing_part:
                (root / (missing_part.replace(".", "/") + ".olean.private")).unlink()
            return subprocess.run(
                [LEAN, "--run", str(DRIVER)],
                cwd=root, env=env, text=True, capture_output=True,
            )

    def assert_collision(self, result, name="Collision", first="EpsilonEridani.A", second="EpsilonEridani.B"):
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(name, result.stderr)
        self.assertIn(first, result.stderr)
        self.assertIn(second, result.stderr)

    def test_identical_independent_definitions_and_empty_root(self):
        self.assert_collision(self.fixture({
            "EpsilonEridani.A": "module\npublic def Collision := 7\n",
            "EpsilonEridani.B": "module\npublic def Collision := 7\n",
        }))

    def test_different_definitions(self):
        self.assert_collision(self.fixture({
            "EpsilonEridani.A": "module\npublic def Collision := 7\n",
            "EpsilonEridani.B": "module\npublic def Collision := true\n",
        }))

    def test_compatible_theorems_even_when_joint_import_succeeds(self):
        self.assert_collision(self.fixture({
            "EpsilonEridani.A": "module\npublic theorem Collision : True := True.intro\n",
            "EpsilonEridani.B": "module\npublic theorem Collision : True := by trivial\n",
            "EpsilonEridani.Both": "module\npublic import EpsilonEridani.A\npublic import EpsilonEridani.B\n",
        }))

    def test_lazy_equations_are_allowed(self):
        result = self.fixture({
            "EpsilonEridani.Base": "module\n@[expose] public def f : Nat → Nat | 0 => 0 | n+1 => n\n",
            "EpsilonEridani.A": "module\npublic import EpsilonEridani.Base\n"
                         "public theorem testA : f 0 = 0 := by simp only [f]\n",
            "EpsilonEridani.B": "module\npublic import EpsilonEridani.Base\n"
                         "public theorem testB : f 0 = 0 := by simp only [f]\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_user_theorem_with_reserved_looking_name_is_not_exempt(self):
        self.assert_collision(self.fixture({
            "EpsilonEridani.A": "module\npublic theorem f.eq_1 : True := True.intro\n",
            "EpsilonEridani.B": "module\npublic theorem f.eq_1 : True := True.intro\n",
            "EpsilonEridani.Base": "module\n@[expose] public def f : Nat → Nat | 0 => 0 | n+1 => n\n",
        }), "f.eq_1")

    def test_nonexported_definitions_are_module_private(self):
        result = self.fixture({
            "EpsilonEridani.A": "module\ndef Collision := 7\n",
            "EpsilonEridani.B": "module\ndef Collision := 7\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_generated_declarations(self):
        result = self.fixture({
            "EpsilonEridani.A": "module\npublic structure Collision where\n  x : Nat\n",
            "EpsilonEridani.B": "module\npublic structure Collision where\n  x : Nat\n",
        })
        self.assert_collision(result, "Collision.")

    def test_local_instance_is_not_a_private_declaration(self):
        self.assert_collision(self.fixture({
            "EpsilonEridani.A": "module\npublic section\nlocal instance Collision : Nonempty Nat := ⟨0⟩\n",
            "EpsilonEridani.B": "module\npublic section\nlocal instance Collision : Nonempty Nat := ⟨0⟩\n",
        }))

    def test_private_helpers_and_namespaces_and_quoted_identifiers(self):
        result = self.fixture({
            "EpsilonEridani.A": 'module\nprivate def helper := 1\npublic def A.item := 1\n'
                         'public def «A.B» := 1\n',
            "EpsilonEridani.B": 'module\nprivate def helper := 1\npublic def B.item := 1\n'
                         'public def A.B := 1\n',
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_diamond_imports(self):
        result = self.fixture({
            "EpsilonEridani.Base": "module\npublic def Unique := 1\n",
            "EpsilonEridani.A": "module\npublic import EpsilonEridani.Base\n",
            "EpsilonEridani.B": "module\npublic import EpsilonEridani.Base\n",
            "EpsilonEridani.Diamond": "module\npublic import EpsilonEridani.A\npublic import EpsilonEridani.B\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_dependency_collision(self):
        self.assert_collision(self.fixture({
            "Dependency": "module\npublic def Collision := 1\n",
            "EpsilonEridani.A": "module\npublic import Dependency\n",
            "EpsilonEridani.B": "module\npublic def Collision := 1\n",
        }), first="Dependency")

    def test_dependency_only_collision_is_out_of_scope(self):
        result = self.fixture({
            "DependencyA": "module\npublic theorem Collision : True := True.intro\n",
            "DependencyB": "module\npublic theorem Collision : True := True.intro\n",
            "EpsilonEridani.A": "module\npublic import DependencyA\n",
            "EpsilonEridani.B": "module\npublic import DependencyB\n",
        })
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_compatible_collision_with_multiple_dependencies(self):
        # These equal theorems survive Lean's importer. Only the ownership audit catches
        # the local collision, including when two dependencies already share the name.
        self.assert_collision(self.fixture({
            "DependencyA": "module\npublic theorem Collision : True := True.intro\n",
            "DependencyB": "module\npublic theorem Collision : True := True.intro\n",
            "EpsilonEridani.Own": "module\npublic theorem Collision : True := True.intro\n",
            "EpsilonEridani.A": "module\npublic import DependencyA\n",
            "EpsilonEridani.B": "module\npublic import DependencyB\n",
        }), first="Dependency", second="EpsilonEridani.Own")

    def test_missing_artifacts_fail_closed(self):
        for options in ({"missing": "EpsilonEridani.A"}, {"missing_part": "EpsilonEridani.A"}):
            with self.subTest(options=options):
                result = self.fixture({"EpsilonEridani.A": "module\npublic def Unique := 1\n"}, **options)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("duplicate-declarations:", result.stderr)

    def test_empty_source_tree_fails_closed(self):
        result = self.fixture({})
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
