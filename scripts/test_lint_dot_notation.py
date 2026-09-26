#!/usr/bin/env python3
"""Regression tests for ``scripts/lint-dot-notation.py``."""

from __future__ import annotations

import contextlib
import io
import pathlib
import tempfile
import unittest

import lean_source as lint


def findings(source: str, namespaces: set[str] | None = None):
    return lint.find_violations({pathlib.Path("EpsilonEridani/Test.lean"): source}, namespaces or {"Foo"})


class DotNotationLintTests(unittest.TestCase):
    def test_named_section_does_not_corrupt_namespace_stack(self):
        source = """\
public section
namespace EpsilonEridani
namespace Foo
def before (x : Foo) := x
section Chain
def inside (x : Foo) := x
end Chain
def after (x : Foo) := x
mutual
def mutualOne (x : Foo) := x
def mutualTwo (x : Foo) := x
end
def afterMutual (x : Foo) := x
end Foo
end EpsilonEridani
end
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         [f"EpsilonEridani.Foo.{name}" for name in
                          ("before", "inside", "after", "mutualOne", "mutualTwo", "afterMutual")])

    def test_attribute_anonymous_instance_and_modifiers_are_detected(self):
        source = """\
namespace EpsilonEridani
namespace Foo
@[expose] def attributed : Foo → Foo := fun x => x
@[simp,
  expose] theorem multilineAttribute (x : Foo) : True := True.intro
instance (x : Foo) : Inhabited Foo := ⟨x⟩
instance (priority := 100) (x : Foo) : Inhabited Foo := ⟨x⟩
nonrec def nonrecursive (x : Foo) := x
scoped instance namedInstance (x : Foo) : Inhabited Foo := ⟨x⟩
local instance localInstance (x : Foo) : Inhabited Foo := ⟨x⟩
partial def partialDefinition (x : Foo) := x
unsafe def unsafeDefinition (x : Foo) := x
def implicitOnly {x : Foo} := x
def connective (x : Foo × Foo) := x
class ClassDeclaration (x : Foo) : Prop where
  property : True
structure StructureDeclaration (x : Foo) where
  field : True
end Foo
end EpsilonEridani
"""
        result = findings(source)
        names = [finding.declaration for finding in result]
        self.assertEqual(len(result), 11)
        self.assertEqual(sum("<anonymous instance " in name for name in names), 2)
        for expected in ("attributed", "multilineAttribute", "nonrecursive", "namedInstance",
                         "localInstance", "partialDefinition", "unsafeDefinition",
                         "ClassDeclaration", "StructureDeclaration"):
            self.assertIn(f"EpsilonEridani.Foo.{expected}", names)

    def test_root_declaration_is_not_flagged(self):
        source = """\
namespace EpsilonEridani
namespace Foo
def _root_.Foo.correct (x : Foo) := x
def misplaced (x : Foo) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.misplaced"])

    def test_function_valued_binders_are_not_receivers(self):
        source = """\
namespace EpsilonEridani
namespace Foo
def returnsFoo : Foo := by
  exact (default : Foo)
def takesFunction (f : Foo → Foo) := f
def takesFoo (x : Foo) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.takesFoo"])

    def test_notation_receivers_and_dotted_subtypes(self):
        source = """\
namespace EpsilonEridani
namespace ContinuousLinearMap
def notationReceiver (T : E →L[𝕜] F) := T
def dottedSubtype (hT : ContinuousLinearMap.IsFredholm T) := hT
end ContinuousLinearMap
namespace LinearMap
def linearMapReceiver (f : M →ₗ[R] N) := f
end LinearMap
namespace Equiv
def equivReceiver (e : α ≃ β) := e
def longerNotationIsNotEquiv (e : α ≃L[𝕜] β) := e
end Equiv
namespace ContinuousMap
def continuousMapReceiver (f : C(X, Y)) := f
def continuousMapValuedFunction (f : C(X, Y) → Z) := f
end ContinuousMap
namespace ContinuousMultilinearMap
def multilinearReceiver (f : E [×n]→L[𝕜] F) := f
def multilinearValuedFunction (f : (E [×n]→L[𝕜] F) → Z) := f
end ContinuousMultilinearMap
namespace RingHom
def ringHomReceiver (f : R →+* S) := f
end RingHom
namespace AlgEquiv
def algEquivReceiver (e : A ≃ₐ[R] B) := e
end AlgEquiv
namespace LinearIsometryEquiv
def linearIsometryEquivReceiver (e : E ≃ₗᵢ[𝕜] F) := e
end LinearIsometryEquiv
namespace Homeomorph
def homeomorphReceiver (e : X ≃ₜ Y) := e
def longerHomeomorphNotation (e : G ≃ₜ* H) := e
end Homeomorph
namespace Diffeomorph
def withCornersReceiver (e : M ≃ₘ^n⟮I, J⟯ N) := e
def withCornersInfiniteReceiver (e : M ≃ₘ⟮I, J⟯ N) := e
def modelReceiver (e : E ≃ₘ^n[𝕜] F) := e
def modelInfiniteReceiver (e : E ≃ₘ[𝕜] F) := e
end Diffeomorph
namespace BialgHom
def bialgHomReceiver (f : A →ₐc[R] B) := f
end BialgHom
namespace CoalgEquiv
def coalgEquivReceiver (e : A ≃ₗc[R] B) := e
end CoalgEquiv
namespace LinearPMap
def linearPMapReceiver (f : E →ₗ.[R] F) := f
def semilinearPMapReceiver (f : E →ₛₗ.[σ] F) := f
end LinearPMap
namespace Hom
def categoryHomReceiver (f : X ⟶ Y) := f
end Hom
namespace TensorProduct
def tensorProductReceiver (x : M ⊗[R] N) := x
end TensorProduct
namespace LieHom
def lieHomReceiver (f : L →ₗ⁅R⁆ L') := f
end LieHom
end EpsilonEridani
"""
        result = findings(source, {"AlgEquiv", "BialgHom", "CoalgEquiv",
                                   "ContinuousLinearMap", "ContinuousMap",
                                   "ContinuousMultilinearMap", "Diffeomorph", "Equiv", "Hom",
                                   "Homeomorph", "LieHom", "LinearIsometryEquiv", "LinearMap",
                                   "LinearPMap", "RingHom", "TensorProduct"})
        self.assertEqual([finding.declaration for finding in result], [
            "EpsilonEridani.ContinuousLinearMap.notationReceiver",
            "EpsilonEridani.LinearMap.linearMapReceiver",
            "EpsilonEridani.Equiv.equivReceiver",
            "EpsilonEridani.ContinuousMap.continuousMapReceiver",
            "EpsilonEridani.ContinuousMultilinearMap.multilinearReceiver",
            "EpsilonEridani.RingHom.ringHomReceiver",
            "EpsilonEridani.AlgEquiv.algEquivReceiver",
            "EpsilonEridani.LinearIsometryEquiv.linearIsometryEquivReceiver",
            "EpsilonEridani.Homeomorph.homeomorphReceiver",
            "EpsilonEridani.Diffeomorph.withCornersReceiver",
            "EpsilonEridani.Diffeomorph.withCornersInfiniteReceiver",
            "EpsilonEridani.Diffeomorph.modelReceiver",
            "EpsilonEridani.Diffeomorph.modelInfiniteReceiver",
            "EpsilonEridani.BialgHom.bialgHomReceiver",
            "EpsilonEridani.CoalgEquiv.coalgEquivReceiver",
            "EpsilonEridani.LinearPMap.linearPMapReceiver",
            "EpsilonEridani.LinearPMap.semilinearPMapReceiver",
            "EpsilonEridani.Hom.categoryHomReceiver",
            "EpsilonEridani.TensorProduct.tensorProductReceiver",
            "EpsilonEridani.LieHom.lieHomReceiver",
        ])

    def test_scoped_variable_and_dotted_name_are_detected(self):
        source = """\
namespace EpsilonEridani
namespace Foo
variable (x : Foo)
variable {y : Foo}
def fromVariable : x = x := rfl
def implicitVariable : y = y := rfl
end Foo
def Foo.dotted (x : Foo) := x
def Foo.termType (x : Foo.term) := x
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.fromVariable", "EpsilonEridani.Foo.dotted"])

    def test_include_and_omit_follow_scope(self):
        source = """\
namespace EpsilonEridani
namespace Foo
variable (x : Foo)
include x
theorem included : True := True.intro
section Inner
omit x
theorem omittedInside : True := True.intro
end Inner
theorem restored : True := True.intro
omit x
theorem omittedAfter : True := True.intro
include x in
theorem includedOnce : True := True.intro
theorem omittedFinally : True := True.intro
end Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)], [
            "EpsilonEridani.Foo.included",
            "EpsilonEridani.Foo.restored",
            "EpsilonEridani.Foo.includedOnce",
        ])

    def test_owned_names_are_lowercase_and_matched_by_full_path(self):
        sources = {
            pathlib.Path("EpsilonEridani/Own.lean"): """\
namespace EpsilonEridani
def prod : Type := Nat
namespace prod
def fst (x : prod) := x
end prod
end EpsilonEridani
""",
            pathlib.Path("EpsilonEridani/Other.lean"): """\
namespace EpsilonEridani
namespace prod
def correctlyOwned (x : prod) := x
end prod
end EpsilonEridani
""",
            pathlib.Path("EpsilonEridani/Unrelated.lean"): """\
namespace EpsilonEridani.Other
namespace prod
def misplaced (x : prod) := x
end prod
end EpsilonEridani.Other
""",
            pathlib.Path("EpsilonEridani/Nested.lean"): """\
namespace EpsilonEridani
def Quiver.IsAcyclic : Type := Nat
end EpsilonEridani
""",
            pathlib.Path("EpsilonEridani/NestedOther.lean"): """\
namespace EpsilonEridani.Quiver.IsAcyclic
def correctlyNested (x : Quiver.IsAcyclic) := x
end EpsilonEridani.Quiver.IsAcyclic
""",
        }
        self.assertEqual([finding.declaration for finding in
                          lint.find_violations(sources, {"prod", "Quiver", "IsAcyclic"})],
                         ["EpsilonEridani.Other.prod.misplaced"])

    def test_value_declaration_does_not_exempt_a_namespace(self):
        source = """\
namespace EpsilonEridani
def Foo : Nat := 0
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.stillMisplaced"])

    def test_nested_owned_type_does_not_exempt_an_outer_namespace(self):
        source = """\
namespace EpsilonEridani.Foo
structure Owned
namespace Owned
def stillMisplaced (x : _root_.Foo) := x
end Owned
end EpsilonEridani.Foo
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.Owned.stillMisplaced"])

    def test_owned_type_does_not_exempt_a_nested_mathlib_named_namespace(self):
        source = """\
namespace EpsilonEridani
def Owned : Type := Nat
namespace Owned.Foo
def stillMisplaced (x : _root_.Foo) := x
end Owned.Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Owned.Foo.stillMisplaced"])

    def test_strict_implicit_type_binder_does_not_make_a_value_an_owned_type(self):
        source = """\
namespace EpsilonEridani
def Foo ⦃α : Type⦄ (n : Nat) : Nat := n
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.stillMisplaced"])

    def test_explicit_receiver_after_strict_implicit_binder_is_detected(self):
        source = """\
namespace EpsilonEridani.Foo
theorem detected ⦃α : Type⦄ (x : _root_.Foo) : True := True.intro
end EpsilonEridani.Foo
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.detected"])

    def test_parenthesized_arrow_domain_does_not_make_a_value_an_owned_type(self):
        source = """\
namespace EpsilonEridani
def Foo : (Type u) → Nat := fun _ ↦ 0
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.stillMisplaced"])

    def test_indexed_type_family_is_an_owned_type(self):
        source = """\
namespace EpsilonEridani
def Foo : Nat → Type := fun _ ↦ Nat
def Bar : Nat -> Type := fun _ ↦ Nat
namespace Foo
def correctlyOwned (x : _root_.Foo 0) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual(findings(source), [])
        self.assertIn(("EpsilonEridani", "Bar"), lint.own_declaration_paths(
            {pathlib.Path("EpsilonEridani/Test.lean"): source}))

    def test_unannotated_type_alias_is_not_an_owned_type(self):
        source = """\
namespace EpsilonEridani
abbrev Foo := Nat
namespace Foo
def stillMisplaced (x : _root_.Foo) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual([finding.declaration for finding in findings(source)],
                         ["EpsilonEridani.Foo.stillMisplaced"])

    def test_prop_and_opaque_sort_results_are_owned(self):
        source = """\
namespace EpsilonEridani
def Predicate : Prop := True
opaque Hidden : Type
def Family : ∀ n : Nat, Type := fun _ ↦ Nat
def Parenthesized : (Nat → Type) := fun _ ↦ Nat
end EpsilonEridani
"""
        self.assertEqual(lint.own_declaration_paths(
            {pathlib.Path("EpsilonEridani/Test.lean"): source}),
            {("EpsilonEridani", "Predicate"), ("EpsilonEridani", "Hidden"),
             ("EpsilonEridani", "Family"), ("EpsilonEridani", "Parenthesized")})

    def test_universe_annotation_is_not_part_of_a_declaration_name(self):
        source = """\
namespace EpsilonEridani
def Foo.{u} (X : Type u) : Type u := X
namespace Foo
def correctlyOwned (x : _root_.Foo Type) := x
end Foo
end EpsilonEridani
"""
        self.assertEqual(findings(source), [])
        self.assertIn(("EpsilonEridani", "Foo"), lint.own_declaration_paths(
            {pathlib.Path("EpsilonEridani/Test.lean"): source}))

    def test_missing_mathlib_checkout_fails_loudly(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            source_root = root / "EpsilonEridani"
            source_root.mkdir()
            baseline = root / "baseline.txt"
            baseline.write_text("")
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr):
                result = lint.main(
                    ["--mathlib-root", str(root / "missing"), "--source-root", str(source_root),
                     "--baseline", str(baseline)])
        self.assertEqual(result, 2)
        self.assertIn("Mathlib source directory not found", stderr.getvalue())

    def test_primed_identifier_does_not_open_a_character_literal(self):
        cleaned = lint.strip_comments_and_strings("Homeomorph.prodAssoc F F' G' ''\ndef next := 1\n")
        self.assertIn("def next", cleaned)

    def test_main_rejects_new_and_reports_ratchetable_findings(self):
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            mathlib = root / "Mathlib"
            source_root = root / "EpsilonEridani"
            mathlib.mkdir()
            source_root.mkdir()
            (mathlib / "Foo.lean").write_text("namespace Foo\nend Foo\n")
            source = source_root / "Test.lean"
            source.write_text("namespace EpsilonEridani\nnamespace Foo\ndef bar (x : Foo) := x\n"
                              "end Foo\nend EpsilonEridani\n")
            baseline = pathlib.Path(directory) / "baseline.txt"
            baseline.write_text("")
            args = ["--mathlib-root", str(mathlib), "--source-root", str(source_root),
                    "--baseline", str(baseline)]
            stdout = io.StringIO()
            with contextlib.redirect_stdout(stdout):
                self.assertEqual(lint.main(args), 1)
                self.assertEqual(lint.main([*args, "--write-baseline"]), 0)
                source.write_text("namespace EpsilonEridani\ndef _root_.Foo.bar (x : Foo) := x\nend EpsilonEridani\n")
                self.assertEqual(lint.main(args), 0)
            self.assertIn("1 new", stdout.getvalue())
            self.assertIn("1 ratchetable", stdout.getvalue())


if __name__ == "__main__":
    unittest.main()
