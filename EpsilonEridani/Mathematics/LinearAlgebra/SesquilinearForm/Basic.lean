/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Isometries of a bilinear form

The maps `f` preserving a bilinear form `B`, `LinearMap.IsOrthogonal B f`, contain the identity
(`LinearMap.isOrthogonal_id`) and are closed under composition (`LinearMap.IsOrthogonal.comp`).
The same holds for the stabilizer `LinearMap.BilinForm.IsPairStabilizer B a b` of a pair of
vectors inside the isometries (`LinearMap.BilinForm.isPairStabilizer_id`,
`LinearMap.BilinForm.IsPairStabilizer.comp`), which fixes every combination of the two vectors
(`LinearMap.BilinForm.IsPairStabilizer.apply_smul_add_smul`).
-/

public section

namespace LinearMap

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- The identity is an isometry of every bilinear form. -/
lemma isOrthogonal_id (B : BilinForm R M) : B.IsOrthogonal _root_.id := fun _ _ ↦ by
  rw [_root_.id_eq, _root_.id_eq]

/-- A composite of isometries of `B` is an isometry of `B`. -/
lemma IsOrthogonal.comp {f f' : M → M} (hf : B.IsOrthogonal f) (hf' : B.IsOrthogonal f') :
    B.IsOrthogonal (f ∘ f') := fun x y ↦ by
  rw [Function.comp_apply, Function.comp_apply, hf, hf']

namespace BilinForm

/-- A `B`-isometry fixing the two vectors `a` and `b`: an element of the stabilizer of the pair
`(a, b)` inside the isometry group of `B`. -/
structure IsPairStabilizer (B : BilinForm R M) (a b : M) (f : M →ₗ[R] M) : Prop where
  /-- `f` preserves the background form. -/
  isOrthogonal : B.IsOrthogonal f
  /-- `f` fixes the first vector of the pair. -/
  fixes_left : f a = a
  /-- `f` fixes the second vector of the pair. -/
  fixes_right : f b = b

/-- The identity stabilizes every pair. -/
lemma isPairStabilizer_id (B : BilinForm R M) (a b : M) :
    B.IsPairStabilizer a b LinearMap.id where
  isOrthogonal := by rw [LinearMap.id_coe]; exact isOrthogonal_id B
  fixes_left := rfl
  fixes_right := rfl

/-- The stabilizer of a pair is closed under composition. -/
lemma IsPairStabilizer.comp {a b : M} {f f' : M →ₗ[R] M}
    (hf : B.IsPairStabilizer a b f) (hf' : B.IsPairStabilizer a b f') :
    B.IsPairStabilizer a b (f ∘ₗ f') where
  isOrthogonal := by rw [LinearMap.coe_comp]; exact hf.isOrthogonal.comp hf'.isOrthogonal
  fixes_left := by rw [LinearMap.comp_apply, hf'.fixes_left, hf.fixes_left]
  fixes_right := by rw [LinearMap.comp_apply, hf'.fixes_right, hf.fixes_right]

/-- A stabilizer of the pair `(a, b)` fixes every combination of `a` and `b`. -/
lemma IsPairStabilizer.apply_smul_add_smul {a b : M} {f : M →ₗ[R] M}
    (hf : B.IsPairStabilizer a b f) (x y : R) : f (x • a + y • b) = x • a + y • b := by
  rw [map_add, map_smul, map_smul, hf.fixes_left, hf.fixes_right]

end BilinForm

end LinearMap
