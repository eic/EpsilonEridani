/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.Reflection
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Splitting a vector space along a pair of vectors

For a bilinear form `g` on a vector space `V` over a field `K` and a pair of vectors `(a, b)`,
this file records two properties of the vectors `g`-orthogonal to both `a` and `b` (in physics
applications, the *spectator* directions of a pair of momenta), and what they say about the
vectors fixed by the stabilizer of the pair.

## Main definitions

* `LinearMap.BilinForm.IsOrthogonalSplit g a b`: every vector is a combination of `a` and `b`
  plus a vector `g`-orthogonal to both.
* `LinearMap.BilinForm.IsAnisotropicOrthogonal g a b`: no non-zero vector `g`-orthogonal to both
  `a` and `b` is `g`-null.

## Main statements

* `LinearMap.BilinForm.isOrthogonalSplit_of_gramDet_ne_zero`: a pair with non-zero Gram
  determinant splits `V`, by Cramer's rule.
* `LinearMap.BilinForm.IsOrthogonalSplit.symm`, `IsAnisotropicOrthogonal.symm`: both properties
  are independent of the order of the pair.
* `LinearMap.BilinForm.apply_eq_zero_of_forall_isPairStabilizer`: a vector fixed by the
  stabilizer `IsPairStabilizer g a b` is `g`-orthogonal to every non-null vector orthogonal to `a`
  and `b`, since the reflection in that vector lies in the stabilizer.
* `LinearMap.BilinForm.IsOrthogonalSplit.exists_eq_smul_add_smul`: under both properties, a vector
  fixed by the stabilizer of the pair is a combination of `a` and `b`.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The pair `(a, b)` splits `V`: every vector is a combination of `a` and `b` plus a vector
`g`-orthogonal to both. -/
structure IsOrthogonalSplit (g : BilinForm K V) (a b : V) : Prop where
  /-- Every vector is a combination of `a` and `b` plus a vector `g`-orthogonal to both. -/
  span : ∀ v : V, ∃ (x y : K) (u : V), g a u = 0 ∧ g b u = 0 ∧ v = x • a + y • b + u

/-- The splitting does not depend on the order of the pair. -/
lemma IsOrthogonalSplit.symm {g : BilinForm K V} {a b : V} (h : g.IsOrthogonalSplit a b) :
    g.IsOrthogonalSplit b a where
  span v := by
    obtain ⟨x, y, u, hau, hbu, rfl⟩ := h.span v
    exact ⟨y, x, u, hbu, hau, by abel⟩

/-- Two vectors with non-zero Gram determinant split `V`: the coefficients of `v` solve the
linear system `g a v = x g a a + y g a b`, `g b v = x g b a + y g b b` by Cramer's rule, and the
remainder is `g`-orthogonal to both. -/
lemma isOrthogonalSplit_of_gramDet_ne_zero (g : BilinForm K V) {a b : V}
    (h : g a a * g b b - g a b * g b a ≠ 0) : g.IsOrthogonalSplit a b := by
  have h' : g b b * g a a - g a b * g b a ≠ 0 := by rwa [mul_comm (g b b)]
  refine ⟨fun v => ?_⟩
  set x := (g a v * g b b - g a b * g b v) / (g a a * g b b - g a b * g b a)
  set y := (g a a * g b v - g b a * g a v) / (g a a * g b b - g a b * g b a)
  refine ⟨x, y, v - x • a - y • b, ?_, ?_, by abel⟩
  · simp only [map_sub, map_smul, smul_eq_mul, x, y]
    field_simp [h']
    ring
  · simp only [map_sub, map_smul, smul_eq_mul, x, y]
    field_simp [h']
    ring

/-- No non-zero vector `g`-orthogonal to both `a` and `b` is `g`-null, so the reflection in it
(`LinearMap.BilinForm.reflection`) reverses it. -/
structure IsAnisotropicOrthogonal (g : BilinForm K V) (a b : V) : Prop where
  /-- A non-zero vector `g`-orthogonal to both `a` and `b` is not `g`-null. -/
  apply_self_ne_zero : ∀ u : V, g a u = 0 → g b u = 0 → u ≠ 0 → g u u ≠ 0

/-- Anisotropy does not depend on the order of the pair. -/
lemma IsAnisotropicOrthogonal.symm {g : BilinForm K V} {a b : V}
    (h : g.IsAnisotropicOrthogonal a b) : g.IsAnisotropicOrthogonal b a :=
  ⟨fun u hbu hau hu => h.apply_self_ne_zero u hau hbu hu⟩

/-- A vector `v` fixed by every element of the stabilizer of `(a, b)` is `g`-orthogonal to every
non-null `u` orthogonal to `a` and `b`: the reflection in `u` lies in the stabilizer and moves `v`
by a multiple of `g u v`. -/
lemma apply_eq_zero_of_forall_isPairStabilizer {g : BilinForm K V} (h2 : (2 : K) ≠ 0)
    (hSymm : g.IsSymm) {a b u v : V} (hv : ∀ f, g.IsPairStabilizer a b f → f v = v)
    (hu : g u u ≠ 0) (hau : g a u = 0) (hbu : g b u = 0) : g u v = 0 := by
  have h := hv _ (g.reflection_isPairStabilizer hSymm u (by rwa [hSymm.eq]) (by rwa [hSymm.eq]))
  rw [reflection_apply, sub_eq_self, smul_eq_zero] at h
  rcases h with h | h
  · simpa [h2, hu] using h
  · simp [h] at hu

/-- **Vectors fixed by the stabilizer of a pair.** If `(a, b)` splits `V` and no non-zero vector
orthogonal to both is null, then a vector fixed by every element of the stabilizer of `(a, b)` is
a combination of `a` and `b`. -/
theorem IsOrthogonalSplit.exists_eq_smul_add_smul {g : BilinForm K V} {a b : V}
    (hS : g.IsOrthogonalSplit a b) (han : g.IsAnisotropicOrthogonal a b) (h2 : (2 : K) ≠ 0)
    (hSymm : g.IsSymm) {v : V} (hv : ∀ f, g.IsPairStabilizer a b f → f v = v) :
    ∃ x y : K, v = x • a + y • b := by
  obtain ⟨x, y, u, hau, hbu, rfl⟩ := hS.span v
  by_cases hu : u = 0
  · exact ⟨x, y, by rw [hu, add_zero]⟩
  have huu := han.apply_self_ne_zero u hau hbu hu
  have h := apply_eq_zero_of_forall_isPairStabilizer h2 hSymm hv huu hau hbu
  have hua : g u a = 0 := by rwa [hSymm.eq]
  have hub : g u b = 0 := by rwa [hSymm.eq]
  simp only [map_add, map_smul, hua, hub, smul_zero, zero_add] at h
  exact absurd h huu

end LinearMap.BilinForm
