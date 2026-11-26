/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring

/-!
# The value of a bilinear form on shifted vectors

For a bilinear form `B` over a commutative ring, the value `B (x - a u) (y - b u)` on a pair of
vectors each shifted along a common vector `u` is expanded bilinearly. As special cases, the value
`B (u - z v) (u - z v)` of the difference with a rescaled second vector is expanded about the value
`B (u - v) (u - v)` of the plain difference, and likewise for `B (z u - v) (z u - v)`. No symmetry
of `B` and no condition on `B u u` or `B v v` is needed.

In the kinematics of radiative deep inelastic scattering the special cases give the virtuality
`-(z k - k')²` after collinear emission of the fraction `1 - z` of a lepton momentum, in terms of
the virtuality `-(k - k')²` computed from the lepton momenta before the emission.

## Main statements

* `LinearMap.BilinForm.apply_sub_smul_sub_smul`:
  `B (x - a u) (y - b u) = B x y - b B x u - a B u y + a b B u u`.
* `LinearMap.BilinForm.apply_sub_smul_self`:
  `B (u - z v) (u - z v) = z B (u - v) (u - v) + (1 - z) (B u u - z B v v)`.
* `LinearMap.BilinForm.apply_smul_sub_self`:
  `B (z u - v) (z u - v) = z B (u - v) (u - v) + (1 - z) (B v v - z B u u)`.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Expansion of a bilinear form on a pair of vectors each shifted along `u`. -/
theorem apply_sub_smul_sub_smul (B : BilinForm R M) (u x y : M) (a b : R) :
    B (x - a • u) (y - b • u) = B x y - b * B x u - a * B u y + a * b * B u u := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The expansion of `B (u - z v) (u - z v)` about `B (u - v) (u - v)`. -/
theorem apply_sub_smul_self (B : BilinForm R M) (u v : M) (z : R) :
    B (u - z • v) (u - z • v) = z * B (u - v) (u - v) + (1 - z) * (B u u - z * B v v) := by
  have h := apply_sub_smul_sub_smul B v u u 1 1
  rw [one_smul] at h
  rw [apply_sub_smul_sub_smul, h]
  ring

/-- The expansion of `B (z u - v) (z u - v)` about `B (u - v) (u - v)`. -/
theorem apply_smul_sub_self (B : BilinForm R M) (u v : M) (z : R) :
    B (z • u - v) (z • u - v) = z * B (u - v) (u - v) + (1 - z) * (B v v - z * B u u) := by
  rw [← neg_sub v (z • u), ← neg_sub v u]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  exact apply_sub_smul_self B v u z

end LinearMap.BilinForm
