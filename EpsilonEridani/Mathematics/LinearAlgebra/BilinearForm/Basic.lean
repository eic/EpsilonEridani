/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Tactic.Ring

/-!
# The value of a bilinear form on a rescaled difference

For a bilinear form `B` over a commutative ring, the value `B (z u - v) (z u - v)` of the
difference with a rescaled first vector is expanded about the value `B (u - v) (u - v)` of the
plain difference, and likewise for `B (u - z v) (u - z v)`. No symmetry of `B` and no condition on
`B u u` or `B v v` is needed.

In the kinematics of radiative deep inelastic scattering these give the virtuality `-(z k - k')²`
after collinear emission of the fraction `1 - z` of a lepton momentum, in terms of the
virtuality `-(k - k')²` computed from the lepton momenta before the emission.

## Main statements

* `LinearMap.BilinForm.apply_smul_sub_self`:
  `B (z u - v) (z u - v) = z B (u - v) (u - v) + (1 - z) (B v v - z B u u)`.
* `LinearMap.BilinForm.apply_sub_smul_self`:
  `B (u - z v) (u - z v) = z B (u - v) (u - v) + (1 - z) (B u u - z B v v)`.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The expansion of `B (z u - v) (z u - v)` about `B (u - v) (u - v)`. -/
theorem apply_smul_sub_self (B : BilinForm R M) (u v : M) (z : R) :
    B (z • u - v) (z • u - v) = z * B (u - v) (u - v) + (1 - z) * (B v v - z * B u u) := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The expansion of `B (u - z v) (u - z v)` about `B (u - v) (u - v)`. -/
theorem apply_sub_smul_self (B : BilinForm R M) (u v : M) (z : R) :
    B (u - z • v) (u - z • v) = z * B (u - v) (u - v) + (1 - z) * (B u u - z * B v v) := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

end LinearMap.BilinForm
