/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The inner product of `EuclideanSpace` in coordinates

Mathlib puts the `L²` inner product space structure on finite products of inner product spaces in
`Mathlib.Analysis.InnerProductSpace.PiL2`: the inner product of `EuclideanSpace 𝕜 ι` is the sum
`∑ i, ⟪x i, y i⟫` of the componentwise inner products (`PiLp.inner_apply`). Over the reals the
conjugations vanish, so the inner product of `EuclideanSpace ℝ ι` is the plain sum of products
of components. This file records that coordinate form, in which the plane
`EuclideanSpace ℝ (Fin 2)` is used as the transverse plane of scattering kinematics.

## Main statements

* `EuclideanSpace.real_inner_eq_sum`: the inner product of `EuclideanSpace ℝ ι` in coordinates,
  `∑ i, u i * v i`.
-/

@[expose] public section

namespace EuclideanSpace

/-- The inner product of `EuclideanSpace ℝ ι` in coordinates: `∑ i, u i * v i`. -/
theorem real_inner_eq_sum {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℝ ι) :
    inner ℝ u v = ∑ i, u i * v i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_comm]

end EuclideanSpace
