/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The rotation matrix of the plane

The real `2 × 2` matrix `Matrix.rotation θ = !![cos θ, -sin θ; sin θ, cos θ]` of the
counterclockwise rotation of `ℝ²` by the angle `θ`.

## Main results

* `Matrix.rotation_mulVec`: the rotation applied to a vector `w`, componentwise.
* `Matrix.rotation_mem_specialOrthogonalGroup`: the rotation is orthogonal with determinant `1`.
-/

public section

namespace EpsilonEridani
namespace Matrix

open _root_.Matrix Real

/-- The rotation of the plane by the angle `θ`, `!![cos θ, -sin θ; sin θ, cos θ]`. -/
noncomputable def rotation (θ : ℝ) : _root_.Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

/-- The rotation matrix, entry by entry. -/
theorem rotation_eq (θ : ℝ) : rotation θ = !![cos θ, -sin θ; sin θ, cos θ] := by
  rw [rotation]

/-- The rotation by `θ` applied to a vector `w = (w₀, w₁)`. -/
theorem rotation_mulVec (θ : ℝ) (w : Fin 2 → ℝ) :
    rotation θ *ᵥ w = ![cos θ * w 0 - sin θ * w 1, sin θ * w 0 + cos θ * w 1] := by
  rw [rotation_eq]
  ext i
  fin_cases i <;> simp [mulVec, vecHead, vecTail, sub_eq_add_neg]

/-- The rotation matrix is orthogonal and has determinant `1`. -/
theorem rotation_mem_specialOrthogonalGroup (θ : ℝ) :
    rotation θ ∈ specialOrthogonalGroup (Fin 2) ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, rotation_eq]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two, ← sq, mul_comm]
  · rw [det_fin_two_of]
    linear_combination cos_sq_add_sin_sq θ

end Matrix
end EpsilonEridani

end
