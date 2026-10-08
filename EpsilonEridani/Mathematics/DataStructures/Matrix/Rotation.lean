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

Mathlib has no explicit rotation matrix (the `GeneralLinearGroup` files list it as a TODO). It is
needed whenever a physical model mixes two real fields by an angle: the neutral electroweak gauge
fields `(W³, B)` are rotated into `(Z, A)` by the weak mixing angle, and the mass matrix is
diagonalised by conjugating with this rotation. The results here are the facts such a
diagonalisation uses: the action on vectors, the transpose as the inverse, the group law, and
membership in the special orthogonal group.

## Main results

* `Matrix.rotation_mulVec`: the rotation applied to a vector `w`, componentwise.
* `Matrix.rotation_zero`, `Matrix.rotation_mul_rotation`: the rotation by `0` is the identity,
  and composing rotations adds their angles.
* `Matrix.rotation_transpose`: the transpose of the rotation by `θ` is the rotation by `-θ`.
* `Matrix.det_rotation`: the rotation has determinant `1`.
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
theorem rotation_def (θ : ℝ) : rotation θ = !![cos θ, -sin θ; sin θ, cos θ] := by
  rw [rotation]

/-- The rotation by `θ` applied to a vector `w = (w₀, w₁)`. -/
@[simp]
theorem rotation_mulVec (θ : ℝ) (w : Fin 2 → ℝ) :
    rotation θ *ᵥ w = ![cos θ * w 0 - sin θ * w 1, sin θ * w 0 + cos θ * w 1] := by
  rw [rotation_def]
  ext i
  fin_cases i <;> simp [mulVec, vecHead, vecTail, sub_eq_add_neg]

/-- The rotation by `0` is the identity. -/
@[simp]
theorem rotation_zero : rotation 0 = 1 := by
  rw [rotation_def, one_fin_two]
  simp

/-- Composing the rotations by `θ` and `φ` gives the rotation by `θ + φ`. -/
@[simp]
theorem rotation_mul_rotation (θ φ : ℝ) : rotation θ * rotation φ = rotation (θ + φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation_def, mul_apply, Fin.sum_univ_two, cos_add, sin_add] <;> ring

/-- The transpose of the rotation by `θ` is the rotation by `-θ`, its inverse. -/
theorem rotation_transpose (θ : ℝ) : (rotation θ)ᵀ = rotation (-θ) := by
  rw [rotation_def, rotation_def, cos_neg, sin_neg, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The rotation matrix has determinant `1`. -/
@[simp]
theorem det_rotation (θ : ℝ) : (rotation θ).det = 1 := by
  rw [rotation_def, det_fin_two_of]
  linear_combination cos_sq_add_sin_sq θ

/-- The rotation matrix is orthogonal and has determinant `1`. -/
theorem rotation_mem_specialOrthogonalGroup (θ : ℝ) :
    rotation θ ∈ specialOrthogonalGroup (Fin 2) ℝ := by
  rw [rotation_def, of_mem_specialOrthogonalGroup_fin_two_iff, neg_sq]
  exact ⟨rfl, rfl, cos_sq_add_sin_sq θ⟩

end Matrix
end EpsilonEridani

end
