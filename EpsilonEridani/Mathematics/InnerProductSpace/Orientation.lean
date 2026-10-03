/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# The standard orientation of Euclidean space

Mathlib attaches a volume form to every oriented finite-dimensional real inner product space and,
in dimension two, an area form `Orientation.areaForm`, with its antisymmetry, its invariance under
orientation-preserving isometries (`Orientation.areaForm_comp_linearIsometryEquiv`) and its
relations to the inner product. It does not single out an orientation of the coordinate space
`EuclideanSpace ℝ ι`. This file fixes the one given by the standard basis and computes the
resulting forms in coordinates: the volume form is the determinant of the coordinate matrix, and
on `EuclideanSpace ℝ (Fin 2)` the area form is the cross product `u₀ v₁ - u₁ v₀`.

## Main definitions

* `EuclideanSpace.orientation ι`: the orientation of `EuclideanSpace ℝ ι` given by its standard
  basis `EuclideanSpace.basisFun ι ℝ`.

## Main statements

* `EuclideanSpace.volumeForm_orientation_apply`: the volume form of the standard orientation is
  the determinant of the coordinate matrix.
* `EuclideanSpace.areaForm_orientation_apply`: in the plane, the area form of the standard
  orientation is `u 0 * v 1 - u 1 * v 0`.
-/

public section

namespace EuclideanSpace

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The standard orientation of `EuclideanSpace ℝ ι`: the orientation of its standard basis. -/
noncomputable def orientation : Orientation ℝ (EuclideanSpace ℝ ι) ι :=
  (basisFun ι ℝ).toBasis.orientation

theorem orientation_def : orientation ι = (basisFun ι ℝ).toBasis.orientation := (rfl)

/-- The volume form of the standard orientation is the determinant of the matrix whose `j`-th
column is the coordinate vector of `v j`. -/
theorem volumeForm_orientation_apply {n : ℕ} (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    (orientation (Fin n)).volumeForm v = (Matrix.of fun i j => v j i).det := by
  rw [Orientation.volumeForm_robust _ (basisFun (Fin n) ℝ) (orientation_def _).symm,
    Module.Basis.det_apply]
  congr 1

/-- In the plane, the area form of the standard orientation is the cross product
`u 0 * v 1 - u 1 * v 0`. -/
@[simp]
theorem areaForm_orientation_apply (u v : EuclideanSpace ℝ (Fin 2)) :
    (orientation (Fin 2)).areaForm u v = u 0 * v 1 - u 1 * v 0 := by
  rw [Orientation.areaForm_to_volumeForm, volumeForm_orientation_apply, Matrix.det_fin_two]
  simp [mul_comm]

end EuclideanSpace
