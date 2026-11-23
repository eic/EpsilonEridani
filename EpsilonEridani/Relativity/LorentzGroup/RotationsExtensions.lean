/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Rotations
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions

/-!
# Rotations fix the time axis

An element of Physlib's subgroup `LorentzGroup.Rotations d` has time-time entry `1`. This module
records the consequences for the rest of its first row and column: the mixed time-space entries
vanish (`rotation_inl_inr_eq_zero` and `rotation_inr_inl_eq_zero`), so a rotation leaves the time
component of every vector unchanged (`timeComponent_rotation_smul`), acts on the spatial part
through its spatial block alone (`spatialPart_rotation_smul_apply`), and, since it also preserves
the Minkowski product, preserves the Euclidean norm of the spatial part
(`norm_spatialPart_rotation_smul`). Hence a rotation acts on `EuclideanSpace ℝ (Fin d)` as the
linear isometry equivalence `Rotations.toLinearIsometryEquiv Λ`, `v ↦ (Λ • (0, v))ₛ`, through
which it acts on the spatial part of every vector (`spatialPart_rotation_smul`).
-/

public section

namespace LorentzGroup

variable {d : ℕ}

/-- The space-time entries of a rotation vanish. -/
@[simp]
theorem rotation_inr_inl_eq_zero (Λ : Rotations d) (j : Fin d) :
    (Λ : LorentzGroup d).1 (Sum.inr j) (Sum.inl 0) = 0 := by
  simpa [toVector_apply] using congrFun (toVector_rotation Λ) (Sum.inr j)

/-- The time-space entries of a rotation vanish. -/
@[simp]
theorem rotation_inl_inr_eq_zero (Λ : Rotations d) (j : Fin d) :
    (Λ : LorentzGroup d).1 (Sum.inl 0) (Sum.inr j) = 0 := by
  simpa [toVector_apply, transpose_val] using
    congrFun (toVector_rotation ⟨transpose Λ.1, (transpose_mem_rotations _).2 Λ.2⟩) (Sum.inr j)

/-- A rotation leaves the time component of a vector unchanged. -/
@[simp]
theorem timeComponent_rotation_smul (Λ : Rotations d) (v : Lorentz.Vector d) :
    ((Λ : LorentzGroup d) • v).timeComponent = v.timeComponent := by
  have h00 := ((mem_rotations_iff _).1 Λ.2).1
  simp [Lorentz.Vector.timeComponent, Lorentz.Vector.smul_eq_sum, Fintype.sum_sum_type, h00]

/-- A rotation acts on the spatial part of a vector through its spatial block. -/
theorem spatialPart_rotation_smul_apply (Λ : Rotations d) (v : Lorentz.Vector d) (j : Fin d) :
    ((Λ : LorentzGroup d) • v).spatialPart j =
      ∑ k, (Λ : LorentzGroup d).1 (Sum.inr j) (Sum.inr k) * v.spatialPart k := by
  simp [Lorentz.Vector.smul_eq_sum, Fintype.sum_sum_type]

/-- A rotation preserves the Euclidean norm of the spatial part of a vector. -/
@[simp]
theorem norm_spatialPart_rotation_smul (Λ : Rotations d) (v : Lorentz.Vector d) :
    ‖((Λ : LorentzGroup d) • v).spatialPart‖ = ‖v.spatialPart‖ := by
  have h := Lorentz.Vector.minkowskiProduct_invariant v v (Λ : LorentzGroup d)
  rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub,
    Lorentz.Vector.minkowskiProduct_self_eq_sq_sub, timeComponent_rotation_smul, sub_right_inj] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- The action of a rotation `Λ` on spatial vectors, `v ↦ (Λ • (0, v))ₛ`, as a linear isometry
equivalence of `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def Rotations.toLinearIsometryEquiv (Λ : Rotations d) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := ((Lorentz.Vector.spatialCLM d).comp ((Lorentz.Vector.actionCLM Λ).comp
        Lorentz.Vector.ofSpatialComponent)).toLinearMap
      norm_map' v := by
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
          Function.comp_apply, Lorentz.Vector.spatialCLM_apply,
          Lorentz.Vector.actionCLM_apply, norm_spatialPart_rotation_smul,
          Lorentz.Vector.spatialPart_ofSpatialComponent] }
    rfl

/-- The linear isometry equivalence of a rotation sends `v` to the spatial part of
`Λ • (0, v)`. -/
@[simp]
theorem Rotations.toLinearIsometryEquiv_apply (Λ : Rotations d) (v : EuclideanSpace ℝ (Fin d)) :
    Rotations.toLinearIsometryEquiv Λ v =
      ((Λ : LorentzGroup d) • Lorentz.Vector.ofSpatialComponent v).spatialPart := by
  simp only [Rotations.toLinearIsometryEquiv, LinearIsometry.coe_toLinearIsometryEquiv,
    LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
    Function.comp_apply, Lorentz.Vector.spatialCLM_apply,
    Lorentz.Vector.actionCLM_apply]

/-- A rotation acts on the spatial part of every vector as its linear isometry equivalence. -/
theorem spatialPart_rotation_smul (Λ : Rotations d) (v : Lorentz.Vector d) :
    ((Λ : LorentzGroup d) • v).spatialPart = Rotations.toLinearIsometryEquiv Λ v.spatialPart := by
  ext j
  rw [Rotations.toLinearIsometryEquiv_apply, spatialPart_rotation_smul_apply,
    spatialPart_rotation_smul_apply, Lorentz.Vector.spatialPart_ofSpatialComponent]

end LorentzGroup
