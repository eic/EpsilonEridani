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
# Lorentz transformations with time-time entry one

An element of Physlib's subgroup `LorentzGroup.Rotations d` has time-time entry `1`
(`rotation_timeComponent_eq_one`). This module records the consequences of that entry for
every `Λ : LorentzGroup d` with time-time entry `1`, so for spatial reflections as well as
rotations: `Λ` is orthochronous (`isOrthochronous_of_timeComponent_eq_one`), the mixed
time-space entries vanish (`inl_inr_eq_zero_of_timeComponent_eq_one` and
`inr_inl_eq_zero_of_timeComponent_eq_one`), so `Λ` leaves the time component of every vector
unchanged (`timeComponent_smul_of_timeComponent_eq_one`), acts on the spatial part through its
spatial block alone (`spatialPart_smul_apply_of_timeComponent_eq_one`), and, since it also
preserves the Minkowski product, preserves the Euclidean norm of the spatial part
(`norm_spatialPart_smul_of_timeComponent_eq_one`). Hence such a `Λ` acts on
`EuclideanSpace ℝ (Fin d)` as the linear isometry equivalence `spatialLinearIsometryEquiv hΛ`,
`v ↦ (Λ • (0, v))ₛ`, through which it acts on the spatial part of every vector
(`spatialPart_smul_of_timeComponent_eq_one`).
-/

public section

namespace LorentzGroup

variable {d : ℕ}

/-- A rotation has time-time entry `1`. -/
@[simp]
theorem rotation_timeComponent_eq_one (Λ : Rotations d) :
    (Λ : LorentzGroup d).1 (Sum.inl 0) (Sum.inl 0) = 1 :=
  ((mem_rotations_iff _).1 Λ.2).1

/-- A Lorentz transformation with time-time entry `1` is orthochronous. -/
theorem isOrthochronous_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) : IsOrthochronous Λ := by
  rw [IsOrthochronous, hΛ]
  exact zero_le_one

/-- The space-time entries of a Lorentz transformation with time-time entry `1` vanish. -/
@[simp]
theorem inr_inl_eq_zero_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (j : Fin d) :
    Λ.1 (Sum.inr j) (Sum.inl 0) = 0 := by
  simpa [toVector_apply] using
    congrFun ((toVector_eq_basis_iff_timeComponent_eq_one Λ).mpr hΛ) (Sum.inr j)

/-- The time-space entries of a Lorentz transformation with time-time entry `1` vanish. -/
@[simp]
theorem inl_inr_eq_zero_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (j : Fin d) :
    Λ.1 (Sum.inl 0) (Sum.inr j) = 0 := by
  have hT : (transpose Λ).1 (Sum.inl 0) (Sum.inl 0) = 1 := by
    rw [transpose_val, Matrix.transpose_apply, hΛ]
  simpa [toVector_apply, transpose_val] using
    congrFun ((toVector_eq_basis_iff_timeComponent_eq_one (transpose Λ)).mpr hT) (Sum.inr j)

/-- A Lorentz transformation with time-time entry `1` leaves the time component of a vector
unchanged. -/
@[simp]
theorem timeComponent_smul_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (v : Lorentz.Vector d) :
    (Λ • v).timeComponent = v.timeComponent := by
  simp [Lorentz.Vector.timeComponent, Lorentz.Vector.smul_eq_sum, Fintype.sum_sum_type, hΛ,
    inl_inr_eq_zero_of_timeComponent_eq_one hΛ]

/-- A Lorentz transformation with time-time entry `1` acts on the spatial part of a vector
through its spatial block. -/
theorem spatialPart_smul_apply_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (v : Lorentz.Vector d) (j : Fin d) :
    (Λ • v).spatialPart j = ∑ k, Λ.1 (Sum.inr j) (Sum.inr k) * v.spatialPart k := by
  simp [Lorentz.Vector.smul_eq_sum, Fintype.sum_sum_type,
    inr_inl_eq_zero_of_timeComponent_eq_one hΛ]

/-- A Lorentz transformation with time-time entry `1` preserves the Euclidean norm of the
spatial part of a vector. -/
@[simp]
theorem norm_spatialPart_smul_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (v : Lorentz.Vector d) :
    ‖(Λ • v).spatialPart‖ = ‖v.spatialPart‖ := by
  have h := Lorentz.Vector.minkowskiProduct_invariant v v Λ
  rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub,
    Lorentz.Vector.minkowskiProduct_self_eq_sq_sub,
    timeComponent_smul_of_timeComponent_eq_one hΛ, sub_right_inj] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- The action of a Lorentz transformation `Λ` with time-time entry `1` on spatial vectors,
`v ↦ (Λ • (0, v))ₛ`, as a linear isometry equivalence of `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def spatialLinearIsometryEquiv {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) :
    EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := ((Lorentz.Vector.spatialCLM d).comp ((Lorentz.Vector.actionCLM Λ).comp
        Lorentz.Vector.ofSpatialComponent)).toLinearMap
      norm_map' v := by
        simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
          Function.comp_apply, Lorentz.Vector.spatialCLM_apply,
          Lorentz.Vector.actionCLM_apply, norm_spatialPart_smul_of_timeComponent_eq_one hΛ,
          Lorentz.Vector.spatialPart_ofSpatialComponent] }
    rfl

/-- The linear isometry equivalence of `Λ` sends `v` to the spatial part of `Λ • (0, v)`. -/
@[simp]
theorem spatialLinearIsometryEquiv_apply {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (v : EuclideanSpace ℝ (Fin d)) :
    spatialLinearIsometryEquiv hΛ v = (Λ • Lorentz.Vector.ofSpatialComponent v).spatialPart := by
  simp only [spatialLinearIsometryEquiv, LinearIsometry.coe_toLinearIsometryEquiv,
    LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_comp,
    Function.comp_apply, Lorentz.Vector.spatialCLM_apply,
    Lorentz.Vector.actionCLM_apply]

/-- A Lorentz transformation with time-time entry `1` acts on the spatial part of every vector
as its linear isometry equivalence. -/
theorem spatialPart_smul_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (v : Lorentz.Vector d) :
    (Λ • v).spatialPart = spatialLinearIsometryEquiv hΛ v.spatialPart := by
  ext j
  rw [spatialLinearIsometryEquiv_apply, spatialPart_smul_apply_of_timeComponent_eq_one hΛ,
    spatialPart_smul_apply_of_timeComponent_eq_one hΛ,
    Lorentz.Vector.spatialPart_ofSpatialComponent]

end LorentzGroup
