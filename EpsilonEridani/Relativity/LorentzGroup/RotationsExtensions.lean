/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Rotations

/-!
# Rotations fix the time axis

An element of Physlib's subgroup `LorentzGroup.Rotations d` has time-time entry `1`. This module
records the consequences for the rest of its first row and column: the mixed time-space entries
vanish (`rotations_inl_0_inr` and `rotations_inr_inl_0`), so a rotation leaves the time component
of every vector unchanged (`timeComponent_rotations_smul`) and acts on the spatial part through
its spatial block alone (`spatialPart_rotations_smul_apply`).
-/

public section

namespace LorentzGroup

variable {d : ℕ}

/-- The space-time entries of a rotation vanish. -/
theorem rotations_inr_inl_0 (Λ : Rotations d) (j : Fin d) :
    (Λ : LorentzGroup d).1 (Sum.inr j) (Sum.inl 0) = 0 := by
  simpa [toVector_apply] using congrFun (toVector_rotation Λ) (Sum.inr j)

/-- The time-space entries of a rotation vanish. -/
theorem rotations_inl_0_inr (Λ : Rotations d) (j : Fin d) :
    (Λ : LorentzGroup d).1 (Sum.inl 0) (Sum.inr j) = 0 := by
  simpa [toVector_apply, transpose_val] using
    congrFun (toVector_rotation ⟨transpose Λ.1, (transpose_mem_rotations _).2 Λ.2⟩) (Sum.inr j)

/-- A rotation leaves the time component of a vector unchanged. -/
@[simp]
theorem timeComponent_rotations_smul (Λ : Rotations d) (v : Lorentz.Vector d) :
    ((Λ : LorentzGroup d) • v).timeComponent = v.timeComponent := by
  have h00 := ((mem_rotations_iff _).1 Λ.2).1
  simp [Lorentz.Vector.timeComponent, Lorentz.Vector.smul_eq_mulVec, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, h00, rotations_inl_0_inr]

/-- A rotation acts on the spatial part of a vector through its spatial block. -/
theorem spatialPart_rotations_smul_apply (Λ : Rotations d) (v : Lorentz.Vector d) (j : Fin d) :
    ((Λ : LorentzGroup d) • v).spatialPart j =
      ∑ k, (Λ : LorentzGroup d).1 (Sum.inr j) (Sum.inr k) * v.spatialPart k := by
  simp [Lorentz.Vector.smul_eq_mulVec, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    rotations_inr_inl_0]

end LorentzGroup
