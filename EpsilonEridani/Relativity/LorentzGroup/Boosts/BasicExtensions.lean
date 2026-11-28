/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Basic
public import Physlib.Relativity.LorentzGroup.Orthochronous.Basic

/-!
# Positivity of the Lorentz factor

Physlib's `LorentzGroup.γ β = 1 / √(1 - β²)` is the Lorentz factor of a boost with speed `β`.
This module records that it is strictly positive for every subluminal speed `|β| < 1`
(`γ_pos`). The time-time entry of a boost is `γ β`, so positivity of `γ` makes a boost
orthochronous (`isOrthochronous_boost`), keeping the energy of an on-shell momentum
non-negative.
-/

public section

namespace LorentzGroup

/-- The Lorentz factor of a subluminal speed is strictly positive. -/
theorem γ_pos {β : ℝ} (hβ : |β| < 1) : 0 < γ β := by
  have : 0 < 1 - β ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one β).2 hβ)
  unfold γ
  positivity

/-- A boost along a coordinate axis is orthochronous. -/
theorem isOrthochronous_boost {d : ℕ} (i : Fin d) {β : ℝ} (hβ : |β| < 1) :
    IsOrthochronous (boost i β hβ) := by
  rw [IsOrthochronous, boost_inl_0_inl_0]
  exact (γ_pos hβ).le

end LorentzGroup
