/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Basic

/-!
# Positivity of the Lorentz factor

Physlib's `LorentzGroup.γ β = 1 / √(1 - β²)` is the Lorentz factor of a boost with speed `β`.
This module records that it is strictly positive for every subluminal speed `|β| < 1`. That is
what makes a boost preserve the sign of the energy of an on-shell momentum.
-/

public section

namespace LorentzGroup

/-- The Lorentz factor of a subluminal speed is strictly positive. -/
theorem γ_pos {β : ℝ} (hβ : |β| < 1) : 0 < γ β := by
  have : 0 < 1 - β ^ 2 := sub_pos.2 ((sq_lt_one_iff_abs_lt_one β).2 hβ)
  unfold γ
  positivity

end LorentzGroup
