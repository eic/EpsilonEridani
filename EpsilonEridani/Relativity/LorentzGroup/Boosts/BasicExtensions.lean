/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Basic

/-!
# Positivity of the Lorentz factor

Physlib defines the Lorentz factor `LorentzGroup.γ β = 1 / √(1 - β²)` and records its square and
its values at `0` and `-β`. This file adds that it is positive for a speed `|β| < 1`, so that a
boost rescales components by factors of a definite sign.

## Main statements

* `LorentzGroup.γ_pos`: `0 < γ β` for `|β| < 1`.
-/

public section

namespace LorentzGroup

/-- The Lorentz factor of a speed `|β| < 1` is positive. -/
lemma γ_pos {β : ℝ} (hβ : |β| < 1) : 0 < γ β := by
  rw [γ, one_div_pos, Real.sqrt_pos, sub_pos, sq_lt_one_iff_abs_lt_one]
  exact hβ

end LorentzGroup
