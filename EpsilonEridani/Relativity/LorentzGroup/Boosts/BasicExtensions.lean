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
its values at `0` and `-β`. This file adds that it is positive for a speed `|β| < 1`, and so are the
factors `γ (1 - β)` and `γ (1 + β)`. These are the rescalings of the light-front components
`p⁺` and `p⁻` under a boost with speed `β` along the boost axis, and their positivity says that
such a boost preserves the signs of both components.

## Main statements

* `LorentzGroup.γ_pos`: `0 < γ β` for `|β| < 1`.
* `LorentzGroup.γ_mul_one_sub_pos`, `LorentzGroup.γ_mul_one_add_pos`: `0 < γ β (1 - β)` and
  `0 < γ β (1 + β)` for `|β| < 1`.
-/

public section

namespace LorentzGroup

/-- The Lorentz factor of a speed `|β| < 1` is positive. -/
lemma γ_pos {β : ℝ} (hβ : |β| < 1) : 0 < γ β := by
  rw [γ, one_div_pos, Real.sqrt_pos, sub_pos, sq_lt_one_iff_abs_lt_one]
  exact hβ

/-- The factor `γ (1 - β)` by which a boost with speed `|β| < 1` rescales the plus light-front
component is positive. -/
lemma γ_mul_one_sub_pos {β : ℝ} (hβ : |β| < 1) : 0 < γ β * (1 - β) :=
  mul_pos (γ_pos hβ) (sub_pos.2 (abs_lt.1 hβ).2)

/-- The factor `γ (1 + β)` by which a boost with speed `|β| < 1` rescales the minus light-front
component is positive. -/
lemma γ_mul_one_add_pos {β : ℝ} (hβ : |β| < 1) : 0 < γ β * (1 + β) :=
  mul_pos (γ_pos hβ) (by linarith [(abs_lt.1 hβ).1])

end LorentzGroup
