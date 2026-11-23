/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Apply
public import EpsilonEridani.Relativity.LorentzGroup.Boosts.BasicExtensions

/-!
# The sign of a boosted component

Physlib computes the components of a boosted four-vector: the boost with speed `β` along the
spatial axis `i` sends `pⁱ` to `γ β (pⁱ - β p⁰)` (`Lorentz.Vector.boost_inr_self_eq`). Since the
Lorentz factor is positive, the boosted component is positive exactly when `β p⁰ < pⁱ`. This is
what decides whether a boost along an axis can reverse the direction of a vector along that axis.

## Main statements

* `Lorentz.Vector.boost_inr_self_pos_iff`: `0 < (Λ p)ⁱ ↔ β p⁰ < pⁱ` for the boost `Λ` with speed
  `β` along the axis `i`.
-/

public section

namespace Lorentz.Vector

open LorentzGroup

variable {d : ℕ}

/-- The component of a boosted four-vector along the boost axis is positive exactly when
`β p⁰ < pⁱ`. -/
lemma boost_inr_self_pos_iff (i : Fin d) {β : ℝ} (hβ : |β| < 1) (p : Vector d) :
    0 < (boost i β hβ • p) (Sum.inr i) ↔ β * p (Sum.inl 0) < p (Sum.inr i) := by
  rw [boost_inr_self_eq, mul_pos_iff_of_pos_left (γ_pos hβ), sub_pos]

end Lorentz.Vector
