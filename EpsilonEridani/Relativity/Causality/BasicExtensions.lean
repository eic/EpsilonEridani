/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions
public import Physlib.Relativity.Causality.Basic

/-!
# Extensions of the causal character of Lorentz vectors

Facts about `Physlib`'s causal character `Lorentz.Vector.causalCharacter` that go beyond
`Physlib`'s own API: the spatial part of a spacelike vector does not vanish
(`spatialPart_ne_zero_of_spaceLike`), a nonzero vector with vanishing time component is
spacelike (`causalCharacter_eq_spaceLike_of_timeComponent_eq_zero`), and the equal-time
projection `v - ofTemporalComponent v.timeComponent` of a vector with nonzero spatial part is
spacelike
(`causalCharacter_sub_ofTemporalComponent_timeComponent_eq_spaceLike_of_spatialPart_ne_zero`).
-/

public section

namespace Lorentz
namespace Vector

open scoped Lorentz.Vector

/-- The spatial part of a spacelike vector does not vanish: a spacelike vector is never purely
temporal. -/
lemma spatialPart_ne_zero_of_spaceLike {d : ℕ} (v : Vector d)
    (hv : causalCharacter v = CausalCharacter.spaceLike) : spatialPart v ≠ 0 := by
  intro h
  have h' : ⟪v, v⟫ₘ < 0 := (spaceLike_iff_norm_sq_neg v).mp hv
  rw [minkowskiProduct_self_eq_sq_sub, h, norm_zero] at h'
  nlinarith [sq_nonneg v.timeComponent]

/-- A nonzero Lorentz vector with vanishing time component is spacelike. -/
lemma causalCharacter_eq_spaceLike_of_timeComponent_eq_zero {d : ℕ} {v : Vector d}
    (h0 : v.timeComponent = 0) (hne : v ≠ 0) :
    causalCharacter v = CausalCharacter.spaceLike := by
  have hsp : spatialPart v ≠ 0 := fun h =>
    hne (eq_zero_of_timeComponent_of_spatialPart h0 h)
  refine (spaceLike_iff_norm_sq_neg v).mpr ?_
  rw [minkowskiProduct_self_eq_sq_sub, h0, zero_pow two_ne_zero, zero_sub, neg_lt_zero]
  exact pow_pos (norm_pos_iff.mpr hsp) 2

/-- The equal-time projection `v - v⁰ e₀` of a vector with nonzero spatial part is spacelike. -/
lemma causalCharacter_sub_ofTemporalComponent_timeComponent_eq_spaceLike_of_spatialPart_ne_zero
    {d : ℕ} (v : Vector d) (hv : spatialPart v ≠ 0) :
    causalCharacter (v - ofTemporalComponent v.timeComponent) = CausalCharacter.spaceLike :=
  causalCharacter_eq_spaceLike_of_timeComponent_eq_zero
    (timeComponent_sub_ofTemporalComponent_timeComponent v)
    (fun h => hv (by rw [← spatialPart_sub_ofTemporalComponent v v.timeComponent, h]; ext i; simp))

end Vector
end Lorentz
