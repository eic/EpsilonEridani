/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Bounds

/-!
# Rapidity as the small-`x` evolution variable

High-energy evolution of the dipole amplitude runs in the rapidity

```
Y = log (x₀ / x),
```

the logarithm of the inverse momentum fraction measured from a fixed reference `x₀`. Rapidity
increases towards small `x`; it is distinct from the logarithm of the hard scale,
`log (Q² / Q₀²)`, which is the evolution variable of collinear factorisation.

This file defines `rapidity x₀ x` and proves the properties the evolution equations rely on:

* it is strictly antitone in `x` on `x > 0`, and tends to `+∞` as `x → 0⁺`;
* the reference point only shifts it by a constant, through the chain rule
  `rapidity x₀ x₁ + rapidity x₁ x = rapidity x₀ x`, so rapidity *differences* do not depend on the
  choice of `x₀`;
* `x ↦ rapidity x₀ x` is inverted by `Y ↦ x₀ exp (-Y)`;
* on the physical region of deep-inelastic scattering, where `0 < x ≤ 1`, the rapidity of the
  Bjorken variable is at least `log x₀`, and ordering in rapidity is reverse ordering in `x`.

## Main definitions

* `SmallX.rapidity`: the rapidity `log (x₀ / x)` of a momentum fraction `x`.

## Main results

* `SmallX.strictAntiOn_rapidity`: rapidity is strictly antitone on `x > 0`.
* `SmallX.rapidity_add_rapidity`: the chain rule for a change of reference.
* `SmallX.rapidity_mul_exp_neg` and `SmallX.mul_exp_neg_rapidity`: rapidity and `Y ↦ x₀ e^{-Y}`
  are mutually inverse.
* `SmallX.tendsto_rapidity_nhdsGT_zero`: rapidity grows without bound as `x → 0⁺`.
* `SmallX.log_le_rapidity`: on `0 < x ≤ 1` the rapidity is at least `log x₀`.
* `DisKinematics.BasicAssumptions.log_le_rapidity_xBj` and
  `DisKinematics.BasicAssumptions.rapidity_xBj_lt_rapidity_xBj_iff`: rapidity on the physical
  region of deep-inelastic scattering.

## References

* Y. V. Kovchegov and E. Levin, *Quantum Chromodynamics at High Energy*, Cambridge University
  Press (2012), chapter 3.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Filter Topology

/-- The rapidity `Y = log (x₀ / x)` of the momentum fraction `x`, measured from the reference
momentum fraction `x₀`. It increases towards small `x`. -/
def rapidity (x₀ x : ℝ) : ℝ := Real.log (x₀ / x)

lemma rapidity_def (x₀ x : ℝ) : rapidity x₀ x = Real.log (x₀ / x) := (rfl)

lemma rapidity_eq_log_sub_log {x₀ x : ℝ} (hx₀ : x₀ ≠ 0) (hx : x ≠ 0) :
    rapidity x₀ x = Real.log x₀ - Real.log x := by
  rw [rapidity_def, Real.log_div hx₀ hx]

/-- The reference momentum fraction has rapidity zero. -/
@[simp] lemma rapidity_self (x : ℝ) : rapidity x x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [rapidity_def]
  · rw [rapidity_def, div_self hx, Real.log_one]

/-- The chain rule for rapidities: measuring from `x₀` is measuring from `x₁` and then adding the
rapidity of `x₁` measured from `x₀`. In particular a change of reference shifts every rapidity by
the same constant. -/
lemma rapidity_add_rapidity {x₀ x₁ x : ℝ} (hx₀ : x₀ ≠ 0) (hx₁ : x₁ ≠ 0) (hx : x ≠ 0) :
    rapidity x₀ x₁ + rapidity x₁ x = rapidity x₀ x := by
  rw [rapidity_eq_log_sub_log hx₀ hx₁, rapidity_eq_log_sub_log hx₁ hx,
    rapidity_eq_log_sub_log hx₀ hx]
  ring

/-- Rapidity differences do not depend on the reference momentum fraction. -/
lemma rapidity_sub_rapidity {x₀ x x' : ℝ} (hx₀ : x₀ ≠ 0) (hx : x ≠ 0) (hx' : x' ≠ 0) :
    rapidity x₀ x - rapidity x₀ x' = rapidity x' x := by
  rw [← rapidity_add_rapidity hx₀ hx' hx]
  ring

/-- Rapidity is strictly antitone in the momentum fraction on `x > 0`. -/
lemma strictAntiOn_rapidity {x₀ : ℝ} (hx₀ : x₀ ≠ 0) : StrictAntiOn (rapidity x₀) (Set.Ioi 0) := by
  intro x hx x' hx' hlt
  rw [rapidity_eq_log_sub_log hx₀ (ne_of_gt hx), rapidity_eq_log_sub_log hx₀ (ne_of_gt hx')]
  have := Real.log_lt_log (Set.mem_Ioi.1 hx) hlt
  linarith

lemma rapidity_lt_rapidity_iff {x₀ x x' : ℝ} (hx₀ : x₀ ≠ 0) (hx : 0 < x) (hx' : 0 < x') :
    rapidity x₀ x < rapidity x₀ x' ↔ x' < x :=
  (strictAntiOn_rapidity hx₀).lt_iff_gt hx hx'

lemma rapidity_le_rapidity_iff {x₀ x x' : ℝ} (hx₀ : x₀ ≠ 0) (hx : 0 < x) (hx' : 0 < x') :
    rapidity x₀ x ≤ rapidity x₀ x' ↔ x' ≤ x :=
  (strictAntiOn_rapidity hx₀).le_iff_ge hx hx'

/-- A positive momentum fraction has positive rapidity exactly when it lies below the positive
reference. -/
lemma rapidity_pos_iff {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : 0 < x) : 0 < rapidity x₀ x ↔ x < x₀ := by
  rw [← rapidity_self x₀, rapidity_lt_rapidity_iff hx₀.ne' hx₀ hx]

/-- On `0 < x ≤ 1` the rapidity is at least `log x₀`. -/
lemma log_le_rapidity (x₀ : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    Real.log x₀ ≤ rapidity x₀ x := by
  rcases eq_or_ne x₀ 0 with rfl | hx₀
  · simp [rapidity_def]
  · rw [rapidity_eq_log_sub_log hx₀ hx.ne']
    linarith [Real.log_nonpos hx.le hx1]

/-- The momentum fraction at rapidity `Y` is `x₀ e^{-Y}`. -/
@[simp] lemma rapidity_mul_exp_neg {x₀ : ℝ} (hx₀ : x₀ ≠ 0) (Y : ℝ) :
    rapidity x₀ (x₀ * Real.exp (-Y)) = Y := by
  rw [rapidity_def, div_mul_cancel_left₀ hx₀, ← Real.exp_neg, neg_neg, Real.log_exp]

/-- A positive momentum fraction is recovered from its rapidity as `x = x₀ e^{-Y}`. -/
lemma mul_exp_neg_rapidity {x₀ x : ℝ} (hx₀ : 0 < x₀) (hx : 0 < x) :
    x₀ * Real.exp (-rapidity x₀ x) = x := by
  rw [rapidity_def, Real.exp_neg, Real.exp_log (div_pos hx₀ hx), inv_div,
    mul_div_cancel₀ _ hx₀.ne']

/-- Rapidity grows without bound towards small momentum fraction. -/
lemma tendsto_rapidity_nhdsGT_zero {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    Tendsto (rapidity x₀) (𝓝[>] 0) atTop := by
  have h : Tendsto (fun x => Real.log x₀ - Real.log x) (𝓝[>] 0) atTop := by
    simp only [sub_eq_add_neg]
    exact tendsto_atTop_add_const_left _ _ (tendsto_neg_atTop_iff.2 Real.tendsto_log_nhdsGT_zero)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (rapidity_eq_log_sub_log hx₀ (ne_of_gt hx)).symm

end SmallX

namespace Scattering.DIS.Kinematics.DisKinematics.BasicAssumptions

open SmallX

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- On the physical region of deep-inelastic scattering, where `0 < x ≤ 1`, the rapidity of the
Bjorken variable is at least `log x₀`. -/
lemma log_le_rapidity_xBj {g : Bilin V} {K : DisKinematics V} (h : BasicAssumptions g K)
    (x₀ : ℝ) : Real.log x₀ ≤ rapidity x₀ (K.xBj g) :=
  log_le_rapidity x₀ (xBj_pos g K h.q2_pos h.p_dot_q_pos)
    (xBj_le_one g K h.p_dot_q_pos h.q2_le_two_p_dot_q)

/-- On the physical region of deep-inelastic scattering, ordering two configurations by the
rapidity of their Bjorken variables reverses their ordering in `x`. -/
lemma rapidity_xBj_lt_rapidity_xBj_iff {g g' : Bilin V} {K K' : DisKinematics V}
    (h : BasicAssumptions g K) (h' : BasicAssumptions g' K') {x₀ : ℝ} (hx₀ : x₀ ≠ 0) :
    rapidity x₀ (K.xBj g) < rapidity x₀ (K'.xBj g') ↔ K'.xBj g' < K.xBj g :=
  rapidity_lt_rapidity_iff hx₀ (xBj_pos g K h.q2_pos h.p_dot_q_pos)
    (xBj_pos g' K' h'.q2_pos h'.p_dot_q_pos)

end Scattering.DIS.Kinematics.DisKinematics.BasicAssumptions

end QFT
end EpsilonEridani
