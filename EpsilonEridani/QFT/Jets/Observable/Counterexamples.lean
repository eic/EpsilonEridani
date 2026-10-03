/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Jets.Observable.Basic

/-!
# Unsafe observables

The safety conditions of `EpsilonEridani.QFT.Jets.Observable.Basic` are only meaningful together
with observables that fail them. This file records the two standard ones.

* The particle multiplicity `s ↦ (Multiset.card s : ℝ)` is neither collinear safe
  (`not_isCollinearSafe_card`) nor infrared safe (`not_isInfraredSafe_card`): a collinear
  splitting and a soft addition each add exactly one particle.
* The leading-particle energy `leadingEnergy E`, the largest value of an energy function `E`
  over the particles of a final state, is infrared safe whenever `E p → 0` as `p → 0`
  (`isInfraredSafe_leadingEnergy`), but for a nonzero linear energy functional it is not collinear
  safe (`not_isCollinearSafe_leadingEnergy`): splitting a single particle of energy `E p ≥ 0`
  with fraction `z` lowers the leading energy to `max z (1 - z) * E p`
  (`leadingEnergy_splitCollinear_singleton`), so already `z = 1 / 2` witnesses the failure.

## References

* G. Sterman and S. Weinberg, *Jets from Quantum Chromodynamics*,
  Phys. Rev. Lett. 39 (1977) 1436.
* G. P. Salam, *Towards jetography*, Eur. Phys. J. C 67 (2010) 637, §2.
-/

public section

namespace EpsilonEridani.QFT.Jets

open Filter Topology

variable {V : Type*}

/-! ### Multiplicity -/

/-- The particle multiplicity is not collinear safe: splitting a particle adds one. -/
theorem not_isCollinearSafe_card [AddCommGroup V] [Module ℝ V] [DecidableEq V] :
    ¬ IsCollinearSafe (fun s : Multiset V => (Multiset.card s : ℝ)) := by
  intro h
  have := h.apply_splitCollinear (Multiset.mem_singleton_self (0 : V))
    (z := 0) ⟨le_rfl, zero_le_one⟩
  simp [card_splitCollinear 0 (Multiset.mem_singleton_self (0 : V))] at this

/-- The particle multiplicity is not infrared safe: adding a momentum, however soft, adds one
particle. -/
theorem not_isInfraredSafe_card [Zero V] [TopologicalSpace V] :
    ¬ IsInfraredSafe (fun s : Multiset V => (Multiset.card s : ℝ)) := by
  intro h
  have := h.tendsto 0
  simp only [Multiset.card_cons, Multiset.card_zero, zero_add, Nat.cast_one,
    Nat.cast_zero] at this
  exact one_ne_zero (tendsto_const_nhds_iff.1 this)

/-! ### The leading-particle energy -/

/-- The leading-particle energy of a final state: the largest value of the energy function `E`
over its particles. The value on the empty final state is `0`, so that for a nonnegative energy
function this is the energy of the most energetic particle. -/
noncomputable def leadingEnergy (E : V → ℝ) : Observable V :=
  fun s => (s.map E).fold max 0

@[simp]
theorem leadingEnergy_zero (E : V → ℝ) : leadingEnergy E 0 = 0 :=
  (rfl)

@[simp]
theorem leadingEnergy_cons (E : V → ℝ) (p : V) (s : Multiset V) :
    leadingEnergy E (p ::ₘ s) = max (E p) (leadingEnergy E s) := by
  simp [leadingEnergy, Multiset.fold_cons_left]

@[simp]
theorem leadingEnergy_singleton (E : V → ℝ) (p : V) : leadingEnergy E {p} = max (E p) 0 := by
  rw [← Multiset.cons_zero, leadingEnergy_cons, leadingEnergy_zero]

/-- The leading-particle energy is the least upper bound of `0` and the particle energies. -/
theorem leadingEnergy_le_iff {E : V → ℝ} {s : Multiset V} {c : ℝ} :
    leadingEnergy E s ≤ c ↔ 0 ≤ c ∧ ∀ p ∈ s, E p ≤ c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih => simp [ih, and_left_comm]

theorem leadingEnergy_nonneg (E : V → ℝ) (s : Multiset V) : 0 ≤ leadingEnergy E s :=
  (leadingEnergy_le_iff.1 le_rfl).1

theorem le_leadingEnergy {E : V → ℝ} {s : Multiset V} {p : V} (hp : p ∈ s) :
    E p ≤ leadingEnergy E s :=
  (leadingEnergy_le_iff.1 le_rfl).2 p hp

/-- The leading-particle energy is infrared safe for an energy function that vanishes in the
limit of vanishing momentum. -/
theorem isInfraredSafe_leadingEnergy [Zero V] [TopologicalSpace V] {E : V → ℝ}
    (hE : Tendsto E (𝓝 0) (𝓝 0)) : IsInfraredSafe (leadingEnergy E) := by
  refine isInfraredSafe_iff.2 fun s => ?_
  simp only [leadingEnergy_cons]
  simpa [max_eq_right (leadingEnergy_nonneg E s)] using
    hE.max (tendsto_const_nhds (x := leadingEnergy E s))

section Linear

variable [AddCommGroup V] [Module ℝ V] [DecidableEq V]

/-- Splitting a single particle of nonnegative energy `E p` with fraction `z ∈ [0, 1]` lowers the
leading-particle energy from `E p` to `max z (1 - z) * E p`. -/
theorem leadingEnergy_splitCollinear_singleton (E : V →ₗ[ℝ] ℝ) {p : V} (hp : 0 ≤ E p) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    leadingEnergy E (splitCollinear p z {p}) = max z (1 - z) * E p := by
  rw [← Multiset.cons_zero, splitCollinear_cons_self]
  have h₂ : 0 ≤ (1 - z) * E p := mul_nonneg (sub_nonneg.2 hz.2) hp
  simp [max_mul_of_nonneg _ _ hp, max_eq_left h₂]

/-- The leading-particle energy of a nonzero linear energy functional is not collinear safe:
splitting a single particle of positive energy into two halves halves the leading energy. -/
theorem not_isCollinearSafe_leadingEnergy {E : V →ₗ[ℝ] ℝ} (hE : E ≠ 0) :
    ¬ IsCollinearSafe (leadingEnergy E) := by
  intro h
  -- A particle of positive energy exists, since `E ≠ 0` and `E (-p) = -E p`.
  obtain ⟨p, hp⟩ : ∃ p, 0 < E p := by
    obtain ⟨q, hq⟩ := DFunLike.ne_iff.1 hE
    rcases (Ne.lt_or_gt hq : E q < 0 ∨ 0 < E q) with hq | hq
    · exact ⟨-q, by simpa using hq⟩
    · exact ⟨q, hq⟩
  have hz : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := h.apply_splitCollinear (Multiset.mem_singleton_self p) hz
  rw [leadingEnergy_splitCollinear_singleton E hp.le hz, leadingEnergy_singleton,
    max_eq_left hp.le] at this
  norm_num at this
  linarith

end Linear

end EpsilonEridani.QFT.Jets
