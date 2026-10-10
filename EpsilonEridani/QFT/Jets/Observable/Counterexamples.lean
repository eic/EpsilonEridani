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

* The particle multiplicity `multiplicity s = (Multiset.card s : ℝ)` is neither collinear safe
  (`not_isCollinearSafe_multiplicity`) nor infrared safe (`not_isInfraredSafe_multiplicity`): a
  collinear splitting and a soft addition each add exactly one particle.
* The leading-particle energy `leadingEnergy E`, the least upper bound of `0` and the values of an
  energy function `E` on the particles of a final state, is infrared safe whenever `E p → 0` as
  `p → 0` (`isInfraredSafe_leadingEnergy`), but for a nonzero linear energy functional it is not
  collinear safe (`not_isCollinearSafe_leadingEnergy`): splitting a single particle of energy
  `E p ≥ 0` with fraction `z` makes the leading energy equal to `max z (1 - z) * E p`, which is at
  most `E p` (`leadingEnergy_splitCollinear_singleton`), so already `z = 1 / 2` witnesses the
  failure.

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

/-- The particle multiplicity of a final state: its number of particles, as a real number. -/
def multiplicity : Observable V :=
  fun s => (Multiset.card s : ℝ)

theorem multiplicity_def (s : Multiset V) : multiplicity s = (Multiset.card s : ℝ) :=
  (rfl)

@[simp]
theorem multiplicity_zero : multiplicity (0 : Multiset V) = 0 := by
  simp [multiplicity_def]

@[simp]
theorem multiplicity_cons (p : V) (s : Multiset V) :
    multiplicity (p ::ₘ s) = multiplicity s + 1 := by
  simp [multiplicity_def]

/-- The particle multiplicity is not collinear safe: splitting a particle adds one. -/
theorem not_isCollinearSafe_multiplicity [AddCommGroup V] [Module ℝ V] [DecidableEq V] :
    ¬ IsCollinearSafe (multiplicity : Observable V) := by
  intro h
  have := h.apply_splitCollinear (Multiset.mem_singleton_self (0 : V))
    (z := 1 / 2) ⟨by norm_num, by norm_num⟩
  simp [multiplicity_def] at this

/-- The particle multiplicity is not infrared safe: adding a momentum, however soft, adds one
particle. -/
theorem not_isInfraredSafe_multiplicity [Zero V] [TopologicalSpace V] :
    ¬ IsInfraredSafe (multiplicity : Observable V) := by
  intro h
  have := h.tendsto 0
  simp only [multiplicity_cons, multiplicity_zero, zero_add] at this
  exact one_ne_zero (tendsto_const_nhds_iff.1 this)

/-! ### The leading-particle energy -/

/-- The leading-particle energy of a final state: the least upper bound of `0` and the values of
the energy function `E` on its particles. For a nonnegative `E` on a nonempty final state this is
the energy of the most energetic particle; on the empty final state it is `0`. -/
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

/-- Splitting a single particle of nonnegative energy `E p` with fraction `z ∈ [0, 1]` makes the
leading-particle energy equal to `max z (1 - z) * E p`, which is at most `E p`. -/
theorem leadingEnergy_splitCollinear_singleton (E : V →ₗ[ℝ] ℝ) {p : V} (hp : 0 ≤ E p) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    leadingEnergy E (splitCollinear p z {p}) = max z (1 - z) * E p := by
  rw [← Multiset.cons_zero, splitCollinear_cons_self]
  have h₂ : 0 ≤ (1 - z) * E p := mul_nonneg (sub_nonneg.2 hz.2) hp
  have key : max (z * E p) ((1 - z) * E p) = max z (1 - z) * E p :=
    (max_mul_of_nonneg _ _ hp).symm
  simp [max_eq_left h₂, key]

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
