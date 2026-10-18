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

* The particle multiplicity `particleMultiplicity s = (Multiset.card s : ℝ)` is neither collinear
  safe (`not_isCollinearSafe_particleMultiplicity`) nor infrared safe
  (`not_isInfraredSafe_particleMultiplicity`): a collinear splitting and a soft addition each add
  exactly one particle.
* The leading-particle energy `leadingEnergy E`, the least upper bound of `0` and the values of an
  energy function `E` on the particles of a final state, is infrared safe whenever `E p → 0` as
  `p → 0` (`isInfraredSafe_leadingEnergy`), but for a nonzero linear energy functional it is not
  collinear safe (`not_isCollinearSafe_leadingEnergy`): splitting a particle of energy `E p ≥ 0`
  with fraction `z` replaces its contribution `E p` by `max z (1 - z) * E p`
  (`leadingEnergy_splitCollinear`), which for `z ∈ [0, 1]` is at most `E p`, so already
  `z = 1 / 2` on a single particle of positive energy witnesses the failure.

## References

* G. Sterman and S. Weinberg, *Jets from Quantum Chromodynamics*,
  Phys. Rev. Lett. 39 (1977) 1436.
* G. P. Salam, *Towards jetography*, Eur. Phys. J. C 67 (2010) 637, §2.
-/

public section

namespace EpsilonEridani.QFT.Jets

open Filter Topology

variable {V : Type*}

/-! ### Particle multiplicity -/

/-- The particle multiplicity of a final state: its number of particles, as a real number. -/
def particleMultiplicity : Observable V :=
  fun s => (Multiset.card s : ℝ)

theorem particleMultiplicity_def (s : Multiset V) :
    particleMultiplicity s = (Multiset.card s : ℝ) :=
  (rfl)

@[simp]
theorem particleMultiplicity_zero : particleMultiplicity (0 : Multiset V) = 0 := by
  simp [particleMultiplicity_def]

@[simp]
theorem particleMultiplicity_cons (p : V) (s : Multiset V) :
    particleMultiplicity (p ::ₘ s) = particleMultiplicity s + 1 := by
  simp [particleMultiplicity_def]

/-- The particle multiplicity of the union of two final states is the sum of their
multiplicities. -/
@[simp]
theorem particleMultiplicity_add (s t : Multiset V) :
    particleMultiplicity (s + t) = particleMultiplicity s + particleMultiplicity t := by
  simp [particleMultiplicity_def]

/-- The particle multiplicity is not collinear safe: splitting a particle adds one. -/
theorem not_isCollinearSafe_particleMultiplicity [AddCommGroup V] [Module ℝ V] :
    ¬ IsCollinearSafe (particleMultiplicity : Observable V) := by
  intro h
  have := isCollinearSafe_def.1 h 0 0 (1 / 2) ⟨by norm_num, by norm_num⟩
  simp at this

/-- The particle multiplicity is not infrared safe: adding a momentum, however soft, adds one
particle. -/
theorem not_isInfraredSafe_particleMultiplicity [Zero V] [TopologicalSpace V] :
    ¬ IsInfraredSafe (particleMultiplicity : Observable V) := by
  intro h
  have := isInfraredSafe_def.1 h 0
  simp only [particleMultiplicity_cons, particleMultiplicity_zero, zero_add] at this
  exact one_ne_zero (tendsto_const_nhds_iff.1 this)

/-! ### The leading-particle energy -/

/-- The leading-particle energy of a final state: the least upper bound of `0` and the values of
the energy function `E` on its particles. For a nonnegative `E` on a nonempty final state this is
the energy of the most energetic particle; on the empty final state it is `0`. -/
noncomputable def leadingEnergy (E : V → ℝ) : Observable V :=
  fun s => (s.map E).fold max 0

@[simp]
theorem leadingEnergy_zero (E : V → ℝ) : leadingEnergy E 0 = 0 := by
  simp [leadingEnergy]

@[simp]
theorem leadingEnergy_cons (E : V → ℝ) (p : V) (s : Multiset V) :
    leadingEnergy E (p ::ₘ s) = max (E p) (leadingEnergy E s) := by
  simp [leadingEnergy, Multiset.fold_cons_left]

@[simp]
theorem leadingEnergy_singleton (E : V → ℝ) (p : V) : leadingEnergy E {p} = max (E p) 0 := by
  rw [← Multiset.cons_zero, leadingEnergy_cons, leadingEnergy_zero]

/-- The leading-particle energy is the least upper bound of `0` and the particle energies. -/
@[simp]
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

/-- The leading-particle energy of the union of two final states is the larger of the two. -/
@[simp]
theorem leadingEnergy_add (E : V → ℝ) (s t : Multiset V) :
    leadingEnergy E (s + t) = max (leadingEnergy E s) (leadingEnergy E t) := by
  have := Multiset.fold_add max (0 : ℝ) 0 (s.map E) (t.map E)
  rwa [max_self, ← Multiset.map_add] at this

/-- The leading-particle energy is infrared safe for an energy function that vanishes in the
limit of vanishing momentum. -/
theorem isInfraredSafe_leadingEnergy [Zero V] [TopologicalSpace V] {E : V → ℝ}
    (hE : Tendsto E (𝓝 0) (𝓝 0)) : IsInfraredSafe (leadingEnergy E) := by
  refine isInfraredSafe_def.2 fun s => ?_
  simp only [leadingEnergy_cons]
  simpa [max_eq_right (leadingEnergy_nonneg E s)] using
    hE.max (tendsto_const_nhds (x := leadingEnergy E s))

section Linear

variable [AddCommGroup V] [Module ℝ V]

/-- The leading-particle energy after a collinear splitting of `p` in any final state `s`, for a
nonnegative energy `E p`: the pair `z • p`, `(1 - z) • p` contributes `max z (1 - z) * E p`, and
`s.erase p` is the rest of the state. When `p ∈ s` this replaces the contribution `E p` of `p`;
for `z ∈ [0, 1]` the new contribution is at most `E p`. -/
theorem leadingEnergy_splitCollinear [DecidableEq V] (E : V →ₗ[ℝ] ℝ) {p : V} (hp : 0 ≤ E p) {z : ℝ}
    (s : Multiset V) :
    leadingEnergy E (splitCollinear p z s) =
      max (max z (1 - z) * E p) (leadingEnergy E (s.erase p)) := by
  rw [splitCollinear_def, leadingEnergy_cons, leadingEnergy_cons, ← max_assoc, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul, ← max_mul_of_nonneg _ _ hp]

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
  classical
  have hz : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have := isCollinearSafe_iff_splitCollinear.1 h {p} p (Multiset.mem_singleton_self p) _ hz
  rw [leadingEnergy_splitCollinear E hp.le, Multiset.erase_singleton, leadingEnergy_zero,
    leadingEnergy_singleton, max_eq_left hp.le] at this
  norm_num [max_eq_left (by positivity : (0 : ℝ) ≤ 1 / 2 * E p)] at this
  linarith

end Linear

end EpsilonEridani.QFT.Jets
