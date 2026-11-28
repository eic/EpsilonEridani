/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Jets.Observable.Basic
public import EpsilonEridani.QFT.Jets.Observable.Leading
public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Unsafe observables

The safety conditions of `EpsilonEridani.QFT.Jets.Observable.Basic` are only meaningful together
with observables that fail them. This file records the standard ones.

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
* The number `thresholdCount E E₀ s` of particles whose energy exceeds a threshold `E₀` is, for a
  nonzero linear energy functional `E`, not collinear safe for any threshold
  (`not_isCollinearSafe_thresholdCount`): a particle of energy `2 (|E₀| + 1)` splits into two
  halves that are both above the threshold. For a nonzero continuous linear energy functional it
  is infrared safe exactly when the threshold is positive (`isInfraredSafe_thresholdCount_iff`):
  at a threshold `E₀ ≤ 0` arbitrarily soft particles of positive energy are counted
  (`not_isInfraredSafe_thresholdCount`). Weighting each particle by its energy instead of counting
  the particles above a threshold gives the energy sum `∑ E p`, which for a linear `E` is collinear
  safe (`isCollinearSafe_sum_map`), and for a continuous linear `E` infrared and collinear safe
  (`isIRCSafe_sum_map`).
* The invariant mass squared `leadingPairMassSq g E s` of the two most energetic particles
  `leadingParticles E 2 s` of a final state (`EpsilonEridani.QFT.Jets.Observable.Leading`) is,
  for a nonzero linear energy functional `E`, collinear safe if and only if the bilinear form `g`
  is alternating, `g q q = 0` for every `q`, so that every invariant mass vanishes
  (`isCollinearSafe_leadingPairMassSq_iff`). For the Minkowski metric it is therefore not
  collinear safe. The explicit witness (`not_isCollinearSafe_leadingPairMassSq`) is a
  two-particle state `{p, q}` with `2 E q < E p`: splitting `p` with `z = 1 / 2` makes the two
  halves of `p` the leading pair, and changes the invariant mass squared of the leading pair from
  `g (p + q) (p + q)` to `g p p`.

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

/-! ### The number of particles above an energy threshold -/

/-- The number of particles of a final state whose energy `E p` exceeds the threshold `E₀`, as a
real number. -/
noncomputable def thresholdCount (E : V → ℝ) (E₀ : ℝ) : Observable V :=
  fun s => (s.countP fun p => E₀ < E p : ℕ)

theorem thresholdCount_def (E : V → ℝ) (E₀ : ℝ) (s : Multiset V) :
    thresholdCount E E₀ s = (s.countP fun p => E₀ < E p : ℕ) :=
  (rfl)

@[simp]
theorem thresholdCount_zero (E : V → ℝ) (E₀ : ℝ) : thresholdCount E E₀ 0 = 0 := by
  simp [thresholdCount_def]

@[simp]
theorem thresholdCount_cons (E : V → ℝ) (E₀ : ℝ) (p : V) (s : Multiset V) :
    thresholdCount E E₀ (p ::ₘ s) = thresholdCount E E₀ s + if E₀ < E p then 1 else 0 := by
  by_cases h : E₀ < E p <;> simp [thresholdCount_def, h]

@[simp]
theorem thresholdCount_singleton (E : V → ℝ) (E₀ : ℝ) (p : V) :
    thresholdCount E E₀ {p} = if E₀ < E p then 1 else 0 := by
  rw [← Multiset.cons_zero, thresholdCount_cons, thresholdCount_zero, zero_add]

/-- The number of particles above a threshold in the union of two final states is the sum of the
two numbers. -/
@[simp]
theorem thresholdCount_add (E : V → ℝ) (E₀ : ℝ) (s t : Multiset V) :
    thresholdCount E E₀ (s + t) = thresholdCount E E₀ s + thresholdCount E E₀ t := by
  simp [thresholdCount_def]

/-- Above a positive threshold, the number of particles above it is infrared safe for an energy
function that vanishes in the limit of vanishing momentum: a soft enough added particle stays
below the threshold. -/
theorem isInfraredSafe_thresholdCount [Zero V] [TopologicalSpace V] {E : V → ℝ}
    (hE : Tendsto E (𝓝 0) (𝓝 0)) {E₀ : ℝ} (hE₀ : 0 < E₀) :
    IsInfraredSafe (thresholdCount E E₀) := by
  refine isInfraredSafe_def.2 fun s => tendsto_const_nhds.congr' ?_
  filter_upwards [hE.eventually (eventually_lt_nhds hE₀)] with p hp
  simp [not_lt.2 hp.le]

section Linear

variable [AddCommGroup V] [Module ℝ V]

/-- The number of particles above an energy threshold is not collinear safe, whatever the
threshold, for a nonzero linear energy functional: a single particle of energy `2 (|E₀| + 1)`
splits into two halves of energy `|E₀| + 1`, both above the threshold. -/
theorem not_isCollinearSafe_thresholdCount {E : V →ₗ[ℝ] ℝ} (hE : E ≠ 0) (E₀ : ℝ) :
    ¬ IsCollinearSafe (thresholdCount E E₀) := by
  intro h
  obtain ⟨p, hp⟩ := LinearMap.surjective hE (2 * (|E₀| + 1))
  have := isCollinearSafe_def.1 h 0 p (1 / 2) ⟨by norm_num, by norm_num⟩
  have h₁ : E₀ < 1 / 2 * (2 * (|E₀| + 1)) := by linarith [le_abs_self E₀]
  have h₂ : E₀ < (1 - 1 / 2) * (2 * (|E₀| + 1)) := by linarith [le_abs_self E₀]
  have h₃ : E₀ < 2 * (|E₀| + 1) := by linarith [le_abs_self E₀, abs_nonneg E₀]
  simp only [thresholdCount_cons, thresholdCount_zero, map_smul, smul_eq_mul, hp, h₁, h₂, h₃,
    ↓reduceIte] at this
  norm_num at this

/-- At a threshold `E₀ ≤ 0`, the number of particles above it is not infrared safe for a nonzero
linear energy functional: the particles `t • p` with `E p = 1` and `t > 0` are arbitrarily soft and
are all counted. -/
theorem not_isInfraredSafe_thresholdCount [TopologicalSpace V] [ContinuousSMul ℝ V]
    {E : V →ₗ[ℝ] ℝ} (hE : E ≠ 0) {E₀ : ℝ} (hE₀ : E₀ ≤ 0) :
    ¬ IsInfraredSafe (thresholdCount E E₀) := by
  intro h
  obtain ⟨p, hp⟩ := LinearMap.surjective hE 1
  have hsoft : Tendsto (fun t : ℝ => t • p) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous fun t : ℝ => t • p := continuous_id.smul continuous_const
    simpa using (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have hcount : Tendsto (fun t : ℝ => thresholdCount E E₀ (t • p ::ₘ 0)) (𝓝[>] 0) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp [hp, hE₀.trans_lt ht]
  have := tendsto_nhds_unique ((isInfraredSafe_def.1 h 0).comp hsoft) hcount
  simp at this

/-- For a nonzero continuous linear energy functional, the number of particles above a threshold
`E₀` is infrared safe if and only if the threshold is positive. -/
theorem isInfraredSafe_thresholdCount_iff [TopologicalSpace V] [ContinuousSMul ℝ V]
    {E : V →L[ℝ] ℝ} (hE : E ≠ 0) {E₀ : ℝ} :
    IsInfraredSafe (thresholdCount E E₀) ↔ 0 < E₀ := by
  refine ⟨fun h => not_le.1 fun hE₀ => ?_,
    isInfraredSafe_thresholdCount (E.continuous.tendsto' 0 0 (map_zero E))⟩
  rw [← ContinuousLinearMap.coe_coe] at h
  refine not_isInfraredSafe_thresholdCount (E := (E : V →ₗ[ℝ] ℝ)) ?_ hE₀ h
  exact fun h0 => hE (ContinuousLinearMap.coe_injective (by simpa using h0))

end Linear

/-! ### The invariant mass of the two most energetic particles -/

section Linear

variable [AddCommGroup V] [Module ℝ V]

/-- The invariant mass squared `g P P` of the total momentum `P` of the two most energetic
particles of a final state, as measured by an energy function `E`. A final state of at most two
particles is its own leading pair (`leadingParticles_of_card_le`). -/
noncomputable def leadingPairMassSq (g : LinearMap.BilinForm ℝ V) (E : V → ℝ) : Observable V :=
  fun s => invariantMassSq g (leadingParticles E 2 s)

theorem leadingPairMassSq_def (g : LinearMap.BilinForm ℝ V) (E : V → ℝ) (s : Multiset V) :
    leadingPairMassSq g E s = invariantMassSq g (leadingParticles E 2 s) :=
  (rfl)

@[simp]
theorem leadingPairMassSq_zero (g : LinearMap.BilinForm ℝ V) (E : V → ℝ) :
    leadingPairMassSq g E 0 = 0 := by
  simp [leadingPairMassSq_def, invariantMassSq_def]

/-- A single particle is its own leading pair, so its leading-pair mass squared is `g p p`. -/
@[simp]
theorem leadingPairMassSq_singleton (g : LinearMap.BilinForm ℝ V) (E : V → ℝ) (p : V) :
    leadingPairMassSq g E {p} = g p p := by
  rw [leadingPairMassSq_def, leadingParticles_of_card_le (by simp), invariantMassSq_def,
    Multiset.sum_singleton]

/-- A two-particle state is its own leading pair, so its leading-pair mass squared is the invariant
mass squared `g (p + q) (p + q)` of the pair. -/
@[simp]
theorem leadingPairMassSq_pair (g : LinearMap.BilinForm ℝ V) (E : V → ℝ) (p q : V) :
    leadingPairMassSq g E (p ::ₘ q ::ₘ 0) = g (p + q) (p + q) := by
  rw [leadingPairMassSq_def, leadingParticles_of_card_le (by simp), invariantMassSq_def]
  simp

/-- The invariant mass squared of the two most energetic particles is not collinear safe whenever
a two-particle state `{p, q}` with `2 E q < E p` has an invariant mass squared different from
`g p p`: splitting `p` with `z = 1 / 2` makes the two halves of `p` the leading pair, whose total
momentum is `p`. -/
theorem not_isCollinearSafe_leadingPairMassSq {g : LinearMap.BilinForm ℝ V}
    {E : V →ₗ[ℝ] ℝ} {p q : V} (hpq : 2 * E q < E p) (hg : g (p + q) (p + q) ≠ g p p) :
    ¬ IsCollinearSafe (leadingPairMassSq g E) := by
  classical
  intro h
  have key := isCollinearSafe_def.1 h (q ::ₘ 0) p (1 / 2) ⟨by norm_num, by norm_num⟩
  -- Before the splitting, the state `{p, q}` is its own leading pair (`leadingPairMassSq_pair`).
  -- After it, the two halves of `p` are strictly more energetic than `q`.
  have hhalf : (1 / 2 : ℝ) • p ::ₘ (1 - 1 / 2 : ℝ) • p ::ₘ q ::ₘ 0 =
      ((1 / 2 : ℝ) • p ::ₘ (1 - 1 / 2 : ℝ) • p ::ₘ 0) + q ::ₘ 0 := by
    simp
  have h₂ : leadingParticles E 2 ((1 / 2 : ℝ) • p ::ₘ (1 - 1 / 2 : ℝ) • p ::ₘ q ::ₘ 0) =
      (1 / 2 : ℝ) • p ::ₘ (1 - 1 / 2 : ℝ) • p ::ₘ 0 := by
    refine leadingParticles_eq_of_lt (by rw [hhalf]; exact le_add_right le_rfl) (by simp) ?_
    rw [hhalf, add_tsub_cancel_left]
    intro a ha b hb
    simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha hb
    subst hb
    rcases ha with rfl | rfl <;> simp <;> linarith
  rw [leadingPairMassSq_pair, leadingPairMassSq_def, h₂] at key
  simp only [invariantMassSq_def, Multiset.sum_cons, Multiset.sum_zero, add_zero,
    smul_add_one_sub_smul] at key
  exact hg key.symm

/-- For a nonzero linear energy functional, the invariant mass squared of the two most energetic
particles is collinear safe if and only if the bilinear form `g` is alternating, that is, every
invariant mass squared `g q q` vanishes. In particular it is not collinear safe for the Minkowski
metric. -/
theorem isCollinearSafe_leadingPairMassSq_iff {g : LinearMap.BilinForm ℝ V}
    {E : V →ₗ[ℝ] ℝ} (hE : E ≠ 0) : IsCollinearSafe (leadingPairMassSq g E) ↔ g.IsAlt := by
  refine ⟨fun h => ?_, fun hg => isCollinearSafe_def.2 fun s p z _ => by
    simp [leadingPairMassSq_def, invariantMassSq_def, hg.self_eq_zero]⟩
  by_contra hg
  obtain ⟨q, hq⟩ : ∃ q, g q q ≠ 0 := by
    by_contra! H
    exact hg H
  -- A particle `p` more energetic than twice `q` and twice `2 • q`.
  obtain ⟨p₀, hp₀⟩ := LinearMap.surjective hE (4 * |E q| + 1)
  have hE₁ : 2 * E q < E p₀ := by rw [hp₀]; linarith [le_abs_self (E q), abs_nonneg (E q)]
  have hE₂ : 2 * E ((2 : ℝ) • q) < E p₀ := by
    rw [hp₀, map_smul, smul_eq_mul]; linarith [le_abs_self (E q), abs_nonneg (E q)]
  -- One of the two witnesses `{p₀, q}` and `{p₀, 2 • q}` changes the leading-pair mass.
  by_cases h₁ : g (p₀ + q) (p₀ + q) = g p₀ p₀
  · refine not_isCollinearSafe_leadingPairMassSq hE₂ (fun h₂ => hq ?_) h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h₁ h₂
    linarith
  · exact not_isCollinearSafe_leadingPairMassSq hE₁ h₁ h

end Linear

end EpsilonEridani.QFT.Jets
