/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Probability.Moments.Variance
public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.Probability.Moments.Variance

/-!
# The Good–Walker decomposition of diffraction off a fluctuating target

A target whose internal state is frozen during the interaction is described by a configuration
space `Ω` (for a nucleus: the positions and internal states of its nucleons) carrying a
probability measure `μ`, and by a diffractive amplitude `A : Ω → E` giving the scattering
amplitude off each fixed configuration at fixed kinematics (photon virtuality, energy, momentum
transfer or impact parameter). The amplitude takes values in a real inner product space `E`:
`ℂ` for a single helicity amplitude, or a space of helicity vectors when final polarisations are
summed over, in which case `‖A ω‖²` is that sum.

Up to the flux and phase-space factor that all three share, the cross sections are

* the *coherent* cross section `‖∫ A dμ‖²`, the squared modulus of the configuration average of
  the amplitude (the target left in the state it started in);
* the *total diffractive* cross section `∫ ‖A‖² dμ`, the configuration average of the squared
  modulus (the target in any final state, by completeness of the target states);
* the *incoherent* cross section, their difference (the target left in any other state).

All three are taken against the *same* measure and the *same* amplitude, so that the
**Good–Walker identity** holds: for a square-integrable amplitude the incoherent cross section is
the variance `∫ ‖A - ∫ A dμ‖² dμ` of the amplitude over target configurations
(`incoherentCrossSection_eq_integral_norm_sub_integral_sq`). It is non-negative, it is half the
mean squared difference between the amplitudes off two independently drawn configurations
(`two_mul_incoherentCrossSection_eq_integral_norm_sub_sq_prod`), and it vanishes exactly when the
amplitude is almost everywhere independent of the configuration
(`incoherentCrossSection_eq_zero_iff`).
Incoherent diffraction therefore measures the fluctuations of the target, and nothing else.

Square-integrability is the only hypothesis: it makes both the mean (`MemLp.integrable`) and the
mean square (`memLp_two_iff_integrable_sq_norm`) finite. The identification of these
configuration averages with matrix elements between target states is the frozen-configuration
approximation; it is not proved here, and nothing in this file depends on it.

The smallest complete example is a target with two configurations `x` and `y` of probabilities
`p` and `1 - p` (Mathlib's `ProbabilityTheory.bernoulliMeasure`). There the incoherent cross
section is `p (1 - p) ‖A x - A y‖²` (`incoherentCrossSection_bernoulliMeasure`), which vanishes
for `0 < p < 1` exactly when the two amplitudes agree.

## Main definitions

* `coherentCrossSection μ A`, `totalDiffractiveCrossSection μ A`, `incoherentCrossSection μ A`.

## Main results

* `incoherentCrossSection_eq_integral_norm_sub_integral_sq`: the Good–Walker identity.
* `coherentCrossSection_add_incoherentCrossSection`: coherent plus incoherent is total.
* `incoherentCrossSection_nonneg`, `coherentCrossSection_le_totalDiffractiveCrossSection`.
* `incoherentCrossSection_eq_zero_iff`: incoherent diffraction vanishes if and only if the
  amplitude is almost everywhere constant.
* `incoherentCrossSection_bernoulliMeasure`: the two-configuration target in closed form.

## References

* M. L. Good and W. D. Walker, *Diffraction dissociation of beam particles*, Phys. Rev. **120**
  (1960) 1857.
* H. I. Miettinen and J. Pumplin, *Diffraction scattering and the parton structure of hadrons*,
  Phys. Rev. D **18** (1978) 1696.
* H. Kowalski, L. Motyka and G. Watt, *Exclusive diffractive processes at HERA within the dipole
  picture*, Phys. Rev. D **74** (2006) 074016, §2.
-/

public section

open MeasureTheory ProbabilityTheory unitInterval
open scoped RealInnerProductSpace

namespace EpsilonEridani.QFT.Scattering.Diffractive.GoodWalker

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [NormedAddCommGroup E]

section Definitions

variable [NormedSpace ℝ E]

/-- The coherent diffractive cross section off a target with configuration measure `μ`, in units
of the common flux and phase-space factor: the squared norm `‖∫ A dμ‖²` of the configuration
average of the amplitude `A`. -/
noncomputable def coherentCrossSection (μ : Measure Ω) (A : Ω → E) : ℝ :=
  ‖∫ ω, A ω ∂μ‖ ^ 2

/-- The total diffractive cross section off a target with configuration measure `μ`, in units of
the common flux and phase-space factor: the configuration average `∫ ‖A‖² dμ` of the squared
norm of the amplitude `A`. -/
noncomputable def totalDiffractiveCrossSection (μ : Measure Ω) (A : Ω → E) : ℝ :=
  ∫ ω, ‖A ω‖ ^ 2 ∂μ

/-- The incoherent diffractive cross section off a target with configuration measure `μ`: the
total diffractive cross section minus the coherent one, both against the same measure and the
same amplitude `A`. -/
noncomputable def incoherentCrossSection (μ : Measure Ω) (A : Ω → E) : ℝ :=
  totalDiffractiveCrossSection μ A - coherentCrossSection μ A

lemma coherentCrossSection_def (μ : Measure Ω) (A : Ω → E) :
    coherentCrossSection μ A = ‖∫ ω, A ω ∂μ‖ ^ 2 := (rfl)

omit [NormedSpace ℝ E] in
lemma totalDiffractiveCrossSection_def (μ : Measure Ω) (A : Ω → E) :
    totalDiffractiveCrossSection μ A = ∫ ω, ‖A ω‖ ^ 2 ∂μ := (rfl)

lemma incoherentCrossSection_def (μ : Measure Ω) (A : Ω → E) :
    incoherentCrossSection μ A = totalDiffractiveCrossSection μ A - coherentCrossSection μ A :=
  (rfl)

/-- **Additivity.** Coherent plus incoherent is the total diffractive cross section. -/
@[simp]
theorem coherentCrossSection_add_incoherentCrossSection (μ : Measure Ω) (A : Ω → E) :
    coherentCrossSection μ A + incoherentCrossSection μ A = totalDiffractiveCrossSection μ A := by
  rw [incoherentCrossSection_def, add_sub_cancel]

/-- The coherent cross section is non-negative. -/
theorem coherentCrossSection_nonneg (μ : Measure Ω) (A : Ω → E) :
    0 ≤ coherentCrossSection μ A := by
  rw [coherentCrossSection_def]
  positivity

omit [NormedSpace ℝ E] in
/-- The total diffractive cross section is non-negative. -/
theorem totalDiffractiveCrossSection_nonneg (μ : Measure Ω) (A : Ω → E) :
    0 ≤ totalDiffractiveCrossSection μ A := by
  rw [totalDiffractiveCrossSection_def]
  exact integral_nonneg fun _ ↦ by positivity

/-- A configuration-independent amplitude `c` has coherent cross section `‖c‖²`. -/
@[simp]
theorem coherentCrossSection_const [CompleteSpace E] [IsProbabilityMeasure μ] (c : E) :
    coherentCrossSection μ (fun _ ↦ c) = ‖c‖ ^ 2 := by
  simp [coherentCrossSection_def]

omit [NormedSpace ℝ E] in
/-- A configuration-independent amplitude `c` has total diffractive cross section `‖c‖²`. -/
@[simp]
theorem totalDiffractiveCrossSection_const [IsProbabilityMeasure μ] (c : E) :
    totalDiffractiveCrossSection μ (fun _ ↦ c) = ‖c‖ ^ 2 := by
  simp [totalDiffractiveCrossSection_def]

/-- A configuration-independent amplitude produces no incoherent diffraction. -/
@[simp]
theorem incoherentCrossSection_const [CompleteSpace E] [IsProbabilityMeasure μ] (c : E) :
    incoherentCrossSection μ (fun _ ↦ c) = 0 := by
  simp [incoherentCrossSection_def]

/-- The coherent cross section of a square-integrable amplitude is at most the total diffractive
cross section. -/
theorem coherentCrossSection_le_totalDiffractiveCrossSection [IsProbabilityMeasure μ]
    {A : Ω → E} (hA : MemLp A 2 μ) :
    coherentCrossSection μ A ≤ totalDiffractiveCrossSection μ A := by
  have h := variance_nonneg (fun ω ↦ ‖A ω‖) μ
  rw [variance_eq_sub hA.norm, sub_nonneg] at h
  rw [coherentCrossSection_def, totalDiffractiveCrossSection_def]
  calc ‖∫ ω, A ω ∂μ‖ ^ 2 ≤ (∫ ω, ‖A ω‖ ∂μ) ^ 2 := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖A ω‖ ^ 2 ∂μ := by simpa using h

/-- The incoherent cross section of a square-integrable amplitude is non-negative. -/
theorem incoherentCrossSection_nonneg [IsProbabilityMeasure μ] {A : Ω → E} (hA : MemLp A 2 μ) :
    0 ≤ incoherentCrossSection μ A :=
  sub_nonneg.2 (coherentCrossSection_le_totalDiffractiveCrossSection hA)

end Definitions

section GoodWalker

variable [InnerProductSpace ℝ E] [CompleteSpace E] [IsProbabilityMeasure μ] {A : Ω → E}

/-- **The Good–Walker identity.** For a square-integrable amplitude, the incoherent cross section
is the variance `∫ ‖A - ∫ A dμ‖² dμ` of the amplitude over target configurations. -/
theorem incoherentCrossSection_eq_integral_norm_sub_integral_sq (hA : MemLp A 2 μ) :
    incoherentCrossSection μ A = ∫ ω, ‖A ω - ∫ ω', A ω' ∂μ‖ ^ 2 ∂μ := by
  rw [hA.integral_norm_sub_integral_sq, incoherentCrossSection_def,
    totalDiffractiveCrossSection_def, coherentCrossSection_def]

/-- Twice the incoherent cross section is the mean squared difference `∫∫ ‖A ω - A ω'‖²` between
the amplitudes off two independently drawn target configurations. -/
theorem two_mul_incoherentCrossSection_eq_integral_norm_sub_sq_prod (hA : MemLp A 2 μ) :
    2 * incoherentCrossSection μ A = ∫ z, ‖A z.1 - A z.2‖ ^ 2 ∂μ.prod μ := by
  rw [TauCeti.integral_norm_sub_sq_prod hA, probReal_univ, one_mul, incoherentCrossSection_def,
    totalDiffractiveCrossSection_def, coherentCrossSection_def]

/-- **Incoherent diffraction measures fluctuations.** For a square-integrable amplitude, the
incoherent cross section vanishes if and only if the amplitude is almost everywhere independent of
the target configuration. -/
theorem incoherentCrossSection_eq_zero_iff (hA : MemLp A 2 μ) :
    incoherentCrossSection μ A = 0 ↔ ∃ c, A =ᵐ[μ] fun _ ↦ c := by
  rw [incoherentCrossSection_eq_integral_norm_sub_integral_sq hA,
    hA.integral_norm_sub_integral_sq_eq_zero_iff]
  refine ⟨fun h ↦ ⟨_, h⟩, fun ⟨c, hc⟩ ↦ ?_⟩
  rwa [integral_congr_ae hc, integral_const, probReal_univ, one_smul]

end GoodWalker

section TwoConfigurations

/-! ### A target with two configurations -/

variable [MeasurableSingletonClass Ω]

/-- The coherent cross section off a target in configuration `x` with probability `p` and in
configuration `y` with probability `1 - p`. -/
theorem coherentCrossSection_bernoulliMeasure [NormedSpace ℝ E] [CompleteSpace E] (x y : Ω)
    (p : I) (A : Ω → E) :
    coherentCrossSection Ber(x, y, p) A = ‖(p : ℝ) • A x + (1 - p : ℝ) • A y‖ ^ 2 := by
  rw [coherentCrossSection_def, integral_bernoulliMeasure]

/-- The total diffractive cross section off a target in configuration `x` with probability `p`
and in configuration `y` with probability `1 - p`. -/
theorem totalDiffractiveCrossSection_bernoulliMeasure (x y : Ω) (p : I) (A : Ω → E) :
    totalDiffractiveCrossSection Ber(x, y, p) A = p * ‖A x‖ ^ 2 + (1 - p) * ‖A y‖ ^ 2 := by
  rw [totalDiffractiveCrossSection_def, integral_bernoulliMeasure, smul_eq_mul, smul_eq_mul]

/-- The incoherent cross section off a target in configuration `x` with probability `p` and in
configuration `y` with probability `1 - p` is `p (1 - p) ‖A x - A y‖²`. -/
theorem incoherentCrossSection_bernoulliMeasure [InnerProductSpace ℝ E] [CompleteSpace E]
    (x y : Ω) (p : I) (A : Ω → E) :
    incoherentCrossSection Ber(x, y, p) A = p * (1 - p) * ‖A x - A y‖ ^ 2 := by
  rw [incoherentCrossSection_def, totalDiffractiveCrossSection_bernoulliMeasure,
    coherentCrossSection_bernoulliMeasure, norm_add_sq_real, norm_sub_sq_real, norm_smul,
    norm_smul, real_inner_smul_left, real_inner_smul_right, Real.norm_of_nonneg (nonneg p),
    Real.norm_of_nonneg (one_sub_nonneg p)]
  ring

/-- For a target with two configurations of non-zero probability, incoherent diffraction
vanishes if and only if the amplitudes off the two configurations agree. -/
theorem incoherentCrossSection_bernoulliMeasure_eq_zero_iff [InnerProductSpace ℝ E]
    [CompleteSpace E] (x y : Ω) {p : I}
    (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) (A : Ω → E) :
    incoherentCrossSection Ber(x, y, p) A = 0 ↔ A x = A y := by
  simp [incoherentCrossSection_bernoulliMeasure, hp₀.ne', (sub_pos.2 hp₁).ne', sub_eq_zero]

end TwoConfigurations

end EpsilonEridani.QFT.Scattering.Diffractive.GoodWalker
