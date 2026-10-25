/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Algebra.BigOperators.Finset
public import EpsilonEridani.Mathematics.Analysis.Fourier.AddCircle

/-!
# Azimuthal harmonics of an event at finite multiplicity

An *event* is a finite family `φ : ι → AddCircle T` of azimuthal angles; its multiplicity is
`M = Fintype.card ι`. For the physical period `T = 2π` the Fourier monomial `fourier n` of
Mathlib is `φ ↦ e^{i n φ}`, and every definition below is stated through it, so the
normalisation of the harmonics is Mathlib's.

* The `Q`-vector of harmonic `n` is `Q_n = ∑ⱼ e^{i n φⱼ}` (`qVector`).
* The anisotropy coefficient of harmonic `n` of a single-particle distribution `μ` on the circle
  is `V_n = ∫ e^{i n φ} dμ` (`anisotropyCoeff`). Its modulus is the coefficient usually written
  `vₙ`, and its phase is `n` times the symmetry-plane angle. When `μ` has a density `f` with
  respect to the normalised Haar measure, `V_n` is the Fourier coefficient of `f` of index `-n`
  (`anisotropyCoeff_withDensity`). The coefficient is a parameter of the distribution, not an
  observable of a single event.

The squared modulus of the `Q`-vector contains the *self-correlation* `M` of every particle with
itself (`norm_qVector_sq`, `ofReal_norm_qVector_sq`). For particles drawn independently from `μ`,
its expectation is `M + M (M - 1) |V_n|²` (`integral_norm_qVector_sq`). The naive estimator
`|Q_n|² / M²` is therefore biased by `(1 - |V_n|²) / M` (`integral_norm_qVector_sq_div_card_sq`).
Subtracting the self-correlation and normalising by the number `M (M - 1)` of ordered pairs of
distinct particles gives the two-particle correlation `⟨2⟩` (`twoParticleCorrelation`). Its
expectation is exactly `|V_n|²` at every multiplicity `M ≥ 2` (`integral_twoParticleCorrelation`).
This is the sense in which `|V_n|` is well posed at finite multiplicity.

Independence enters only through pairs of particles, so the expectations are stated under
pairwise independence. `iIndepFun.indepFun` supplies that from mutual independence, and the
product measure `Measure.pi` is the canonical model (`integral_twoParticleCorrelation_pi`).

A common rotation `φⱼ ↦ φⱼ + ψ` of all angles multiplies `Q_n` and `V_n` by the phase
`e^{i n ψ}`, so their moduli and `⟨2⟩` are invariant (`norm_qVector_add_const`,
`twoParticleCorrelation_add_const`, `norm_anisotropyCoeff_map_add_const`). The coefficient
itself is not: it is unchanged exactly when it vanishes or `e^{i n ψ} = 1`
(`anisotropyCoeff_map_add_const_eq_self_iff`). An anisotropy coefficient is therefore only defined
relative to a reference angle, and only its modulus is a rotation-invariant property of the
distribution.

## Main definitions

* `EpsilonEridani.Nuclear.Medium.Collective.qVector n φ`: the `Q`-vector `∑ⱼ e^{i n φⱼ}`.
* `EpsilonEridani.Nuclear.Medium.Collective.twoParticleCorrelation n φ`: the single-event
  two-particle correlation `⟨2⟩ = (|Q_n|² - M) / (M (M - 1))`.
* `EpsilonEridani.Nuclear.Medium.Collective.anisotropyCoeff μ n`: the coefficient
  `∫ e^{i n φ} dμ` of a distribution `μ` on the circle.

## Main statements

* `ofReal_norm_qVector_sq`: `|Q_n|² = M + ∑_{j ≠ k} e^{i n φⱼ} conj (e^{i n φₖ})`.
* `integral_norm_qVector_sq`: `E |Q_n|² = M + M (M - 1) |V_n|²` for independent draws.
* `integral_twoParticleCorrelation`: `E ⟨2⟩ = |V_n|²` for independent draws and `M ≥ 2`.
* `anisotropyCoeff_map_add_const`: rotating the distribution by `ψ` multiplies `V_n` by `e^{i n ψ}`.

## References

* A. Bilandzic, R. Snellings and S. Voloshin, *Flow analysis with cumulants: direct
  calculations*, Phys. Rev. C 83 (2011) 044913, arXiv:1010.0233, §II.
* N. Borghini, P. M. Dinh and J.-Y. Ollitrault, *Flow analysis from multiparticle azimuthal
  correlations*, Phys. Rev. C 64 (2001) 054901, arXiv:nucl-th/0105040.
* S. Voloshin and Y. Zhang, *Flow study in relativistic nuclear collisions by Fourier expansion
  of azimuthal particle distributions*, Z. Phys. C 70 (1996) 665, arXiv:hep-ph/9407282.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset AddCircle
open scoped ComplexConjugate

namespace EpsilonEridani.Nuclear.Medium.Collective

variable {T : ℝ} {ι : Type*} [Fintype ι]

/-! ### The `Q`-vector and the two-particle correlation of one event -/

/-- The `Q`-vector of harmonic `n` of an event `φ`, `Q_n = ∑ⱼ e^{i n φⱼ}`, with the Fourier
monomial `fourier n` of Mathlib as the harmonic. -/
def qVector (n : ℤ) (φ : ι → AddCircle T) : ℂ :=
  ∑ j, fourier n (φ j)

theorem qVector_def (n : ℤ) (φ : ι → AddCircle T) : qVector n φ = ∑ j, fourier n (φ j) :=
  (rfl)

/-- The zeroth harmonic counts the particles: `Q_0 = M`. -/
@[simp]
theorem qVector_zero (φ : ι → AddCircle T) : qVector 0 φ = Fintype.card ι := by
  simp [qVector_def]

/-- The `Q`-vector of harmonic `-n` is the complex conjugate of that of harmonic `n`. -/
@[simp]
theorem qVector_neg (n : ℤ) (φ : ι → AddCircle T) : qVector (-n) φ = conj (qVector n φ) := by
  simp [qVector_def]

/-- A common rotation of all angles by `ψ` multiplies the `Q`-vector by `e^{i n ψ}`. -/
theorem qVector_add_const (n : ℤ) (φ : ι → AddCircle T) (ψ : AddCircle T) :
    qVector n (fun j => φ j + ψ) = fourier n ψ * qVector n φ := by
  rw [mul_comm]
  simp only [qVector_def, Finset.sum_mul, fourier_eval_add]

/-- The modulus of the `Q`-vector is invariant under a common rotation of all angles. -/
@[simp]
theorem norm_qVector_add_const (n : ℤ) (φ : ι → AddCircle T) (ψ : AddCircle T) :
    ‖qVector n (fun j => φ j + ψ)‖ = ‖qVector n φ‖ := by
  rw [qVector_add_const, norm_mul, norm_fourier_eval, one_mul]

/-- The `Q`-vector depends continuously on the angles. -/
@[fun_prop]
theorem continuous_qVector (n : ℤ) : Continuous (qVector (T := T) (ι := ι) n) := by
  simp_rw [funext (qVector_def n)]
  exact continuous_finsetSum _ fun j _ => (fourier n).continuous.comp (continuous_apply j)

/-- The modulus of the `Q`-vector is at most the multiplicity. -/
theorem norm_qVector_le_card (n : ℤ) (φ : ι → AddCircle T) : ‖qVector n φ‖ ≤ Fintype.card ι := by
  rw [qVector_def]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_fourier_eval, sum_const, card_univ, nsmul_eq_mul, mul_one, le_refl]

/-- The squared modulus of the `Q`-vector is the self-correlation `M` plus the sum over ordered
pairs of distinct particles of `e^{i n φⱼ} conj (e^{i n φₖ}) = e^{i n (φⱼ - φₖ)}`. -/
theorem ofReal_norm_qVector_sq [DecidableEq ι] (n : ℤ) (φ : ι → AddCircle T) :
    (‖qVector n φ‖ : ℂ) ^ 2 =
      Fintype.card ι + ∑ j, ∑ k ∈ univ.erase j, fourier n (φ j) * conj (fourier n (φ k)) := by
  simp only [← Complex.mul_conj', qVector_def, map_sum, Finset.sum_mul_sum]
  refine (Finset.sum_congr rfl fun j _ => (Finset.add_sum_erase _ _ (mem_univ j)).symm).trans ?_
  simp only [Complex.mul_conj', norm_fourier_eval, Complex.ofReal_one, one_pow,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The squared modulus of the `Q`-vector is the self-correlation `M` plus the sum over ordered
pairs of distinct particles of `Re e^{i n (φⱼ - φₖ)}`, the cosine of `n (φⱼ - φₖ)` at `T = 2π`. -/
theorem norm_qVector_sq [DecidableEq ι] (n : ℤ) (φ : ι → AddCircle T) :
    ‖qVector n φ‖ ^ 2 =
      Fintype.card ι + ∑ j, ∑ k ∈ univ.erase j, (fourier n (φ j - φ k)).re := by
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.add_re, Complex.natCast_re,
    Complex.re_sum, fourier_eval_sub] using congrArg Complex.re (ofReal_norm_qVector_sq n φ)

/-- At multiplicity `M ≤ 1` the squared modulus of the `Q`-vector is the self-correlation `M`:
`Q_n = 0` for `M = 0` and `|Q_n| = 1` for `M = 1`. -/
theorem norm_qVector_sq_of_card_le_one (h : Fintype.card ι ≤ 1) (n : ℤ) (φ : ι → AddCircle T) :
    ‖qVector n φ‖ ^ 2 = Fintype.card ι := by
  have := Fintype.card_le_one_iff_subsingleton.1 h
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j⟩⟩
  · simp [qVector_def]
  · have : Unique ι := uniqueOfSubsingleton j
    simp [qVector_def]

/-- The single-event two-particle correlation `⟨2⟩ = (|Q_n|² - M) / (M (M - 1))`: the squared
modulus of the `Q`-vector with the self-correlation removed, averaged over the `M (M - 1)` ordered
pairs of distinct particles. When `M ≤ 1` the denominator vanishes and the value is `0` (Lean junk).
The meaningful values are for `M ≥ 2`. -/
def twoParticleCorrelation (n : ℤ) (φ : ι → AddCircle T) : ℝ :=
  (‖qVector n φ‖ ^ 2 - Fintype.card ι) / (Fintype.card ι * (Fintype.card ι - 1))

theorem twoParticleCorrelation_def (n : ℤ) (φ : ι → AddCircle T) :
    twoParticleCorrelation n φ =
      (‖qVector n φ‖ ^ 2 - Fintype.card ι) / (Fintype.card ι * (Fintype.card ι - 1)) :=
  (rfl)

/-- At multiplicity `M ≤ 1` there are no ordered pairs of distinct particles, the denominator
`M (M - 1)` vanishes and the two-particle correlation takes the junk value `0`. -/
theorem twoParticleCorrelation_eq_zero_of_card_le_one (h : Fintype.card ι ≤ 1) (n : ℤ)
    (φ : ι → AddCircle T) : twoParticleCorrelation n φ = 0 := by
  rw [twoParticleCorrelation_def, norm_qVector_sq_of_card_le_one h, sub_self, zero_div]

/-- The squared modulus of the `Q`-vector is the self-correlation `M` plus `M (M - 1)` times the
two-particle correlation, at every multiplicity. -/
theorem norm_qVector_sq_eq_card_add_mul_twoParticleCorrelation (n : ℤ) (φ : ι → AddCircle T) :
    ‖qVector n φ‖ ^ 2 =
      Fintype.card ι + Fintype.card ι * (Fintype.card ι - 1) * twoParticleCorrelation n φ := by
  rcases le_or_gt (Fintype.card ι) 1 with h | h
  · rw [twoParticleCorrelation_eq_zero_of_card_le_one h, mul_zero, add_zero,
      norm_qVector_sq_of_card_le_one h]
  · have h1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast h
    have hD : (Fintype.card ι : ℝ) * (Fintype.card ι - 1) ≠ 0 := by
      apply mul_ne_zero <;> [positivity; linarith]
    rw [twoParticleCorrelation_def, mul_div_cancel₀ _ hD, add_sub_cancel]

/-- For `M ≥ 2` the two-particle correlation of the zeroth harmonic is `1`: every ordered pair of
distinct particles contributes `e^0 = 1`. -/
@[simp]
theorem twoParticleCorrelation_zero (h : 1 < Fintype.card ι) (φ : ι → AddCircle T) :
    twoParticleCorrelation 0 φ = 1 := by
  have h1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast h
  have hD : (Fintype.card ι : ℝ) * (Fintype.card ι - 1) ≠ 0 := by
    apply mul_ne_zero <;> [positivity; linarith]
  rw [twoParticleCorrelation_def, qVector_zero, Complex.norm_natCast, div_eq_one_iff_eq hD]
  ring

/-- The two-particle correlation is the average of `Re e^{i n (φⱼ - φₖ)}`, the cosine of
`n (φⱼ - φₖ)` at `T = 2π`, over ordered pairs of distinct particles. -/
theorem twoParticleCorrelation_eq_sum [DecidableEq ι] (n : ℤ) (φ : ι → AddCircle T) :
    twoParticleCorrelation n φ =
      (∑ j, ∑ k ∈ univ.erase j, (fourier n (φ j - φ k)).re) /
        (Fintype.card ι * (Fintype.card ι - 1)) := by
  rw [twoParticleCorrelation_def, norm_qVector_sq, add_sub_cancel_left]

/-- The two-particle correlation is the average of `e^{i n (φⱼ - φₖ)}` over ordered pairs of
distinct particles. -/
theorem ofReal_twoParticleCorrelation_eq_sum [DecidableEq ι] (n : ℤ) (φ : ι → AddCircle T) :
    (twoParticleCorrelation n φ : ℂ) =
      (∑ j, ∑ k ∈ univ.erase j, fourier n (φ j) * conj (fourier n (φ k))) /
        (Fintype.card ι * (Fintype.card ι - 1)) := by
  rw [twoParticleCorrelation_def]
  push_cast
  rw [ofReal_norm_qVector_sq]
  ring

/-- The two-particle correlation has absolute value at most `1`, at every multiplicity.
At `M ≤ 1` the value is `0` (division by zero) and the bound is trivially true. -/
theorem abs_twoParticleCorrelation_le_one (n : ℤ) (φ : ι → AddCircle T) :
    |twoParticleCorrelation n φ| ≤ 1 := by
  -- for M ≤ 1 the denominator M (M - 1) vanishes and ⟨2⟩ takes the junk value 0
  rcases le_or_gt (Fintype.card ι) 1 with h | h
  · simp [twoParticleCorrelation_eq_zero_of_card_le_one h]
  rw [twoParticleCorrelation_def]
  have h2 : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast h
  have hq := pow_le_pow_left₀ (norm_nonneg _) (norm_qVector_le_card n φ) 2
  have hD : (0 : ℝ) < Fintype.card ι * (Fintype.card ι - 1) := by nlinarith
  simp only [abs_div, abs_of_pos hD, div_le_one hD, abs_sub_le_iff]
  constructor <;> nlinarith [sq_nonneg ‖qVector n φ‖]

/-- The two-particle correlations of harmonics `n` and `-n` coincide. -/
@[simp]
theorem twoParticleCorrelation_neg (n : ℤ) (φ : ι → AddCircle T) :
    twoParticleCorrelation (-n) φ = twoParticleCorrelation n φ := by
  simp [twoParticleCorrelation_def]

/-- The two-particle correlation is invariant under a common rotation of all angles. -/
@[simp]
theorem twoParticleCorrelation_add_const (n : ℤ) (φ : ι → AddCircle T) (ψ : AddCircle T) :
    twoParticleCorrelation n (fun j => φ j + ψ) = twoParticleCorrelation n φ := by
  simp [twoParticleCorrelation_def]

/-- The two-particle correlation depends continuously on the angles. -/
@[fun_prop]
theorem continuous_twoParticleCorrelation (n : ℤ) :
    Continuous (twoParticleCorrelation (T := T) (ι := ι) n) := by
  simp_rw [funext (twoParticleCorrelation_def n)]
  fun_prop

/-! ### The anisotropy coefficient of a distribution on the circle -/

/-- The anisotropy coefficient of harmonic `n` of a single-particle distribution `μ` on the
circle, `V_n = ∫ e^{i n φ} dμ`. Its modulus is the coefficient `vₙ` and its argument is `n` times
the symmetry-plane angle. -/
def anisotropyCoeff (μ : Measure (AddCircle T)) (n : ℤ) : ℂ :=
  ∫ x, fourier n x ∂μ

theorem anisotropyCoeff_def (μ : Measure (AddCircle T)) (n : ℤ) :
    anisotropyCoeff μ n = ∫ x, fourier n x ∂μ :=
  (rfl)

/-- The zeroth coefficient is the total mass of the distribution; for a probability distribution
it is `1`. -/
@[simp]
theorem anisotropyCoeff_zero (μ : Measure (AddCircle T)) :
    anisotropyCoeff μ 0 = μ.real Set.univ := by
  simp [anisotropyCoeff_def]

/-- The coefficient of harmonic `-n` is the complex conjugate of that of harmonic `n`. -/
@[simp]
theorem anisotropyCoeff_neg (μ : Measure (AddCircle T)) (n : ℤ) :
    anisotropyCoeff μ (-n) = conj (anisotropyCoeff μ n) := by
  simp_rw [anisotropyCoeff_def, fourier_neg, integral_conj]

/-- The coefficients of a probability distribution have modulus at most `1`. -/
theorem norm_anisotropyCoeff_le_one (μ : Measure (AddCircle T)) [IsProbabilityMeasure μ]
    (n : ℤ) : ‖anisotropyCoeff μ n‖ ≤ 1 := by
  rw [anisotropyCoeff_def]
  refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall
    fun x => (norm_fourier_eval n x).le)).trans ?_
  simp

/-- For a distribution with density `f` with respect to the normalised Haar measure, the
anisotropy coefficient of harmonic `n` is the Fourier coefficient of `f` of index `-n`. -/
theorem anisotropyCoeff_withDensity [Fact (0 < T)] {f : AddCircle T → ENNReal}
    (hf : AEMeasurable f haarAddCircle) (hf_lt_top : ∀ᵐ x ∂haarAddCircle, f x < ⊤) (n : ℤ) :
    anisotropyCoeff (haarAddCircle.withDensity f) n =
      fourierCoeff (fun x => ((f x).toReal : ℂ)) (-n) := by
  simp [anisotropyCoeff_def, integral_withDensity_eq_integral_toReal_smul₀ hf hf_lt_top,
    fourierCoeff, Complex.real_smul, mul_comm]

/-- Rotating a distribution by `ψ` multiplies its anisotropy coefficient by `e^{i n ψ}`. -/
theorem anisotropyCoeff_map_add_const (μ : Measure (AddCircle T)) (n : ℤ) (ψ : AddCircle T) :
    anisotropyCoeff (μ.map (· + ψ)) n = fourier n ψ * anisotropyCoeff μ n := by
  simp only [anisotropyCoeff_def, ← integral_const_mul]
  rw [integral_map (measurable_add_const ψ).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  congr 1 with x
  rw [fourier_eval_add, mul_comm]

/-- The modulus of the anisotropy coefficient is invariant under rotations. -/
@[simp]
theorem norm_anisotropyCoeff_map_add_const (μ : Measure (AddCircle T)) (n : ℤ) (ψ : AddCircle T) :
    ‖anisotropyCoeff (μ.map (· + ψ)) n‖ = ‖anisotropyCoeff μ n‖ := by
  rw [anisotropyCoeff_map_add_const, norm_mul, norm_fourier_eval, one_mul]

/-- The anisotropy coefficient itself is not rotation invariant: rotating by `ψ` leaves it
unchanged exactly when it vanishes or `e^{i n ψ} = 1`. -/
theorem anisotropyCoeff_map_add_const_eq_self_iff (μ : Measure (AddCircle T)) (n : ℤ)
    (ψ : AddCircle T) :
    anisotropyCoeff (μ.map (· + ψ)) n = anisotropyCoeff μ n ↔
      anisotropyCoeff μ n = 0 ∨ fourier n ψ = 1 := by
  simp [anisotropyCoeff_map_add_const, mul_left_eq_self₀, or_comm]

/-! ### Measurability and integrability of the event observables -/

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Measure (AddCircle T)}
  {φ : ι → Ω → AddCircle T}

/-- The `Q`-vector of an event whose angles are almost everywhere measurable is almost everywhere
measurable. -/
@[fun_prop]
theorem aemeasurable_qVector (hφ : ∀ j, AEMeasurable (φ j) P) (n : ℤ) :
    AEMeasurable (fun ω => qVector n fun j => φ j ω) P :=
  (continuous_qVector n).measurable.comp_aemeasurable (AEMeasurable.of_eval hφ)

/-- The two-particle correlation of an event whose angles are almost everywhere measurable is
almost everywhere measurable. -/
@[fun_prop]
theorem aemeasurable_twoParticleCorrelation (hφ : ∀ j, AEMeasurable (φ j) P) (n : ℤ) :
    AEMeasurable (fun ω => twoParticleCorrelation n fun j => φ j ω) P :=
  (continuous_twoParticleCorrelation n).measurable.comp_aemeasurable (AEMeasurable.of_eval hφ)

section Integrable

variable [IsFiniteMeasure P]

/-- The `Q`-vector of an event whose angles are almost everywhere measurable is integrable. -/
@[fun_prop]
theorem integrable_qVector (hφ : ∀ j, AEMeasurable (φ j) P) (n : ℤ) :
    Integrable (fun ω => qVector n fun j => φ j ω) P :=
  .of_bound (aemeasurable_qVector hφ n).aestronglyMeasurable (Fintype.card ι)
    (Filter.Eventually.of_forall fun _ => norm_qVector_le_card n _)

/-- The squared modulus of the `Q`-vector of an event whose angles are almost everywhere
measurable is integrable. -/
@[fun_prop]
theorem integrable_norm_qVector_sq (hφ : ∀ j, AEMeasurable (φ j) P) (n : ℤ) :
    Integrable (fun ω => ‖qVector n fun j => φ j ω‖ ^ 2) P :=
  .of_bound ((aemeasurable_qVector hφ n).norm.pow_const 2).aestronglyMeasurable
    ((Fintype.card ι : ℝ) ^ 2) (Filter.Eventually.of_forall fun ω => by
      simp only [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_qVector_le_card n _) 2)

/-- The two-particle correlation of an event whose angles are almost everywhere measurable is
integrable. -/
@[fun_prop]
theorem integrable_twoParticleCorrelation (hφ : ∀ j, AEMeasurable (φ j) P) (n : ℤ) :
    Integrable (fun ω => twoParticleCorrelation n fun j => φ j ω) P :=
  .of_bound (aemeasurable_twoParticleCorrelation hφ n).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun _ => (abs_twoParticleCorrelation_le_one n _))

/-- The expectation of the `Q`-vector of `M` particles with distribution `μ` is `M V_n`. Only
the finiteness of the measure enters: independence is not needed for the first moment. -/
theorem integral_qVector (hφ : ∀ j, HasLaw (φ j) μ P) (n : ℤ) :
    ∫ ω, qVector n (fun j => φ j ω) ∂P = Fintype.card ι * anisotropyCoeff μ n := by
  simp_rw [qVector_def]
  rw [integral_finsetSum _ fun j _ => integrable_fourier_comp (hφ j).aemeasurable n,
    anisotropyCoeff_def, ← nsmul_eq_mul, ← card_univ, ← sum_const]
  exact Finset.sum_congr rfl fun j _ =>
    (hφ j).integral_comp (fourier n).continuous.aestronglyMeasurable

end Integrable

/-! ### Expectations for independent draws -/

variable [IsProbabilityMeasure P] (hφ : ∀ j, HasLaw (φ j) μ P)
  (hind : Pairwise fun j k => IndepFun (φ j) (φ k) P)
include hφ hind

/-- **Expectation of the squared `Q`-vector.** For `M` pairwise independent particles with
distribution `μ`, `E |Q_n|² = M + M (M - 1) |V_n|²`. The term `M` is the self-correlation. -/
theorem integral_norm_qVector_sq (n : ℤ) :
    ∫ ω, ‖qVector n (fun j => φ j ω)‖ ^ 2 ∂P =
      Fintype.card ι + Fintype.card ι * (Fintype.card ι - 1) * ‖anisotropyCoeff μ n‖ ^ 2 := by
  classical
  have hpair : ∀ j, ∀ k ∈ univ.erase j,
      Integrable (fun ω => fourier n (φ j ω) * conj (fourier n (φ k ω))) P := fun j k _ =>
    integrable_fourier_mul_conj_fourier (hφ j).aemeasurable (hφ k).aemeasurable n
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  simp_rw [ofReal_norm_qVector_sq]
  simp only [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ (hpair j)), integral_finsetSum _ fun j _ =>
      integrable_finsetSum _ (hpair j)]
  simp_rw [fun j => integral_finsetSum _ (hpair j)]
  have hjk : ∀ j, ∀ k ∈ univ.erase j,
      ∫ ω, fourier n (φ j ω) * conj (fourier n (φ k ω)) ∂P =
        (‖anisotropyCoeff μ n‖ : ℂ) ^ 2 := fun j k hk => by
    rw [integral_fourier_mul_conj_fourier (hind (Finset.ne_of_mem_erase hk).symm) (hφ j)
      (hφ k) n, ← anisotropyCoeff_def, Complex.mul_conj']
  -- each of the `M (M - 1)` ordered pairs of distinct particles contributes `|V_n|²`
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl (hjk j), sum_sum_erase_const',
    Finset.card_univ, integral_const, probReal_univ, one_smul]

/-- For `M ≥ 1` pairwise independent particles with distribution `μ`, the expectation of
`|Q_n|² / M²` exceeds `|V_n|²` by the self-correlation term `(1 - |V_n|²) / M`; it vanishes
whenever `|V_n| = 1` (e.g. at `n = 0` where `V_0 = 1`). -/
theorem integral_norm_qVector_sq_div_card_sq [Nonempty ι] (n : ℤ) :
    ∫ ω, ‖qVector n (fun j => φ j ω)‖ ^ 2 / (Fintype.card ι : ℝ) ^ 2 ∂P =
      ‖anisotropyCoeff μ n‖ ^ 2 + (1 - ‖anisotropyCoeff μ n‖ ^ 2) / Fintype.card ι := by
  have hM : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [integral_div, integral_norm_qVector_sq hφ hind]
  field_simp
  ring

/-- **The two-particle correlation is unbiased.** For `M ≥ 2` pairwise independent particles
with distribution `μ`, the expectation of `⟨2⟩` is exactly `|V_n|²`. -/
theorem integral_twoParticleCorrelation (hM : 1 < Fintype.card ι) (n : ℤ) :
    ∫ ω, twoParticleCorrelation n (fun j => φ j ω) ∂P = ‖anisotropyCoeff μ n‖ ^ 2 := by
  have h1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hM
  have hM0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hM1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  simp_rw [twoParticleCorrelation_def]
  simp only [integral_div,
    integral_sub (integrable_norm_qVector_sq (fun j => (hφ j).aemeasurable) n) (integrable_const _),
    integral_norm_qVector_sq hφ hind, integral_const, probReal_univ, one_smul,
    div_eq_iff (mul_ne_zero hM0 hM1)]
  ring

end Expectation

/-- **Independent draws.** For `M ≥ 2` particles drawn independently from a probability
distribution `μ` on the circle, the expectation of `⟨2⟩` is `|V_n|²`. -/
theorem integral_twoParticleCorrelation_pi (μ : Measure (AddCircle T)) [IsProbabilityMeasure μ]
    (hM : 1 < Fintype.card ι) (n : ℤ) :
    ∫ φ, twoParticleCorrelation n φ ∂(Measure.pi fun _ : ι => μ) = ‖anisotropyCoeff μ n‖ ^ 2 := by
  have hind : iIndepFun (fun (j : ι) (φ : ι → AddCircle T) => φ j)
      (Measure.pi fun _ : ι => μ) :=
    iIndepFun_pi (X := fun (_ : ι) (x : AddCircle T) => x) fun _ => aemeasurable_id
  exact integral_twoParticleCorrelation (P := Measure.pi fun _ : ι => μ)
    (φ := fun j (x : ι → AddCircle T) => x j)
    (fun j => (measurePreserving_eval (fun _ : ι => μ) j).hasLaw)
    (fun _ _ hjk => hind.indepFun hjk) hM n

end EpsilonEridani.Nuclear.Medium.Collective
