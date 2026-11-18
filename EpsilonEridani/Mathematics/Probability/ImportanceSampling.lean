/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.StrongLaw

/-!
# Importance sampling and the weighted Monte Carlo estimator

To integrate a signed density `f` against a measure `μ`, importance sampling draws points from
a *proposal* law `μ.withDensity g`, with `g` a density against `μ`, and gives each point `x` the
*weight* `f x / g x` (`ImportanceSampling.weight f g`). The weight is real-valued and may be
negative, as the weights of an event generator with negative-weight events are.

The hypotheses are the ones an implementation needs: `g` is almost everywhere finite, and `g`
vanishes only where `f` does (`∀ᵐ x ∂μ, g x = 0 → f x = 0`), so that every region where `f`
has mass is ever proposed. Under them:

* `integral_weight`: the expected weight under the proposal is `∫ f dμ`, so the mean weight is an
  unbiased estimator of the integral. An observable `O` is estimated with the weight of `f * O`,
  which is `weight f g * O` (`weight_mul`).
* `withDensityᵥ_weight`: the proposal law reweighted by `weight f g` is the signed measure with
  density `f`. This is the statement that a weighted sample is a sample of `f`.
* `variance_weight`: for a normalised proposal, the variance of the weight is
  `∫ f² / g dμ - (∫ f dμ)²`.
* `sq_integral_abs_sub_sq_integral_le_variance_weight` and
  `variance_weight_optimalProposal`: that variance is at least `(∫ |f| dμ)² - (∫ f dμ)²` for
  every proposal, and the proposal `|f| / ∫ |f| dμ` (`optimalProposal`) attains the bound. For
  a non-negative `f` the optimal proposal has zero variance
  (`variance_weight_optimalProposal_of_nonneg`).
* `integral_average_weight` and `ae_tendsto_average_weight`: for independent draws `X i` from
  the proposal, the average `(1/n) ∑_{i < n} weight f g (X i)` has expectation `∫ f dμ` for every
  `n ≥ 1` and converges to it almost surely, by Mathlib's strong law of large numbers. This is
  the convergence of the cross-section estimator of an event generator.

## References

* G. P. Lepage, *A new algorithm for adaptive multidimensional integration*,
  J. Comput. Phys. 27 (1978) 192.
* L. Devroye, *Non-Uniform Random Variate Generation*, Springer (1986).
* A. B. Owen, *Monte Carlo theory, methods and examples* (2013), Chapter 9, for the variance of
  the importance-sampling estimator and its optimal proposal.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped ENNReal Topology

namespace EpsilonEridani.ImportanceSampling

variable {α : Type*} {f : α → ℝ} {g : α → ℝ≥0∞}

/-- The importance weight `f x / g x` of a point `x` drawn from the proposal law
`μ.withDensity g`, for the signed target density `f` against `μ`. It is `0` where `g x` is `0`
or `∞`. -/
def weight (f : α → ℝ) (g : α → ℝ≥0∞) (x : α) : ℝ := f x / (g x).toReal

theorem weight_def (f : α → ℝ) (g : α → ℝ≥0∞) (x : α) : weight f g x = f x / (g x).toReal :=
  (rfl)

/-- The weight for the integrand `f * O` is the weight for `f` times the observable `O`. -/
theorem weight_mul (f O : α → ℝ) (g : α → ℝ≥0∞) (x : α) :
    weight (f * O) g x = weight f g x * O x := by
  simp only [weight_def, Pi.mul_apply, mul_div_right_comm]

theorem abs_weight (f : α → ℝ) (g : α → ℝ≥0∞) (x : α) :
    |weight f g x| = weight (fun y => |f y|) g x := by
  simp only [weight_def, abs_div, ENNReal.abs_toReal]

/-- Away from the points where `g` is infinite, or zero while `f` is not, the density times the
weight recovers the target. -/
theorem toReal_mul_weight {x : α} (hx : g x ≠ ∞) (hfg : g x = 0 → f x = 0) :
    (g x).toReal * weight f g x = f x := by
  rcases eq_or_ne (g x) 0 with h | h
  · simp [weight_def, h, hfg h]
  · rw [weight_def, mul_div_cancel₀ _ (ENNReal.toReal_ne_zero.2 ⟨h, hx⟩)]

theorem toReal_mul_weight_sq (f : α → ℝ) (g : α → ℝ≥0∞) (x : α) :
    (g x).toReal * weight f g x ^ 2 = f x ^ 2 / (g x).toReal := by
  rcases eq_or_ne (g x).toReal 0 with h | h
  · simp [weight_def, h]
  · rw [weight_def]
    field_simp

variable [MeasurableSpace α] {μ : Measure α}

theorem aestronglyMeasurable_weight (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEStronglyMeasurable (weight f g) (μ.withDensity g) := by
  rw [show weight f g = fun x => f x / (g x).toReal from funext (weight_def f g)]
  exact (hf.div hg.ennreal_toReal).aestronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous μ g)

/-- **Unbiasedness of importance sampling.** The expected weight under the proposal law is the
integral of the target density. -/
theorem integral_weight (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) :
    ∫ x, weight f g x ∂μ.withDensity g = ∫ x, f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hg hg_top]
  refine integral_congr_ae ?_
  filter_upwards [hg_top, hfg] with x hx hx0
  rw [smul_eq_mul, toReal_mul_weight hx.ne hx0]

/-- The weight is integrable under the proposal law exactly when the target density is
integrable. -/
theorem integrable_weight_iff (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) :
    Integrable (weight f g) (μ.withDensity g) ↔ Integrable f μ := by
  rw [integrable_withDensity_iff_integrable_smul₀' hg hg_top]
  refine integrable_congr ?_
  filter_upwards [hg_top, hfg] with x hx hx0
  rw [smul_eq_mul, toReal_mul_weight hx.ne hx0]

/-- **The weighted sample is a sample of the target.** The proposal law reweighted by the
importance weight is the signed measure with density `f`. -/
theorem withDensityᵥ_weight (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) :
    (μ.withDensity g).withDensityᵥ (weight f g) = μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  · have hfg' : (fun x => (g x).toReal • weight f g x) =ᵐ[μ] f := by
      filter_upwards [hg_top, hfg] with x hx hx0
      rw [smul_eq_mul, toReal_mul_weight hx.ne hx0]
    rw [← withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hg hg_top
      ((integrable_congr hfg').2 hf)]
    exact WithDensityᵥEq.congr_ae hfg'
  · rw [Measure.withDensityᵥ, Measure.withDensityᵥ, dite_eq_right hf,
      dite_eq_right (mt (integrable_weight_iff hg hg_top hfg).1 hf)]

/-- The second moment of the weight under the proposal law is `∫ f² / g dμ`. -/
theorem integral_weight_sq (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞) :
    ∫ x, weight f g x ^ 2 ∂μ.withDensity g = ∫ x, f x ^ 2 / (g x).toReal ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hg hg_top]
  simp only [smul_eq_mul, toReal_mul_weight_sq]

/-- The weight is square-integrable under the proposal law exactly when `f² / g` is integrable
against `μ`. -/
theorem memLp_weight_two_iff (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hg_top : ∀ᵐ x ∂μ, g x < ∞) :
    MemLp (weight f g) 2 (μ.withDensity g) ↔ Integrable (fun x => f x ^ 2 / (g x).toReal) μ := by
  rw [memLp_two_iff_integrable_sq (aestronglyMeasurable_weight hf hg),
    integrable_withDensity_iff_integrable_smul₀' hg hg_top]
  simp only [smul_eq_mul, toReal_mul_weight_sq]

/-- **The variance of the importance weight.** For a normalised proposal density `g`, the variance
of the weight is `∫ f² / g dμ - (∫ f dμ)²`. -/
theorem variance_weight (hg : AEMeasurable g μ) (hg1 : ∫⁻ x, g x ∂μ = 1)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) (hw : MemLp (weight f g) 2 (μ.withDensity g)) :
    variance (weight f g) (μ.withDensity g) =
      ∫ x, f x ^ 2 / (g x).toReal ∂μ - (∫ x, f x ∂μ) ^ 2 := by
  have : IsProbabilityMeasure (μ.withDensity g) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1]⟩
  have hg_top : ∀ᵐ x ∂μ, g x < ∞ := ae_lt_top' hg (by simp [hg1])
  rw [variance_eq_sub hw]
  simp only [Pi.pow_apply]
  rw [integral_weight_sq hg hg_top, integral_weight hg hg_top hfg]

/-- **No proposal beats `|f|`.** For every normalised proposal density, the variance of the
importance weight is at least `(∫ |f| dμ)² - (∫ f dμ)²`. -/
theorem sq_integral_abs_sub_sq_integral_le_variance_weight (hg : AEMeasurable g μ)
    (hg1 : ∫⁻ x, g x ∂μ = 1) (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (hw : MemLp (weight f g) 2 (μ.withDensity g)) :
    (∫ x, |f x| ∂μ) ^ 2 - (∫ x, f x ∂μ) ^ 2 ≤ variance (weight f g) (μ.withDensity g) := by
  have : IsProbabilityMeasure (μ.withDensity g) :=
    ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1]⟩
  have hg_top : ∀ᵐ x ∂μ, g x < ∞ := ae_lt_top' hg (by simp [hg1])
  -- The mean of `|weight f g|` is `∫ |f| dμ`, and its square is at most the second moment.
  have habs : ∫ x, |weight f g x| ∂μ.withDensity g = ∫ x, |f x| ∂μ := by
    simp_rw [abs_weight]
    exact integral_weight hg hg_top (by filter_upwards [hfg] with x hx h0 using by simp [hx h0])
  have h2 := variance_nonneg (|weight f g|) (μ.withDensity g)
  rw [variance_eq_sub hw.abs] at h2
  rw [variance_eq_sub hw]
  simp only [Pi.pow_apply, Pi.abs_apply, sq_abs] at h2 ⊢
  rw [habs] at h2
  rw [integral_weight hg hg_top hfg]
  linarith

/-- The variance-minimising proposal density `|f| / ∫ |f| dμ`. -/
def optimalProposal (f : α → ℝ) (μ : Measure α) (x : α) : ℝ≥0∞ :=
  ENNReal.ofReal (|f x| / ∫ y, |f y| ∂μ)

theorem optimalProposal_def (f : α → ℝ) (μ : Measure α) (x : α) :
    optimalProposal f μ x = ENNReal.ofReal (|f x| / ∫ y, |f y| ∂μ) :=
  (rfl)

@[simp]
theorem toReal_optimalProposal (f : α → ℝ) (μ : Measure α) (x : α) :
    (optimalProposal f μ x).toReal = |f x| / ∫ y, |f y| ∂μ :=
  ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _))

theorem aemeasurable_optimalProposal (hf : AEMeasurable f μ) :
    AEMeasurable (optimalProposal f μ) μ :=
  ((continuous_abs.measurable.comp_aemeasurable hf).div_const _).ennreal_ofReal

/-- The optimal proposal is a probability density. -/
theorem lintegral_optimalProposal (hf : Integrable f μ) (hf0 : ∫ x, |f x| ∂μ ≠ 0) :
    ∫⁻ x, optimalProposal f μ x ∂μ = 1 := by
  simp only [optimalProposal_def]
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.abs.div_const _)
    (ae_of_all _ fun _ => div_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)),
    integral_div, div_self hf0, ENNReal.ofReal_one]

/-- The optimal proposal vanishes only where `f` does. -/
theorem eq_zero_of_optimalProposal_eq_zero (hf0 : ∫ x, |f x| ∂μ ≠ 0) {x : α}
    (hx : optimalProposal f μ x = 0) : f x = 0 := by
  rw [optimalProposal_def, ENNReal.ofReal_eq_zero,
    div_le_iff₀ ((integral_nonneg fun _ => abs_nonneg _).lt_of_ne' hf0), zero_mul] at hx
  exact abs_nonpos_iff.1 hx

/-- Against the optimal proposal, `f² / g` is `(∫ |f| dμ) |f|`. -/
theorem sq_div_toReal_optimalProposal (hf0 : ∫ x, |f x| ∂μ ≠ 0) (x : α) :
    f x ^ 2 / (optimalProposal f μ x).toReal = (∫ y, |f y| ∂μ) * |f x| := by
  rw [toReal_optimalProposal]
  rcases eq_or_ne (f x) 0 with h | h
  · simp [h]
  · have : |f x| ≠ 0 := abs_ne_zero.2 h
    rw [← sq_abs]
    field_simp

/-- **The optimal proposal attains the variance bound.** With the proposal
`|f| / ∫ |f| dμ`, the variance of the weight is exactly `(∫ |f| dμ)² - (∫ f dμ)²`. -/
theorem variance_weight_optimalProposal (hf : Integrable f μ) (hf0 : ∫ x, |f x| ∂μ ≠ 0) :
    variance (weight f (optimalProposal f μ)) (μ.withDensity (optimalProposal f μ)) =
      (∫ x, |f x| ∂μ) ^ 2 - (∫ x, f x ∂μ) ^ 2 := by
  have hg := aemeasurable_optimalProposal (μ := μ) hf.aemeasurable
  have hfg : ∀ᵐ x ∂μ, optimalProposal f μ x = 0 → f x = 0 :=
    ae_of_all _ fun _ => eq_zero_of_optimalProposal_eq_zero hf0
  have hsq : (fun x => f x ^ 2 / (optimalProposal f μ x).toReal) =
      fun x => (∫ y, |f y| ∂μ) * |f x| := funext (sq_div_toReal_optimalProposal hf0)
  have hw : MemLp (weight f (optimalProposal f μ)) 2 (μ.withDensity (optimalProposal f μ)) := by
    rw [memLp_weight_two_iff hf.aemeasurable hg (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), hsq]
    exact hf.abs.const_mul _
  rw [variance_weight hg (lintegral_optimalProposal hf hf0) hfg hw, hsq, integral_const_mul]
  ring

/-- For a non-negative target density, the optimal proposal has zero variance. -/
theorem variance_weight_optimalProposal_of_nonneg (hf : Integrable f μ) (hf0 : ∫ x, |f x| ∂μ ≠ 0)
    (hpos : 0 ≤ᵐ[μ] f) :
    variance (weight f (optimalProposal f μ)) (μ.withDensity (optimalProposal f μ)) = 0 := by
  rw [variance_weight_optimalProposal hf hf0,
    integral_congr_ae (hpos.mono fun x hx => abs_of_nonneg hx), sub_self]

section Estimator

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → α}

/-- **The estimator is unbiased for every sample size.** For draws `X i` from the proposal law,
the average weight of the first `n ≥ 1` draws has expectation `∫ f dμ`. No independence is
needed. -/
theorem integral_average_weight (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hg_top : ∀ᵐ x ∂μ, g x < ∞) (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (hX : ∀ i, HasLaw (X i) (μ.withDensity g) P) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, weight f g (X i ω) ∂P = ∫ x, f x ∂μ := by
  have hw := aestronglyMeasurable_weight hf.aemeasurable hg
  have hwi := (integrable_weight_iff hg hg_top hfg).2 hf
  rw [integral_const_mul, integral_finsetSum _ fun i _ => (hX i).integrable_fun_comp hwi]
  have hi : ∀ i, ∫ ω, weight f g (X i ω) ∂P = ∫ x, f x ∂μ := fun i => by
    simpa only [Function.comp_apply, integral_weight hg hg_top hfg] using (hX i).integral_comp hw
  simp only [hi, sum_const, card_range, nsmul_eq_mul]
  field_simp

/-- **The estimator converges almost surely.** For pairwise independent draws `X i` from the
proposal law, the average weight `(1/n) ∑_{i < n} weight f g (X i)` converges almost surely to
`∫ f dμ`. This is Mathlib's strong law of large numbers applied to the weights. -/
theorem ae_tendsto_average_weight (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hg_top : ∀ᵐ x ∂μ, g x < ∞) (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (hX : ∀ i, HasLaw (X i) (μ.withDensity g) P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, weight f g (X i ω)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  have hw := aestronglyMeasurable_weight hf.aemeasurable hg
  have hwi := (integrable_weight_iff hg hg_top hfg).2 hf
  have hwm : ∀ i, AEMeasurable (weight f g) (P.map (X i)) := fun i => by
    rw [(hX i).map_eq]
    exact hw.aemeasurable
  have hident : ∀ i, IdentDistrib (weight f g ∘ X i) (weight f g ∘ X 0) P P := fun i =>
    IdentDistrib.comp_of_aemeasurable
      { aemeasurable_fst := (hX i).aemeasurable
        aemeasurable_snd := (hX 0).aemeasurable
        map_eq := by rw [(hX i).map_eq, (hX 0).map_eq] } (hwm i)
  have key := strong_law_ae (fun i => weight f g ∘ X i) ((hX 0).integrable_comp hwi)
    (fun i j hij => (hindep hij).comp₀ (hX i).aemeasurable (hX j).aemeasurable (hwm i) (hwm j))
    hident
  rw [(hX 0).integral_comp hw, integral_weight hg hg_top hfg] at key
  simpa only [smul_eq_mul, Function.comp_apply] using key

end Estimator

end EpsilonEridani.ImportanceSampling
