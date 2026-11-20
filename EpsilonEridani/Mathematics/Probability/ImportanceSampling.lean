/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.MeasureTheory.WithDensity
public import EpsilonEridani.Mathematics.Probability.MonteCarloAverage
public import Mathlib.Basic.Real.Sign
public import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.VectorMeasure.WithDensity
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.Variance

/-!
# Importance sampling and the weighted Monte Carlo estimator

To integrate a signed density `f` against a measure `μ`, importance sampling draws points from
a *proposal* law `μ.withDensity g`, with `g` a density against `μ`, and gives each point `x` the
*weight* `f x / g x` (`ImportanceSampling.weight f g`). The weight is real-valued and may be
negative, as the weights of an event generator with negative-weight events are.

The standing hypotheses are the ones an implementation needs: `g` is almost everywhere finite,
and `g` vanishes only where `f` does (`∀ᵐ x ∂μ, g x = 0 → f x = 0`), so that every region where
`f` has mass is ever proposed. Under them:

* `integral_weight`: the expected weight under the proposal is `∫ f dμ`, so the mean weight is an
  unbiased estimator of the integral. An observable `O` is estimated with the weight of `f * O`,
  which is `weight f g * O` (`weight_mul`), so its expectation is `∫ f O dμ`
  (`integral_weight_mul`).
* `withDensityᵥ_weight`: the proposal law reweighted by `weight f g` is the signed measure with
  density `f`. This is the statement that a weighted sample is a sample of `f`.

The variance results additionally assume a normalised proposal (`∫⁻ g dμ = 1`, which also makes
`g` almost everywhere finite) and a square-integrable weight (`MemLp (weight f g) 2`; otherwise
Mathlib's `variance` is `0`):

* `variance_weight`: the variance of the weight is `∫ f² / g dμ - (∫ f dμ)²`.
* `sq_integral_abs_sub_sq_integral_le_variance_weight` and
  `variance_weight_optimalProposal`: that variance is at least `(∫ |f| dμ)² - (∫ f dμ)²` for
  every such proposal, and the proposal `|f| / ∫ |f| dμ` (`optimalProposal`) attains the bound.
  The optimal proposal gives every point the weight `(∫ |f| dμ) · sign (f x)`
  (`weight_optimalProposal`), so for a non-negative `f` it has zero variance
  (`variance_weight_optimalProposal_eq_zero_of_nonneg`).

For the estimator built from draws `X i`:

* `integral_inv_mul_sum_weight`: for any draws with the proposal law, independent or not, the
  average `(1/n) ∑_{i < n} weight f g (X i)` has expectation `∫ f dμ` for every `n ≥ 1`.
* `ae_tendsto_inv_mul_sum_weight`: for pairwise independent draws with the proposal law, that
  average converges to `∫ f dμ` almost surely, by Mathlib's strong law of large numbers. This is
  the convergence of the cross-section estimator of an event generator.

Both are instances of `EpsilonEridani.MonteCarlo.integral_inv_smul_sum` and
`EpsilonEridani.MonteCarlo.ae_tendsto_inv_smul_sum`, the same statements for an arbitrary
integrable observable of draws with an arbitrary law.

## References

* G. P. Lepage, *A new algorithm for adaptive multidimensional integration*,
  J. Comput. Phys. 27 (1978) 192.
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

theorem weight_apply (f : α → ℝ) (g : α → ℝ≥0∞) (x : α) : weight f g x = f x / (g x).toReal :=
  (rfl)

/-- The weight for the integrand `f * O` is the weight for `f` times the observable `O`. -/
theorem weight_mul (f O : α → ℝ) (g : α → ℝ≥0∞) (x : α) :
    weight (f * O) g x = weight f g x * O x := by
  simp only [weight_apply, Pi.mul_apply, mul_div_right_comm]

theorem abs_weight (f : α → ℝ) (g : α → ℝ≥0∞) (x : α) :
    |weight f g x| = weight (fun y => |f y|) g x := by
  simp only [weight_apply, abs_div, ENNReal.abs_toReal]

/-- Away from the points where `g` is infinite, or zero while `f` is not, the density times the
weight recovers the target. -/
theorem toReal_mul_weight {x : α} (hx : g x ≠ ∞) (hfg : g x = 0 → f x = 0) :
    (g x).toReal * weight f g x = f x := by
  rcases eq_or_ne (g x) 0 with h | h
  · simp [weight_apply, h, hfg h]
  · rw [weight_apply, mul_div_cancel₀ _ (ENNReal.toReal_ne_zero.2 ⟨h, hx⟩)]

theorem toReal_mul_weight_sq (f : α → ℝ) (g : α → ℝ≥0∞) (x : α) :
    (g x).toReal * weight f g x ^ 2 = f x ^ 2 / (g x).toReal := by
  rcases eq_or_ne (g x).toReal 0 with h | h
  · simp [weight_apply, h]
  · rw [weight_apply]
    field_simp

variable [MeasurableSpace α] {μ : Measure α}

theorem aestronglyMeasurable_weight (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    AEStronglyMeasurable (weight f g) (μ.withDensity g) := by
  exact (hf.div hg.ennreal_toReal).aestronglyMeasurable.mono_ac
    (withDensity_absolutelyContinuous μ g)

/-- Almost everywhere, the density times the weight recovers the target. -/
theorem toReal_smul_weight_ae_eq (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) :
    (fun x => (g x).toReal • weight f g x) =ᵐ[μ] f := by
  filter_upwards [hg_top, hfg] with x hx hx0
  rw [smul_eq_mul, toReal_mul_weight hx.ne hx0]

/-- **Unbiasedness of importance sampling.** The expected weight under the proposal law is the
integral of the target density. -/
theorem integral_weight (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) :
    ∫ x, weight f g x ∂μ.withDensity g = ∫ x, f x ∂μ := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hg hg_top]
  exact integral_congr_ae (toReal_smul_weight_ae_eq hg_top hfg)

/-- **Importance-sampled observables.** The expectation of `weight f g * O` under the proposal law
is `∫ f O dμ`. -/
theorem integral_weight_mul (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) (O : α → ℝ) :
    ∫ x, weight f g x * O x ∂μ.withDensity g = ∫ x, f x * O x ∂μ := by
  simp_rw [← weight_mul]
  exact integral_weight hg hg_top (by filter_upwards [hfg] with x hx h0 using by simp [hx h0])

/-- The weight is integrable under the proposal law exactly when the target density is
integrable. -/
theorem integrable_weight_iff (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) :
    Integrable (weight f g) (μ.withDensity g) ↔ Integrable f μ := by
  rw [integrable_withDensity_iff_integrable_smul₀' hg hg_top]
  exact integrable_congr (toReal_smul_weight_ae_eq hg_top hfg)

/-- **The weighted sample is a sample of the target.** The proposal law reweighted by the
importance weight is the signed measure with density `f`. -/
theorem withDensityᵥ_weight (hg : AEMeasurable g μ) (hg_top : ∀ᵐ x ∂μ, g x < ∞)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) :
    (μ.withDensity g).withDensityᵥ (weight f g) = μ.withDensityᵥ f := by
  by_cases hf : Integrable f μ
  · have hfg' := toReal_smul_weight_ae_eq hg_top hfg
    rw [← withDensityᵥ_smul_eq_withDensityᵥ_withDensity' hg hg_top
      ((integrable_congr hfg').2 hf)]
    exact WithDensityᵥEq.congr_ae hfg'
  · rw [withDensityᵥ_eq_zero_of_not_integrable hf, withDensityᵥ_eq_zero_of_not_integrable
      (mt (integrable_weight_iff hg hg_top hfg).1 hf)]

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

/-- **The variance of the importance weight.** For a normalised proposal density `g` whose weight
is square-integrable, the variance of the weight is `∫ f² / g dμ - (∫ f dμ)²`. -/
theorem variance_weight (hg : AEMeasurable g μ) (hg1 : ∫⁻ x, g x ∂μ = 1)
    (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0) (hw : MemLp (weight f g) 2 (μ.withDensity g)) :
    variance (weight f g) (μ.withDensity g) =
      ∫ x, f x ^ 2 / (g x).toReal ∂μ - (∫ x, f x ∂μ) ^ 2 := by
  have := isProbabilityMeasure_withDensity hg1
  have hg_top : ∀ᵐ x ∂μ, g x < ∞ := ae_lt_top' hg (by simp [hg1])
  rw [variance_eq_sub hw]
  simp only [Pi.pow_apply]
  rw [integral_weight_sq hg hg_top, integral_weight hg hg_top hfg]

/-- **No proposal beats `|f|`.** For every normalised proposal density whose weight is
square-integrable, the variance of the importance weight is at least `(∫ |f| dμ)² - (∫ f dμ)²`. -/
theorem sq_integral_abs_sub_sq_integral_le_variance_weight (hg : AEMeasurable g μ)
    (hg1 : ∫⁻ x, g x ∂μ = 1) (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (hw : MemLp (weight f g) 2 (μ.withDensity g)) :
    (∫ x, |f x| ∂μ) ^ 2 - (∫ x, f x ∂μ) ^ 2 ≤ variance (weight f g) (μ.withDensity g) := by
  -- The weight of `|f|` is `|weight f g|`. Its variance, `∫ f² / g dμ - (∫ |f| dμ)²` by
  -- `variance_weight`, is non-negative.
  have habs : weight (fun y => |f y|) g = |weight f g| := funext fun x => (abs_weight f g x).symm
  have h := variance_nonneg (weight (fun y => |f y|) g) (μ.withDensity g)
  rw [variance_weight hg hg1 (by filter_upwards [hfg] with x hx h0 using by simp [hx h0])
    (habs ▸ hw.abs)] at h
  rw [variance_weight hg hg1 hfg hw]
  simp only [sq_abs] at h
  linarith

/-- The variance-minimising proposal density `|f| / ∫ |f| dμ`. -/
def optimalProposal (f : α → ℝ) (μ : Measure α) (x : α) : ℝ≥0∞ :=
  ENNReal.ofReal (|f x| / ∫ y, |f y| ∂μ)

theorem optimalProposal_apply (f : α → ℝ) (μ : Measure α) (x : α) :
    optimalProposal f μ x = ENNReal.ofReal (|f x| / ∫ y, |f y| ∂μ) :=
  (rfl)

@[simp]
theorem toReal_optimalProposal (f : α → ℝ) (μ : Measure α) (x : α) :
    (optimalProposal f μ x).toReal = |f x| / ∫ y, |f y| ∂μ :=
  ENNReal.toReal_ofReal (div_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _))

/-- The optimal proposal density is finite everywhere. -/
theorem optimalProposal_lt_top (f : α → ℝ) (μ : Measure α) (x : α) : optimalProposal f μ x < ∞ :=
  ENNReal.ofReal_lt_top

theorem aemeasurable_optimalProposal (hf : AEMeasurable f μ) :
    AEMeasurable (optimalProposal f μ) μ :=
  (hf.abs.div_const _).ennreal_ofReal

/-- The optimal proposal is a probability density. -/
theorem lintegral_optimalProposal_eq_one (hf : Integrable f μ) (hf0 : ∫ x, |f x| ∂μ ≠ 0) :
    ∫⁻ x, optimalProposal f μ x ∂μ = 1 := by
  simp only [optimalProposal_apply]
  rw [← ofReal_integral_eq_lintegral_ofReal (hf.abs.div_const _)
    (ae_of_all _ fun _ => div_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)),
    integral_div, div_self hf0, ENNReal.ofReal_one]

/-- The optimal proposal law is a probability measure. -/
theorem isProbabilityMeasure_withDensity_optimalProposal (hf : Integrable f μ)
    (hf0 : ∫ x, |f x| ∂μ ≠ 0) : IsProbabilityMeasure (μ.withDensity (optimalProposal f μ)) :=
  isProbabilityMeasure_withDensity (lintegral_optimalProposal_eq_one hf hf0)

/-- The optimal proposal vanishes exactly where `f` does. -/
theorem optimalProposal_eq_zero_iff (hf0 : ∫ x, |f x| ∂μ ≠ 0) {x : α} :
    optimalProposal f μ x = 0 ↔ f x = 0 := by
  rw [optimalProposal_apply, ENNReal.ofReal_eq_zero,
    div_le_iff₀ ((integral_nonneg fun _ => abs_nonneg _).lt_of_ne' hf0), zero_mul,
    abs_nonpos_iff]

/-- **The optimal proposal fixes the weight magnitude.** Against the optimal proposal the weight is
`(∫ |f| dμ) · sign (f x)`, of constant magnitude wherever `f x ≠ 0`
(`abs_weight_optimalProposal`). -/
@[simp]
theorem weight_optimalProposal (f : α → ℝ) (μ : Measure α) (x : α) :
    weight f (optimalProposal f μ) x = (∫ y, |f y| ∂μ) * Real.sign (f x) := by
  rw [weight_apply, toReal_optimalProposal]
  rcases eq_or_ne (∫ y, |f y| ∂μ) 0 with hc | hc
  · simp [hc]
  rcases lt_trichotomy (f x) 0 with h | h | h
  · rw [abs_of_neg h, Real.sign_of_neg h]
    field_simp [h.ne]
  · simp [h]
  · rw [abs_of_pos h, Real.sign_of_pos h]
    field_simp [h.ne']

/-- Against the optimal proposal, every point where `f` does not vanish has weight of magnitude
`∫ |f| dμ`. -/
theorem abs_weight_optimalProposal {x : α} (hx : f x ≠ 0) :
    |weight f (optimalProposal f μ) x| = ∫ y, |f y| ∂μ := by
  rw [weight_optimalProposal, abs_mul, abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
  rcases Real.sign_apply_eq_of_ne_zero _ hx with h | h <;> simp [h]

/-- Against the optimal proposal, `f² / g` is `(∫ |f| dμ) |f|`. -/
theorem sq_div_toReal_optimalProposal (f : α → ℝ) (μ : Measure α) (x : α) :
    f x ^ 2 / (optimalProposal f μ x).toReal = (∫ y, |f y| ∂μ) * |f x| := by
  rw [toReal_optimalProposal]
  rcases eq_or_ne (∫ y, |f y| ∂μ) 0 with hc | hc
  · simp [hc]
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
    ae_of_all _ fun _ => (optimalProposal_eq_zero_iff hf0).1
  have hsq : (fun x => f x ^ 2 / (optimalProposal f μ x).toReal) =
      fun x => (∫ y, |f y| ∂μ) * |f x| := funext (sq_div_toReal_optimalProposal f μ)
  have hw : MemLp (weight f (optimalProposal f μ)) 2 (μ.withDensity (optimalProposal f μ)) := by
    rw [memLp_weight_two_iff hf.aemeasurable hg (ae_of_all _ (optimalProposal_lt_top f μ)), hsq]
    exact hf.abs.const_mul _
  rw [variance_weight hg (lintegral_optimalProposal_eq_one hf hf0) hfg hw, hsq, integral_const_mul]
  ring

/-- For a non-negative target density, the optimal proposal has zero variance. -/
theorem variance_weight_optimalProposal_eq_zero_of_nonneg (hf : Integrable f μ)
    (hf0 : ∫ x, |f x| ∂μ ≠ 0) (hpos : 0 ≤ᵐ[μ] f) :
    variance (weight f (optimalProposal f μ)) (μ.withDensity (optimalProposal f μ)) = 0 := by
  rw [variance_weight_optimalProposal hf hf0,
    integral_congr_ae (hpos.mono fun x hx => abs_of_nonneg hx), sub_self]

section Estimator

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → α}

/-- **The estimator is unbiased for every sample size.** For draws `X i` from the proposal law,
the average weight of the first `n ≥ 1` draws has expectation `∫ f dμ`. No independence is
needed. -/
theorem integral_inv_mul_sum_weight (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hg_top : ∀ᵐ x ∂μ, g x < ∞) (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (hX : ∀ i, HasLaw (X i) (μ.withDensity g) P) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, (n : ℝ)⁻¹ * ∑ i ∈ range n, weight f g (X i ω) ∂P = ∫ x, f x ∂μ := by
  simpa only [smul_eq_mul, integral_weight hg hg_top hfg] using
    MonteCarlo.integral_inv_smul_sum ((integrable_weight_iff hg hg_top hfg).2 hf) hX hn

/-- **The estimator converges almost surely.** For pairwise independent draws `X i` from the
proposal law, the average weight `(1/n) ∑_{i < n} weight f g (X i)` converges almost surely to
`∫ f dμ`. This is Mathlib's strong law of large numbers applied to the weights. -/
theorem ae_tendsto_inv_mul_sum_weight (hf : Integrable f μ) (hg : AEMeasurable g μ)
    (hg_top : ∀ᵐ x ∂μ, g x < ∞) (hfg : ∀ᵐ x ∂μ, g x = 0 → f x = 0)
    (hX : ∀ i, HasLaw (X i) (μ.withDensity g) P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∑ i ∈ range n, weight f g (X i ω)) atTop
      (𝓝 (∫ x, f x ∂μ)) := by
  simpa only [smul_eq_mul, integral_weight hg hg_top hfg] using
    MonteCarlo.ae_tendsto_inv_smul_sum ((integrable_weight_iff hg hg_top hfg).2 hf) hX hindep

end Estimator

end EpsilonEridani.ImportanceSampling
