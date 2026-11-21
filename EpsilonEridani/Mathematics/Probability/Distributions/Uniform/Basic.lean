/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import TauCeti.Probability.Distributions.Uniform.Basic
public import EpsilonEridani.Mathematics.MeasureTheory.Measure.Prod

/-!
# Further facts about the uniform measure

This file extends `TauCeti.Probability.Distributions.Uniform.Basic` with the facts about the
uniform law needed to thin a proposal by an independent uniform variate: keep a draw `x` when a
standard uniform variate lies below `a x`. That is the mechanism behind acceptance–rejection
sampling, analysed in `EpsilonEridani.Mathematics.Probability.AcceptReject`, and the worked
examples there integrate continuous targets against the standard uniform law.

## Main results

* `EpsilonEridani.uniformMeasure_Iic`: the uniform measure of a closed lower tail, the companion
  of `TauCeti.Probability.uniformMeasure_Iio`.
* `EpsilonEridani.integrable_uniformMeasure_iff`: on a nondegenerate interval, integrability
  against the uniform law is integrability on `Set.Ioc a b` for Lebesgue measure.
* `ContinuousOn.integrable_uniformMeasure`: a function continuous on `Set.Icc a b` is integrable
  against every uniform measure.
* `EpsilonEridani.lintegral_ofReal_uniformMeasure`: the lower integral of an integrable,
  almost everywhere nonnegative function against the uniform law, as an interval integral
  divided by the interval length.
* `EpsilonEridani.lintegral_one_add_sq_div_two_uniformMeasure_zero_one` and
  `EpsilonEridani.lintegral_min_two_mul_three_div_two_uniformMeasure_zero_one`: the integrals of
  the acceptance–rejection example targets against the standard uniform law, with
  `EpsilonEridani.ae_one_add_sq_div_two_le_one_uniformMeasure_zero_one`, the bound of the first.
* `MeasureTheory.Measure.map_fst_restrict_setOf_le_prod_uniformMeasure_zero_one`: thinning by a
  uniform variate. Keeping a proposal `x` when an independent standard uniform variate lies
  below `a x` multiplies its law by the density `min (a x) 1`, clipped at `0`.
-/

public section

open MeasureTheory TauCeti.Probability

namespace EpsilonEridani

/-- On a nondegenerate interval, a function is integrable against the uniform law exactly when it
is integrable on `Set.Ioc a b` for Lebesgue measure: the two measures differ by the positive,
finite factor `b - a`. -/
theorem integrable_uniformMeasure_iff {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b : ℝ}
    (hab : a < b) : Integrable f (uniformMeasure a b) ↔ IntegrableOn f (Set.Ioc a b) := by
  rw [uniformMeasure_eq_smul]
  exact integrable_smul_measure (by simp) (by simp [hab])

end EpsilonEridani

/-- A function continuous on `Set.Icc a b` is integrable against the uniform measure on any
interval: on a nondegenerate interval it is bounded there, and on a degenerate one the measure
is zero. -/
theorem ContinuousOn.integrable_uniformMeasure {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) : Integrable f (uniformMeasure a b) := by
  rcases le_or_gt b a with hba | hab
  · simp [uniformMeasure_eq_zero_of_le hba]
  exact (EpsilonEridani.integrable_uniformMeasure_iff hab).mpr
    (hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)

namespace EpsilonEridani

/-- The uniform measure of a closed lower tail: the fraction of `Set.Ioc a b` lying below `t`,
which is `0` below the interval and `1` above it. -/
theorem uniformMeasure_Iic {a b : ℝ} (hab : a < b) (t : ℝ) :
    uniformMeasure a b (Set.Iic t) = ENNReal.ofReal ((min t b - a) / (b - a)) := by
  have hset : Set.Iic t ∩ Set.Ioc a b = Set.Ioc a (min t b) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
    tauto
  rw [uniformMeasure_apply measurableSet_Iic, hset, Real.volume_Ioc,
    ENNReal.ofReal_div_of_pos (sub_pos.mpr hab), ENNReal.div_eq_inv_mul]

/-- The lower integral of an integrable, almost everywhere nonnegative `f` against the uniform
law on `Set.Ioc a b` is the interval integral of `f` over `[a, b]` divided by the interval
length. -/
theorem lintegral_ofReal_uniformMeasure {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Integrable f (uniformMeasure a b)) (hf₀ : 0 ≤ᵐ[uniformMeasure a b] f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂uniformMeasure a b =
      ENNReal.ofReal ((∫ x in a..b, f x) / (b - a)) := by
  rw [uniformMeasure_eq_smul,
    Measure.ae_ennreal_smul_measure_eq (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)] at hf₀
  rw [uniformMeasure_eq_smul, lintegral_smul_measure, smul_eq_mul,
    ← ofReal_integral_eq_lintegral_ofReal ((integrable_uniformMeasure_iff hab).mp hf) hf₀,
    ← intervalIntegral.integral_of_le hab.le, ENNReal.ofReal_div_of_pos (sub_pos.mpr hab),
    ENNReal.div_eq_inv_mul]

/-- The function `(1 + z ^ 2) / 2` is bounded by `1` almost everywhere for the standard uniform
law. It is the bound hypothesis of the acceptance–rejection example in
`EpsilonEridani.Mathematics.Probability.AcceptReject` with constant proposal and bound `1`. -/
theorem ae_one_add_sq_div_two_le_one_uniformMeasure_zero_one :
    ∀ᵐ z ∂uniformMeasure 0 1, (1 + z ^ 2) / 2 ≤ 1 := by
  filter_upwards [ae_mem_Ioc_uniformMeasure] with z hz
  nlinarith [hz.1, hz.2]

/-- The function `(1 + z ^ 2) / 2` has integral `2 / 3` over `[0, 1]`. It is the target of the
acceptance–rejection example in `EpsilonEridani.Mathematics.Probability.AcceptReject`, and its
integral is that example's acceptance probability. -/
theorem lintegral_one_add_sq_div_two_uniformMeasure_zero_one :
    ∫⁻ z, ENNReal.ofReal ((1 + z ^ 2) / 2) ∂uniformMeasure 0 1 = ENNReal.ofReal (2 / 3) := by
  have hcont : Continuous fun z : ℝ => (1 + z ^ 2) / 2 := by fun_prop
  rw [lintegral_ofReal_uniformMeasure zero_lt_one hcont.continuousOn.integrable_uniformMeasure
    (ae_of_all _ fun z => by positivity), sub_zero, div_one]
  norm_num [intervalIntegral.integral_div, integral_pow]

/-- The clipped function `min (2 * z) (3 / 2)` has integral `15 / 16` over `[0, 1]`. It is the
clipped target of the acceptance–rejection example in
`EpsilonEridani.Mathematics.Probability.AcceptReject`. -/
theorem lintegral_min_two_mul_three_div_two_uniformMeasure_zero_one :
    ∫⁻ z, ENNReal.ofReal (min (2 * z) (3 / 2)) ∂uniformMeasure 0 1 = ENNReal.ofReal (15 / 16) := by
  have hcont : Continuous fun z : ℝ => min (2 * z) (3 / 2) := by fun_prop
  rw [lintegral_ofReal_uniformMeasure zero_lt_one hcont.continuousOn.integrable_uniformMeasure
    (by
      filter_upwards [ae_mem_Ioc_uniformMeasure] with x hx
      rw [Pi.zero_apply]
      exact le_min (by linarith [hx.1]) (by norm_num)), sub_zero, div_one]
  -- Split `[0, 1]` at the crossing point `3 / 4`, where `2 * z` meets the bound.
  have hlo : ∫ z in (0 : ℝ)..3 / 4, min (2 * z) (3 / 2) = ∫ z in (0 : ℝ)..3 / 4, 2 * z :=
    intervalIntegral.integral_congr fun z hz => by
      rw [Set.uIcc_of_le (by norm_num)] at hz
      exact min_eq_left (by linarith [hz.2])
  have hhi : ∫ z in (3 / 4 : ℝ)..1, min (2 * z) (3 / 2) = ∫ _ in (3 / 4 : ℝ)..1, (3 / 2 : ℝ) :=
    intervalIntegral.integral_congr fun z hz => by
      rw [Set.uIcc_of_le (by norm_num)] at hz
      exact min_eq_right (by linarith [hz.1])
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 3 / 4)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hlo, hhi,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  norm_num

end EpsilonEridani

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- **Thinning by a uniform variate.** Draw `x` from `ν` and an independent standard uniform
variate `u`, and keep `x` when `u ≤ a x`. The kept part of the law of `x` is `ν` with density
`min (a x) 1`, read as `0` where `a x` is negative. -/
theorem map_fst_restrict_setOf_le_prod_uniformMeasure_zero_one (ν : Measure α) {a : α → ℝ}
    (ha : Measurable a) :
    ((ν.prod (uniformMeasure 0 1)).restrict {p | p.2 ≤ a p.1}).map Prod.fst =
      ν.withDensity fun x => ENNReal.ofReal (min (a x) 1) := by
  have hs : MeasurableSet {p : α × ℝ | p.2 ≤ a p.1} :=
    measurableSet_le measurable_snd (ha.comp measurable_fst)
  rw [ν.map_fst_restrict_prod _ hs]
  congr 1
  funext x
  have hslice : Prod.mk x ⁻¹' {p : α × ℝ | p.2 ≤ a p.1} = Set.Iic (a x) := by
    ext u
    simp
  rw [hslice, EpsilonEridani.uniformMeasure_Iic zero_lt_one]
  simp

end MeasureTheory.Measure
