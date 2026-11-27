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
* `EpsilonEridani.integrable_uniformMeasure_iff`: integrability against the uniform law is
  integrability on `Set.Ioc a b` for Lebesgue measure, with no hypothesis on the interval.
* `ContinuousOn.integrable_uniformMeasure`: a function continuous on `Set.Icc a b` is integrable
  against `uniformMeasure a b`, with no nondegeneracy hypothesis on the interval.
* `EpsilonEridani.lintegral_uniformMeasure`: the lower integral of any extended nonnegative
  function against the uniform law, as a lower integral over `Set.Ioc a b` divided by the
  interval length, with no hypothesis.
* `EpsilonEridani.lintegral_ofReal_uniformMeasure`: the lower integral of an integrable,
  almost everywhere nonnegative function against the uniform law, as an interval integral
  divided by the interval length.
* `MeasureTheory.Measure.map_fst_restrict_setOf_le_prod_uniformMeasure_zero_one`: thinning by a
  uniform variate. Keeping a proposal `x` when an independent standard uniform variate lies
  below `a x` multiplies its law by the density `min (a x) 1`, clipped at `0`.
-/

public section

open MeasureTheory TauCeti.Probability

open scoped ENNReal

namespace EpsilonEridani

/-- A function is integrable against the uniform law exactly when it is integrable on
`Set.Ioc a b` for Lebesgue measure. On a nondegenerate interval the two measures differ by the
positive, finite factor `b - a`; on a degenerate one both are the zero measure. -/
theorem integrable_uniformMeasure_iff {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a b : ℝ} :
    Integrable f (uniformMeasure a b) ↔ IntegrableOn f (Set.Ioc a b) := by
  rcases le_or_gt b a with hba | hab
  · simp [uniformMeasure_eq_zero_of_le hba, Set.Ioc_eq_empty_of_le hba]
  rw [uniformMeasure_eq_smul]
  exact integrable_smul_measure (by simp) (by simp [hab])

end EpsilonEridani

/-- A function continuous on `Set.Icc a b` is integrable against `uniformMeasure a b`, with no
nondegeneracy hypothesis on the interval: the degenerate case is the zero measure. -/
theorem ContinuousOn.integrable_uniformMeasure {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) : Integrable f (uniformMeasure a b) :=
  EpsilonEridani.integrable_uniformMeasure_iff.mpr
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

/-- The lower integral of any `k : ℝ → ℝ≥0∞` against the uniform law on `Set.Ioc a b` is its
lower integral over `Set.Ioc a b` for Lebesgue measure, divided by the interval length. -/
theorem lintegral_uniformMeasure (k : ℝ → ℝ≥0∞) (a b : ℝ) :
    ∫⁻ x, k x ∂uniformMeasure a b = (ENNReal.ofReal (b - a))⁻¹ * ∫⁻ x in Set.Ioc a b, k x := by
  rw [uniformMeasure_eq_smul, lintegral_smul_measure, smul_eq_mul]

/-- The lower integral of an integrable, almost everywhere nonnegative `f` against the uniform
law on `Set.Ioc a b` is the interval integral of `f` over `[a, b]` divided by the interval
length. -/
theorem lintegral_ofReal_uniformMeasure {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : Integrable f (uniformMeasure a b)) (hf₀ : 0 ≤ᵐ[uniformMeasure a b] f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂uniformMeasure a b =
      ENNReal.ofReal ((∫ x in a..b, f x) / (b - a)) := by
  rw [uniformMeasure_eq_smul,
    Measure.ae_ennreal_smul_measure_eq (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)] at hf₀
  rw [lintegral_uniformMeasure,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_uniformMeasure_iff.mp hf) hf₀,
    ← intervalIntegral.integral_of_le hab.le, ENNReal.ofReal_div_of_pos (sub_pos.mpr hab),
    ENNReal.div_eq_inv_mul]

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
