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

* `EpsilonEridani.uniformMeasure_zero_one`: the standard uniform law is Lebesgue measure
  restricted to `Set.Ioc 0 1`.
* `EpsilonEridani.uniformMeasure_Iic`: the uniform measure of a closed lower tail, the companion
  of `TauCeti.Probability.uniformMeasure_Iio`.
* `Continuous.integrable_uniformMeasure`: a continuous function is integrable against every
  uniform measure.
* `MeasureTheory.Measure.map_fst_restrict_setOf_le_prod_uniformMeasure`: thinning by a uniform
  variate. Keeping a proposal `x` when an independent standard uniform variate lies below `a x`
  multiplies its law by the density `min (a x) 1`, clipped at `0`.
-/

public section

open MeasureTheory TauCeti.Probability

namespace EpsilonEridani

/-- The standard uniform law is Lebesgue measure restricted to `Set.Ioc 0 1`. -/
theorem uniformMeasure_zero_one : uniformMeasure 0 1 = volume.restrict (Set.Ioc 0 1) := by
  simp [uniformMeasure_eq_smul]

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

end EpsilonEridani

/-- A continuous function is integrable against the uniform measure on any interval: on a
nondegenerate interval it is bounded there, and on a degenerate one the measure is zero. -/
theorem Continuous.integrable_uniformMeasure {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (hf : Continuous f) {a b : ℝ} : Integrable f (uniformMeasure a b) := by
  rcases le_or_gt b a with hba | hab
  · simp [uniformMeasure_eq_zero_of_le hba]
  rw [uniformMeasure_eq_smul]
  exact (hf.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).smul_measure (by simp [hab])

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- **Thinning by a uniform variate.** Draw `x` from `ν` and an independent standard uniform
variate `u`, and keep `x` when `u ≤ a x`. The kept part of the law of `x` is `ν` with density
`min (a x) 1`, read as `0` where `a x` is negative. -/
theorem map_fst_restrict_setOf_le_prod_uniformMeasure (ν : Measure α) {a : α → ℝ}
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
