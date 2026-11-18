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

This file extends `TauCeti.Probability.Distributions.Uniform.Basic`.

## Main results

* `EpsilonEridani.uniformMeasure_Iic`: the uniform measure of a closed lower tail, the companion
  of `TauCeti.Probability.uniformMeasure_Iio`.
* `MeasureTheory.Measure.map_fst_restrict_le_prod_uniformMeasure`: thinning by a uniform
  variate. Keeping a proposal `x` when an independent standard uniform variate lies below `a x`
  multiplies its law by the density `min (a x) 1`, clipped at `0`.
-/

public section

open MeasureTheory TauCeti.Probability

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

end EpsilonEridani

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- **Thinning by a uniform variate.** Draw `x` from `ν` and an independent standard uniform
variate `u`, and keep `x` when `u ≤ a x`. The kept part of the law of `x` is `ν` with density
`min (a x) 1`, read as `0` where `a x` is negative. -/
theorem map_fst_restrict_le_prod_uniformMeasure (ν : Measure α) {a : α → ℝ}
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
