/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.HasLaw

/-!
# The inverse-transform method

A *quantile function* of a distribution function `F : ℝ → ℝ` is a function `q : ℝ → ℝ` satisfying
the characterisation

`q u ≤ x ↔ u ≤ F x` for every variate `u` strictly between `0` and `1` and every `x`,

which says that `q u` is the least `x` with `u ≤ F x`. This is `IsQuantileFunction F q`, and the
inverse-transform method is the theorem that such a `q`, read as a random variable on `[0, 1]`
carrying Lebesgue measure, has law the measure whose distribution function is `F`
(`IsQuantileFunction.hasLaw`): one uniform variate becomes a draw from a prescribed law.

Taking the characterisation as the hypothesis, rather than a formula for `q`, is what makes the
theorem usable by a sampler, which inverts its distribution function in closed form and never
forms an infimum: the hypothesis to check is then a pair of inequalities. The exponential sampler
at the end of this file is the elementary instance.

Two facts make the characterisation suffice on its own. It forces `q` to be monotone on the open
unit interval (`IsQuantileFunction.monotoneOn`), hence almost everywhere measurable there, so no
measurability has to be assumed; and it determines `q` there outright (`IsQuantileFunction.eqOn`),
so a distribution function has essentially one quantile function.

The endpoint variates `0` and `1` are excluded throughout because a distribution function need
not attain either value, so the least `x` can fail to exist there; the endpoints form a null set
and the law is unaffected.

## Main definitions

* `EpsilonEridani.IsQuantileFunction`: the characterisation above.

## Main results

* `EpsilonEridani.IsQuantileFunction.map_apply_Iic`: the law of a quantile function gives `F x` to
  the interval `Iic x`.
* `EpsilonEridani.IsQuantileFunction.hasLaw`: **the inverse-transform method**, for a law
  presented through its values on left-infinite intervals, which is how a law built from a
  density arrives, and `EpsilonEridani.IsQuantileFunction.hasLaw_cdf` for one presented through
  its cumulative distribution function.
* `EpsilonEridani.hasLaw_neg_log_one_sub_div` and `EpsilonEridani.hasLaw_neg_log_div`: the
  exponential law of rate `r` is the law of `u ↦ -log (1 - u) / r`, and equally of
  `u ↦ -log u / r`.

## References

* L. Devroye, *Non-Uniform Random Variate Generation*, Springer 1986, Chapter II.
* P. Embrechts and M. Hofert, *A note on generalized inverses*, Mathematical Methods of
  Operations Research 77 (2013), 423--432, for the characterisation and its consequences.
-/

@[expose] public section

open MeasureTheory Measure Set Filter Topology ProbabilityTheory

open scoped ENNReal

namespace EpsilonEridani

variable {F q : ℝ → ℝ}

/-- `q` is a *quantile function* of the distribution function `F`: for every variate `u` strictly
between `0` and `1`, the value `q u` is the least `x` with `u ≤ F x`, stated as the
characterisation `q u ≤ x ↔ u ≤ F x`.

The variate is restricted to the open unit interval because `F` need not attain `0` or `1`, in
which case no least such `x` exists at the endpoints. -/
def IsQuantileFunction (F q : ℝ → ℝ) : Prop :=
  ∀ u ∈ Ioo (0 : ℝ) 1, ∀ x, q u ≤ x ↔ u ≤ F x

/-- A variate never exceeds the distribution function at its own quantile. -/
theorem IsQuantileFunction.le_apply (h : IsQuantileFunction F q) {u : ℝ}
    (hu : u ∈ Ioo (0 : ℝ) 1) : u ≤ F (q u) :=
  (h u hu (q u)).1 le_rfl

/-- A quantile function is monotone on the open unit interval. Monotonicity is not an assumption:
it follows from the characterisation. -/
theorem IsQuantileFunction.monotoneOn (h : IsQuantileFunction F q) :
    MonotoneOn q (Ioo (0 : ℝ) 1) :=
  fun _ hu _ hv huv => (h _ hu _).2 (huv.trans (h.le_apply hv))

/-- Two quantile functions of the same distribution function agree on the open unit interval. -/
theorem IsQuantileFunction.eqOn (h : IsQuantileFunction F q) {q' : ℝ → ℝ}
    (h' : IsQuantileFunction F q') : EqOn q q' (Ioo (0 : ℝ) 1) :=
  fun u hu => le_antisymm ((h u hu _).2 (h'.le_apply hu)) ((h' u hu _).2 (h.le_apply hu))

/-- The variates in the open unit interval whose quantile is at most `x` are exactly those at
most `F x`. -/
theorem IsQuantileFunction.preimage_Iic_inter (h : IsQuantileFunction F q) (x : ℝ) :
    q ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Iic (F x) ∩ Ioo (0 : ℝ) 1 := by
  simp only [Set.ext_iff, mem_inter_iff, mem_preimage, mem_Iic]
  exact fun u => and_congr_left fun hu => h u hu x

/-- A quantile function is almost everywhere measurable for Lebesgue measure on `[0, 1]`, by its
monotonicity on the open unit interval. -/
theorem IsQuantileFunction.aemeasurable (h : IsQuantileFunction F q) :
    AEMeasurable q (volume.restrict (Icc (0 : ℝ) 1)) := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact aemeasurable_restrict_of_monotoneOn measurableSet_Ioo h.monotoneOn

/-- **The law of a quantile function has distribution function `F`.** Pushing Lebesgue measure on
`[0, 1]` forward along a quantile function of `F` gives `F x` as the measure of `Iic x`, provided
`F x ≤ 1`, which every distribution function satisfies.

The proof is the length of the interval of variates whose quantile is at most `x`, which the
characterisation identifies up to the two endpoints. -/
theorem IsQuantileFunction.map_apply_Iic (h : IsQuantileFunction F q) {x : ℝ} (hx : F x ≤ 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).map q) (Iic x) = ENNReal.ofReal (F x) := by
  rw [map_apply_of_aemeasurable h.aemeasurable measurableSet_Iic,
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc, Measure.restrict_apply' measurableSet_Ioo,
    h.preimage_Iic_inter]
  refine le_antisymm ?_ ?_
  · calc volume (Iic (F x) ∩ Ioo (0 : ℝ) 1)
        ≤ volume (Ioc (0 : ℝ) (F x)) := measure_mono fun u hu => ⟨hu.2.1, hu.1⟩
      _ = ENNReal.ofReal (F x) := by rw [Real.volume_Ioc, sub_zero]
  · calc ENNReal.ofReal (F x) = volume (Ioo (0 : ℝ) (F x)) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume (Iic (F x) ∩ Ioo (0 : ℝ) 1) :=
        measure_mono fun u hu => ⟨hu.2.le, hu.1, hu.2.trans_le hx⟩

/-- **The inverse-transform method.** A quantile function of `F`, read as a random variable on
`[0, 1]` carrying Lebesgue measure, has law any probability measure whose values on the
left-infinite intervals are those of `F`.

`F` is allowed to differ from the cumulative distribution function where the latter is `0`,
since `ENNReal.ofReal` is not injective there and no variate in the open unit interval can tell
the difference. -/
theorem IsQuantileFunction.hasLaw (h : IsQuantileFunction F q) {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hF : ∀ x, μ (Iic x) = ENNReal.ofReal (F x)) :
    HasLaw q μ (volume.restrict (Icc (0 : ℝ) 1)) where
  aemeasurable := h.aemeasurable
  map_eq := by
    have hle : ∀ x, F x ≤ 1 := fun x =>
      ENNReal.ofReal_le_one.1 (by rw [← hF x]; exact prob_le_one)
    have : IsProbabilityMeasure ((volume.restrict (Icc (0 : ℝ) 1)).map q) :=
      (Measure.isProbabilityMeasure_map_iff h.aemeasurable).2 ⟨by simp⟩
    exact Measure.ext_of_Iic _ _ fun x => by rw [h.map_apply_Iic (hle x), hF x]

/-- The inverse-transform method for a law presented through its cumulative distribution
function: a quantile function of `cdf μ` has law `μ`. -/
theorem IsQuantileFunction.hasLaw_cdf {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h : IsQuantileFunction (cdf μ) q) : HasLaw q μ (volume.restrict (Icc (0 : ℝ) 1)) :=
  h.hasLaw fun x => (ofReal_cdf μ x).symm

/-- `u ↦ -log (1 - u) / r` is a quantile function of the exponential law of rate `r`, in closed
form: the characterisation is checked from the exponential distribution function and no infimum
appears. -/
theorem isQuantileFunction_cdf_expMeasure {r : ℝ} (hr : 0 < r) :
    IsQuantileFunction (cdf (expMeasure r)) (fun u => -Real.log (1 - u) / r) := by
  intro u hu x
  have h1u : 0 < 1 - u := by linarith [hu.2]
  have hlog : Real.log (1 - u) < 0 := Real.log_neg h1u (by linarith [hu.1])
  simp only [cdf_expMeasure_eq hr]
  split_ifs with hx
  · constructor
    · intro h
      rw [div_le_iff₀ hr] at h
      have hle : -(r * x) ≤ Real.log (1 - u) := by linarith
      have := (Real.le_log_iff_exp_le h1u).1 hle
      linarith
    · intro h
      have hle : Real.exp (-(r * x)) ≤ 1 - u := by linarith
      have := (Real.le_log_iff_exp_le h1u).2 hle
      rw [div_le_iff₀ hr]
      linarith
  · rw [not_le] at hx
    have hpos : 0 < -Real.log (1 - u) / r := div_pos (by linarith) hr
    exact ⟨fun h => absurd (hpos.trans_le h) (by linarith),
      fun h => absurd (h.trans_lt hu.1) (lt_irrefl u)⟩

/-- **Inverse transform for the exponential law.** On `[0, 1]` with Lebesgue measure,
`u ↦ -log (1 - u) / r` has the exponential law of rate `r`. -/
theorem hasLaw_neg_log_one_sub_div {r : ℝ} (hr : 0 < r) :
    HasLaw (fun u => -Real.log (1 - u) / r) (expMeasure r) (volume.restrict (Icc (0 : ℝ) 1)) :=
  haveI := isProbabilityMeasure_expMeasure hr
  (isQuantileFunction_cdf_expMeasure hr).hasLaw_cdf

/-- Lebesgue measure on `[0, 1]` is invariant under the reflection `u ↦ 1 - u`. -/
theorem map_one_sub_restrict_Icc :
    (volume.restrict (Icc (0 : ℝ) 1)).map (fun u => 1 - u) = volume.restrict (Icc (0 : ℝ) 1) := by
  have hpre : (fun u : ℝ => 1 - u) ⁻¹' Icc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := by
    ext u
    simp only [mem_preimage, mem_Icc]
    constructor <;> exact fun h => ⟨by linarith [h.2], by linarith [h.1]⟩
  have h := Measure.restrict_map (μ := (volume : Measure ℝ)) (f := fun u : ℝ => 1 - u)
    (by fun_prop) (s := Icc (0 : ℝ) 1) measurableSet_Icc
  rw [hpre, (volume.measurePreserving_sub_left 1).map_eq] at h
  exact h.symm

/-- The usual form of the exponential sampler: on `[0, 1]` with Lebesgue measure,
`u ↦ -log u / r` also has the exponential law of rate `r`, because the reflection `u ↦ 1 - u`
preserves that measure. -/
theorem hasLaw_neg_log_div {r : ℝ} (hr : 0 < r) :
    HasLaw (fun u => -Real.log u / r) (expMeasure r) (volume.restrict (Icc (0 : ℝ) 1)) := by
  have h := hasLaw_neg_log_one_sub_div hr
  have hT : AEMeasurable (fun u : ℝ => 1 - u) (volume.restrict (Icc (0 : ℝ) 1)) := by fun_prop
  have hg : AEMeasurable (fun v : ℝ => -Real.log (1 - v) / r)
      ((volume.restrict (Icc (0 : ℝ) 1)).map (fun u : ℝ => 1 - u)) := by
    rw [map_one_sub_restrict_Icc]
    exact h.aemeasurable
  have hcomp : (fun u : ℝ => -Real.log u / r)
      = (fun v : ℝ => -Real.log (1 - v) / r) ∘ (fun u : ℝ => 1 - u) := by
    ext u
    simp
  refine ⟨?_, ?_⟩
  · rw [hcomp]
    exact hg.comp_aemeasurable hT
  · rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hg hT, map_one_sub_restrict_Icc, h.map_eq]

end EpsilonEridani
