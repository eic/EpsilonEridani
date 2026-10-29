/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Power weights and extensions by zero on the half-line

This module collects measurability and integrability facts for functions on the half-line
`(0, ∞)` and on intervals `(a, b]`. They supply the hypotheses that Mathlib's theorems on
`mellin` ask of a function on `(0, ∞)`.

## Main results

- `aestronglyMeasurable_of_integrableOn_cpow_mul`, `aestronglyMeasurable_of_integrableOn_rpow_mul`:
  if `x ^ c * f x` is integrable on a measurable `s ⊆ (0, ∞)`, then `f` is
  a.e.-strongly-measurable on `s`.
- `locallyIntegrableOn_Ioi_indicator_Ioc`: the extension by zero of a function locally integrable
  on `(a, b]` is locally integrable on `(a, ∞)`.
- `indicator_Ioc_eventuallyEq_zero_atTop`, `indicator_Ioc_eventuallyEq_nhdsGT`: the extension by
  zero from `(a, b]` vanishes near `+∞` and agrees with the function to the right of `a`.

Nothing in this file is physics-specific.
-/

public section

open MeasureTheory Set Filter Topology

namespace EpsilonEridani

variable {f : ℝ → ℝ}

/-- Dividing out a power weight: if `x ^ c * f x` is integrable on a measurable `s ⊆ (0, ∞)`, then
`f` is a.e.-strongly-measurable on `s`. -/
theorem aestronglyMeasurable_of_integrableOn_cpow_mul {s : Set ℝ} (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) {c : ℂ} (h : IntegrableOn (fun x : ℝ => (x : ℂ) ^ c * (f x : ℂ)) s) :
    AEStronglyMeasurable f (volume.restrict s) := by
  have hw : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-c)) s :=
    Complex.continuous_ofReal.continuousOn.cpow_const fun x hx =>
      Complex.ofReal_mem_slitPlane.mpr (hs0 hx)
  refine (Complex.continuous_re.comp_aestronglyMeasurable
    ((hw.aestronglyMeasurable hs).mul h.aestronglyMeasurable)).congr ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs0 hx).ne'
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← Complex.cpow_add _ _ hx0, neg_add_cancel, Complex.cpow_zero, one_mul,
    Complex.ofReal_re]

/-- Dividing out a real power weight: if `x ^ σ * f x` is integrable on a measurable
`s ⊆ (0, ∞)`, then `f` is a.e.-strongly-measurable on `s`. -/
theorem aestronglyMeasurable_of_integrableOn_rpow_mul {s : Set ℝ} (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) {σ : ℝ} (h : IntegrableOn (fun x => x ^ σ * f x) s) :
    AEStronglyMeasurable f (volume.restrict s) := by
  refine aestronglyMeasurable_of_integrableOn_cpow_mul hs hs0 (c := σ)
    (h.ofReal.congr_fun (fun x hx => ?_) hs)
  rw [← Complex.ofReal_cpow (hs0 hx).le]
  exact Complex.ofReal_mul _ _

/-- The extension by zero of a function locally integrable on `(a, b]` is locally integrable on
`(a, ∞)`. -/
theorem locallyIntegrableOn_Ioi_indicator_Ioc {E : Type*} [NormedAddCommGroup E] {a b : ℝ}
    {g : ℝ → E} (hg : LocallyIntegrableOn g (Ioc a b)) :
    LocallyIntegrableOn ((Ioc a b).indicator g) (Ioi a) := by
  -- A compact `k ⊆ (a, ∞)` meets `(a, b]` inside the compact interval `[inf k, b] ⊆ (a, b]`, on
  -- which `g` is integrable.
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk hkc
  rcases k.eq_empty_or_nonempty with rfl | hne
  · exact integrableOn_empty
  have hpos : a < sInf k := hk (hkc.sInf_mem hne)
  have hIcc : IntegrableOn g (Icc (sInf k) b) :=
    hg.integrableOn_compact_subset (fun x hx => ⟨hpos.trans_le hx.1, hx.2⟩) isCompact_Icc
  rw [integrableOn_indicator_iff measurableSet_Ioc]
  exact hIcc.mono_set fun x hx => ⟨csInf_le hkc.bddBelow hx.2, hx.1.2⟩

/-- The extension by zero of a function from `(a, b]` vanishes near `+∞`. -/
theorem indicator_Ioc_eventuallyEq_zero_atTop {E : Type*} [Zero E] (a b : ℝ) (g : ℝ → E) :
    (Ioc a b).indicator g =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop b] with x hx
  exact indicator_of_notMem (fun h => hx.not_ge h.2) g

/-- The extension by zero of a function from `(a, b]` agrees with it to the right of `a`. -/
theorem indicator_Ioc_eventuallyEq_nhdsGT {E : Type*} [Zero E] {a b : ℝ} (hab : a < b)
    (g : ℝ → E) : (Ioc a b).indicator g =ᶠ[𝓝[>] a] g := by
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  exact indicator_of_mem (Ioo_subset_Ioc_self hx) g

end EpsilonEridani
