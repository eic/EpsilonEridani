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

- `aestronglyMeasurable_of_integrableOn_cpow_smul`,
  `aestronglyMeasurable_of_integrableOn_rpow_smul`: if `x ^ c • g x` is integrable on a
  measurable `s ⊆ (0, ∞)`, then `g` is a.e.-strongly-measurable on `s`.
- `indicator_Ioc_eventuallyEq_zero_atTop`, `indicator_Ioc_eventuallyEq_nhdsGT`: the extension by
  zero from `(a, b]` vanishes near `+∞` and agrees with the function to the right of `a`.
- `MeasureTheory.LocallyIntegrableOn.indicator_Ioc_Ioi`: the extension by zero of a function
  locally integrable on `(a, b]` is locally integrable on `(a, ∞)`.
- `MeasureTheory.IntegrableOn.rpow_smul_Ioc_of_le`: on `(0, 1]` the power weight `x ^ σ` decreases
  as `σ` grows, so integrability of `x ^ σ₀ • g x` there gives that of `x ^ σ • g x` for
  `σ₀ ≤ σ`.

Nothing in this file is physics-specific.
-/

public section

open MeasureTheory Set Filter Topology

namespace EpsilonEridani

variable {E : Type*} [NormedAddCommGroup E] {g : ℝ → E} {s : Set ℝ}

/-- Dividing out a power weight: if `x ^ c • g x` is integrable on a measurable `s ⊆ (0, ∞)`, then
`g` is a.e.-strongly-measurable on `s`. -/
theorem aestronglyMeasurable_of_integrableOn_cpow_smul [NormedSpace ℂ E] (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) {c : ℂ} (h : IntegrableOn (fun x : ℝ => (x : ℂ) ^ c • g x) s) :
    AEStronglyMeasurable g (volume.restrict s) :=
  (aestronglyMeasurable_smul_iff₀ (Complex.measurable_ofReal.pow_const c).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem hs] with x hx h0 using
      (hs0 hx).ne' (Complex.ofReal_eq_zero.mp ((Complex.cpow_eq_zero_iff _ _).mp h0).1))).mp
    h.aestronglyMeasurable

/-- Dividing out a real power weight: if `x ^ σ • g x` is integrable on a measurable
`s ⊆ (0, ∞)`, then `g` is a.e.-strongly-measurable on `s`. -/
theorem aestronglyMeasurable_of_integrableOn_rpow_smul [NormedSpace ℝ E] (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) {σ : ℝ} (h : IntegrableOn (fun x => x ^ σ • g x) s) :
    AEStronglyMeasurable g (volume.restrict s) :=
  (aestronglyMeasurable_smul_iff₀ (measurable_id.pow_const σ).aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem hs] with x hx using
      (Real.rpow_pos_of_pos (hs0 hx) σ).ne')).mp h.aestronglyMeasurable

/-- The extension by zero of a function from `(a, b]` vanishes near `+∞`. -/
theorem indicator_Ioc_eventuallyEq_zero_atTop {E : Type*} [Zero E] (a b : ℝ) (g : ℝ → E) :
    (Ioc a b).indicator g =ᶠ[atTop] 0 :=
  eqOn_indicator'.eventuallyEq_of_mem
    (mem_of_superset (Ioi_mem_atTop b) fun _ hx hmem => hx.not_ge hmem.2)

/-- The extension by zero of a function from `(a, b]` agrees with it to the right of `a`. -/
theorem indicator_Ioc_eventuallyEq_nhdsGT {E : Type*} [Zero E] {a b : ℝ} (hab : a < b)
    (g : ℝ → E) : (Ioc a b).indicator g =ᶠ[𝓝[>] a] g :=
  eqOn_indicator.eventuallyEq_of_mem (Ioc_mem_nhdsGT hab)

end EpsilonEridani

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}

/-- The extension by zero of a function locally integrable on `(a, b]` is locally integrable on
`(a, ∞)`. -/
theorem LocallyIntegrableOn.indicator_Ioc_Ioi {a b : ℝ} (hg : LocallyIntegrableOn g (Ioc a b)) :
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

/-- On `(0, 1]` the power weight `x ^ σ` decreases as `σ` grows: integrability of `x ^ σ₀ • g x`
on `(0, 1]` gives that of `x ^ σ • g x` for every `σ ≥ σ₀`. -/
theorem IntegrableOn.rpow_smul_Ioc_of_le [NormedSpace ℝ E] {σ₀ σ : ℝ}
    (h : IntegrableOn (fun x => x ^ σ₀ • g x) (Ioc 0 1)) (hσ : σ₀ ≤ σ) :
    IntegrableOn (fun x => x ^ σ • g x) (Ioc 0 1) := by
  have hg := EpsilonEridani.aestronglyMeasurable_of_integrableOn_rpow_smul measurableSet_Ioc
    Ioc_subset_Ioi_self h
  refine Integrable.mono' h.norm ((measurable_id.pow_const σ).aestronglyMeasurable.smul hg) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 hσ) (norm_nonneg _)

end MeasureTheory
