/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Set integrals over a subset of a product, slice by slice

For a measurable set `S ⊆ α × β` and an integrand `g` integrable on `S`, Fubini's theorem
integrates `g` over `S` slice by slice: at each `x` the inner integral runs over the vertical slice
`Prod.mk x ⁻¹' S = {y | (x, y) ∈ S}`,

`∫_S g = ∫ dx ∫_{y : (x, y) ∈ S} dy g(x, y)`.

Mathlib states Fubini for the whole product (`MeasureTheory.integral_prod`) and for rectangles
(`MeasureTheory.setIntegral_prod`); this file gives the form for an arbitrary measurable set,
together with the integrability of the outer integrand. A concrete region then only has to compute
its slices. It also gives the invariance of set integrals and integrability over an arbitrary
subset under exchanging the two factors, which Mathlib states only for rectangles
(`MeasureTheory.setIntegral_prod_swap`).

## Main statements

* `EpsilonEridani.setIntegral_prod_eq_integral_setIntegral_mk_preimage`: Fubini over a measurable
  subset of a product, slice by slice.
* `EpsilonEridani.integrable_setIntegral_mk_preimage`: the outer integrand of that formula is
  integrable.
* `EpsilonEridani.setIntegral_preimage_swap`, `EpsilonEridani.integrableOn_preimage_swap_iff`:
  set integrals and integrability over a subset of a product are invariant under exchanging the
  factors.
-/

public section

noncomputable section

namespace EpsilonEridani

open MeasureTheory Set

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set (α × β)}
  {g : α × β → E}

/-- The integral of the extension by zero of `g` along the vertical line through `x` is the
integral of `g` over the slice of `S` at `x`. -/
theorem integral_indicator_comp_mk (hS : MeasurableSet S) (g : α × β → E) (x : α) :
    ∫ y, S.indicator g (x, y) ∂ν = ∫ y in Prod.mk x ⁻¹' S, g (x, y) ∂ν := by
  rw [← integral_indicator (measurable_prodMk_left hS)]
  simp_rw [← indicator_comp_right (Prod.mk x) (g := g), Function.comp_def]

/-- **Fubini over a measurable subset of a product**: the integral of `g` over `S` is the integral
over `x` of the integral of `g (x, ·)` over the slice `{y | (x, y) ∈ S}`. -/
theorem setIntegral_prod_eq_integral_setIntegral_mk_preimage [SFinite μ] [SFinite ν]
    (hS : MeasurableSet S) (hg : IntegrableOn g S (μ.prod ν)) :
    ∫ p in S, g p ∂μ.prod ν = ∫ x, ∫ y in Prod.mk x ⁻¹' S, g (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hS, integral_prod _ (hg.integrable_indicator hS)]
  simp only [integral_indicator_comp_mk hS]

/-- The outer integrand `x ↦ ∫_{y : (x, y) ∈ S} g(x, y)` of
`setIntegral_prod_eq_integral_setIntegral_mk_preimage` is integrable. -/
theorem integrable_setIntegral_mk_preimage [SFinite ν] (hS : MeasurableSet S)
    (hg : IntegrableOn g S (μ.prod ν)) :
    Integrable (fun x => ∫ y in Prod.mk x ⁻¹' S, g (x, y) ∂ν) μ :=
  (hg.integrable_indicator hS).integral_prod_left.congr
    (Filter.Eventually.of_forall fun x => integral_indicator_comp_mk hS g x)

/-- Set integrals over a subset of a product are invariant under exchanging the factors: the
integral of `g ∘ Prod.swap` over the preimage of `S` under `Prod.swap` is the integral of `g` over
`S`. This generalizes `MeasureTheory.setIntegral_prod_swap` from rectangles to arbitrary sets. -/
theorem setIntegral_preimage_swap [SFinite μ] [SFinite ν] (S : Set (β × α)) (g : β × α → E) :
    ∫ p in Prod.swap ⁻¹' S, g p.swap ∂μ.prod ν = ∫ p in S, g p ∂ν.prod μ :=
  Measure.measurePreserving_swap.setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding g S

omit [NormedSpace ℝ E] in
/-- Integrability over a subset of a product is invariant under exchanging the factors. -/
theorem integrableOn_preimage_swap_iff [SFinite μ] [SFinite ν] {S : Set (β × α)}
    {g : β × α → E} :
    IntegrableOn (fun p => g p.swap) (Prod.swap ⁻¹' S) (μ.prod ν) ↔ IntegrableOn g S (ν.prod μ) :=
  Measure.measurePreserving_swap.integrableOn_comp_preimage
    MeasurableEquiv.prodComm.measurableEmbedding

end EpsilonEridani
