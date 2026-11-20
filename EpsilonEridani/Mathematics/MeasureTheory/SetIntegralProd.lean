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
its slices.

## Main statements

* `EpsilonEridani.setIntegral_prod_eq_integral_setIntegral_preimage_mk`: Fubini over a measurable
  subset of a product, slice by slice.
* `EpsilonEridani.integrable_setIntegral_preimage_mk`: the outer integrand of that formula is
  integrable.
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
theorem integral_indicator_mk (hS : MeasurableSet S) (g : α × β → E) (x : α) :
    ∫ y, S.indicator g (x, y) ∂ν = ∫ y in Prod.mk x ⁻¹' S, g (x, y) ∂ν := by
  rw [← integral_indicator (measurable_prodMk_left hS)]
  rfl

/-- **Fubini over a measurable subset of a product**: the integral of `g` over `S` is the integral
over `x` of the integral of `g (x, ·)` over the slice `{y | (x, y) ∈ S}`. -/
theorem setIntegral_prod_eq_integral_setIntegral_preimage_mk [SFinite μ] [SFinite ν]
    (hS : MeasurableSet S) (hg : IntegrableOn g S (μ.prod ν)) :
    ∫ p in S, g p ∂μ.prod ν = ∫ x, ∫ y in Prod.mk x ⁻¹' S, g (x, y) ∂ν ∂μ := by
  rw [← integral_indicator hS, integral_prod _ (hg.integrable_indicator hS)]
  simp only [integral_indicator_mk hS]

/-- The outer integrand `x ↦ ∫_{y : (x, y) ∈ S} g(x, y)` of
`setIntegral_prod_eq_integral_setIntegral_preimage_mk` is integrable. -/
theorem integrable_setIntegral_preimage_mk [SFinite μ] [SFinite ν] (hS : MeasurableSet S)
    (hg : IntegrableOn g S (μ.prod ν)) :
    Integrable (fun x => ∫ y in Prod.mk x ⁻¹' S, g (x, y) ∂ν) μ :=
  (hg.integrable_indicator hS).integral_prod_left.congr
    (Filter.Eventually.of_forall fun x => integral_indicator_mk hS g x)

end EpsilonEridani
