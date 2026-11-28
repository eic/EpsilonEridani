/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Restricted product measures projected to a factor

This file extends `Mathlib.MeasureTheory.Measure.Prod`. The part of a product measure `ν.prod ρ`
carried by a measurable set `s`, pushed forward to the first factor (its first marginal
`Measure.fst`), is `ν` with density the `ρ`-measure of the slices of `s`.

## Main results

* `MeasureTheory.Measure.fst_restrict_prod`: the first marginal `((ν.prod ρ).restrict s).fst` is
  `ν.withDensity fun x => ρ (Prod.mk x ⁻¹' s)`.
-/

public section

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The part of a product measure carried by a measurable set `s`, pushed forward to the first
factor, is the first factor with density `x ↦ ρ (Prod.mk x ⁻¹' s)`, the measure of the slice of
`s` above `x`. -/
theorem fst_restrict_prod (ν : Measure α) (ρ : Measure β) [SFinite ρ] {s : Set (α × β)}
    (hs : MeasurableSet s) :
    ((ν.prod ρ).restrict s).fst = ν.withDensity fun x => ρ (Prod.mk x ⁻¹' s) := by
  ext t ht
  rw [fst_apply ht, restrict_apply (measurable_fst ht),
    prod_apply ((measurable_fst ht).inter hs), withDensity_apply _ ht,
    ← lintegral_indicator ht]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ t <;> simp [hx, Set.preimage_inter, Set.preimage_preimage]

end MeasureTheory.Measure
