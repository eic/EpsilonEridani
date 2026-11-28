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
* `MeasureTheory.Measure.fst_smul`: the first marginal commutes with scalar multiplication.
-/

public section

namespace MeasureTheory.Measure

open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The first marginal of a scalar multiple of a measure is the scalar multiple of its first
marginal. -/
theorem fst_smul {R : Type*} [SMul R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞] (c : R)
    (ρ : Measure (α × β)) : (c • ρ).fst = c • ρ.fst := by
  unfold fst
  exact Measure.map_smul c measurable_fst.aemeasurable

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
