/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Measures with a density

A density `g` against `μ` defines a probability measure `μ.withDensity g` exactly when its lower
integral is `1` (`isProbabilityMeasure_withDensity_iff`). Mathlib has the finite-measure version
(`MeasureTheory.isFiniteMeasure_withDensity`) but not the normalised one.

The signed measure `μ.withDensityᵥ f` of a non-integrable `f` is `0`
(`withDensityᵥ_eq_zero_of_not_integrable`); Mathlib states this only through the definition.
-/

public section

namespace EpsilonEridani

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A density defines a probability measure exactly when its lower integral is `1`. -/
theorem isProbabilityMeasure_withDensity_iff {g : α → ℝ≥0∞} :
    IsProbabilityMeasure (μ.withDensity g) ↔ ∫⁻ x, g x ∂μ = 1 := by
  rw [isProbabilityMeasure_iff, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-- The signed measure with a non-integrable density is `0`. -/
theorem withDensityᵥ_eq_zero_of_not_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → E} (hf : ¬Integrable f μ) : μ.withDensityᵥ f = 0 := by
  -- `Measure.withDensityᵥ` is a `dite` on integrability whose `else` branch is `0`.
  rw [Measure.withDensityᵥ]
  exact dite_eq_right hf

end EpsilonEridani
