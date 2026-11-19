/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.VectorMeasure.WithDensity

/-!
# Measures with a density

A density `g` against `μ` whose lower integral is `1` defines a probability measure
`μ.withDensity g` (`isProbabilityMeasure_withDensity`). Mathlib has the finite-measure version
(`MeasureTheory.isFiniteMeasure_withDensity`) but not the normalised one.

The signed measure `μ.withDensityᵥ f` of a non-integrable `f` is `0`
(`withDensityᵥ_eq_zero_of_not_integrable`); Mathlib states this only through the definition.
-/

public section

namespace EpsilonEridani

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A density with lower integral `1` defines a probability measure. -/
theorem isProbabilityMeasure_withDensity {g : α → ℝ≥0∞} (hg1 : ∫⁻ x, g x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity g) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1]⟩

/-- The signed measure with a non-integrable density is `0`. -/
theorem withDensityᵥ_eq_zero_of_not_integrable {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : α → E} (hf : ¬Integrable f μ) : μ.withDensityᵥ f = 0 :=
  dite_eq_right hf

end EpsilonEridani
