/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Probability measures with a density

A density `g` against `μ` whose lower integral is `1` defines a probability measure
`μ.withDensity g` (`isProbabilityMeasure_withDensity`), and such a density is almost everywhere
finite (`ae_lt_top_of_lintegral_eq_one`). Mathlib has the finite-measure version
(`MeasureTheory.isFiniteMeasure_withDensity`) but not the normalised one.
-/

public section

namespace EpsilonEridani

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ≥0∞}

/-- A density with lower integral `1` defines a probability measure. -/
theorem isProbabilityMeasure_withDensity (hg1 : ∫⁻ x, g x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity g) :=
  ⟨by rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hg1]⟩

/-- A density with lower integral `1` is almost everywhere finite. -/
theorem ae_lt_top_of_lintegral_eq_one (hg : AEMeasurable g μ) (hg1 : ∫⁻ x, g x ∂μ = 1) :
    ∀ᵐ x ∂μ, g x < ∞ :=
  ae_lt_top' hg (by simp [hg1])

end EpsilonEridani
