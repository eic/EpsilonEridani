/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The squared coordinates of a Gaussian measure are integrable

Fernique's theorem gives a Gaussian measure moments of all orders
(`ProbabilityTheory.IsGaussian.memLp_id`). This file records the second-moment case for a
coordinate of a Gaussian measure on a real inner product space: the squared coordinate
`x ↦ ⟪x, v⟫ ^ 2` is integrable (`ProbabilityTheory.IsGaussian.integrable_inner_sq`).
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E]

/-- The square of a coordinate `⟪x, v⟫` is integrable against a Gaussian measure: a Gaussian has
finite second moments. -/
theorem integrable_inner_sq (μ : Measure E) [IsGaussian μ] (v : E) :
    Integrable (fun x : E ↦ ⟪x, v⟫ ^ 2) μ := by
  have h := (innerSL ℝ v).comp_memLp' (memLp_two_id (μ := μ))
  refine h.integrable_sq.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  dsimp only
  rw [Function.comp_apply, id_eq, innerSL_apply_apply, real_inner_comm v x]

end ProbabilityTheory.IsGaussian
