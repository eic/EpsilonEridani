/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The squared norm is integrable against a Gaussian measure

Fernique's theorem gives a Gaussian measure moments of all orders
(`ProbabilityTheory.IsGaussian.memLp_id`). This file records the second-moment case in the form
in which it enters a second-moment bound: the squared norm `x ↦ ‖x‖ ^ 2` is integrable
(`ProbabilityTheory.IsGaussian.integrable_norm_sq`).
-/

public section

open MeasureTheory

namespace ProbabilityTheory.IsGaussian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [CompleteSpace E] [SecondCountableTopology E]

/-- The squared norm is integrable against a Gaussian measure: a Gaussian has a finite second
moment. -/
theorem integrable_norm_sq (μ : Measure E) [IsGaussian μ] :
    Integrable (fun x ↦ ‖x‖ ^ 2) μ :=
  (memLp_two_iff_integrable_sq_norm (by fun_prop)).1 memLp_two_id

end ProbabilityTheory.IsGaussian
