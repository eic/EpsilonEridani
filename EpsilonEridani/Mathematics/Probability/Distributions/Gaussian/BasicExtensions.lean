/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# The squared continuous linear functionals of a Gaussian measure are integrable

Every continuous linear functional `L` of a Gaussian measure has moments of all finite orders
(`ProbabilityTheory.IsGaussian.memLp_dual`), and Mathlib records the first-moment case as
`ProbabilityTheory.IsGaussian.integrable_dual`. This file records the second-moment case, the
integrability of `x ↦ L x ^ 2` (`ProbabilityTheory.IsGaussian.integrable_dual_sq`), the form in
which a second moment of a coordinate is integrated.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The square of a continuous linear functional is integrable against a Gaussian measure. -/
theorem IsGaussian.integrable_dual_sq (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E) :
    Integrable (fun x ↦ L x ^ 2) μ :=
  (IsGaussian.memLp_dual μ L 2 (by simp)).integrable_sq

end ProbabilityTheory
