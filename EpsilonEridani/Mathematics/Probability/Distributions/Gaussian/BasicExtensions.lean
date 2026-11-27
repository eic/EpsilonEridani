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
which a second moment of a coordinate is integrated. On a real inner product space the coordinate
`⟪x, v⟫` along a vector `v` is such a functional, so its square is integrable too
(`ProbabilityTheory.IsGaussian.integrable_inner_sq`).
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The square of a continuous linear functional is integrable against a Gaussian measure. -/
theorem IsGaussian.integrable_dual_sq (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E) :
    Integrable (fun x ↦ L x ^ 2) μ :=
  (IsGaussian.memLp_dual μ L 2 (by simp)).integrable_sq

/-- The square of a coordinate `⟪x, v⟫` of a real inner product space is integrable against a
Gaussian measure. -/
theorem IsGaussian.integrable_inner_sq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure F) [IsGaussian μ] (v : F) :
    Integrable (fun x ↦ ⟪x, v⟫ ^ 2) μ :=
  -- the coordinate is the continuous linear functional `innerSL ℝ v`, up to symmetry
  (IsGaussian.integrable_dual_sq μ (innerSL ℝ v)).congr
    (.of_forall fun x ↦ by simp [real_inner_comm])

end ProbabilityTheory
