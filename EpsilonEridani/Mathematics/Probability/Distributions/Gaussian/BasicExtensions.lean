/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Basic

/-!
# Dilations of Gaussian measures

Mathlib shows that the image of a Gaussian measure under a continuous linear map is Gaussian
(`ProbabilityTheory.isGaussian_map`). This file registers the instance for the image under a
dilation `x ↦ c • x`, the form in which a Gaussian of width `c` is written as the image of a
standard one, so that it is found by instance search and the moment bounds of Gaussian measures,
such as `ProbabilityTheory.IsGaussian.integrable_norm_sq`, apply to the dilated measure.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsGaussian μ]

/-- The image of a Gaussian measure under the dilation `x ↦ c • x` is Gaussian. -/
instance isGaussian_map_smul (c : ℝ) : IsGaussian (μ.map (c • ·)) := by
  -- the dilation is the continuous linear map `c • id`
  convert isGaussian_map (μ := μ) (c • ContinuousLinearMap.id ℝ E)
  simp

end ProbabilityTheory
