/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle averages of odd functions

Reversing the radius of a circle about the origin reverses every point of it, while Mathlib's
`Real.circleAverage_neg_radius` says that the circle average does not see the sign of the radius.
For a function that is odd on the circle the two facts together force the average to equal its
own negative, so it vanishes.

## Main results

* `Real.circleAverage_eq_zero_of_odd`: the circle average about the origin of a function that is
  odd on the circle vanishes.
-/

@[expose] public section

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The circle average about the origin of a function that is odd on the circle of radius `|R|`
    vanishes. -/
theorem circleAverage_eq_zero_of_odd {f : ℂ → E} {R : ℝ}
    (hf : ∀ z ∈ Metric.sphere (0 : ℂ) |R|, f (-z) = -f z) :
    circleAverage f 0 R = 0 := by
  -- The radius `-R` traces the reversed circle, so the average equals its own negative.
  have h : circleAverage f 0 R = -circleAverage f 0 R := by
    conv_lhs => rw [← circleAverage_neg_radius]
    rw [circleAverage_def, circleAverage_def, ← smul_neg, ← intervalIntegral.integral_neg]
    congr 1
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hc : circleMap 0 (-R) θ = -circleMap 0 R θ := by simp [circleMap_zero]
    rw [hc, hf _ (circleMap_mem_sphere' 0 R θ)]
  -- Adding the two sides gives `2 • circleAverage f 0 R = 0`; halving recovers the claim.
  have h2 : (2 : ℝ) • circleAverage f 0 R = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  simpa using h2

end Real
