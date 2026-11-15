/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Circle averages of odd and of measurable functions

This module supplies two facts about Mathlib's `Real.circleAverage` that Mathlib does not state:
the circle average of a function that is odd about the centre on the circle vanishes, and the
circle average of a strongly measurable function is strongly measurable in the radius. They are
consumed by the transverse circle average of `EpsilonEridani.Particles.Parton.GTMD.CircleAverage`,
which carries them to the azimuthal average of a vector-argument TMD: the first is why that
average annihilates azimuthally odd amplitudes, the second why it is measurable in the
transverse-momentum magnitude.

## Main results

* `Real.circleAverage_comp_reflection`: reflecting the function through the centre does not
  change its circle average.
* `Real.circleAverage_eq_zero_of_odd`: the circle average about `c` of a function that is odd
  about `c` on the circle vanishes.
* `MeasureTheory.StronglyMeasurable.circleAverage`: the circle average of a strongly measurable
  function is strongly measurable as a function of the radius.
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace Real

/-- Reflecting the function through the centre, `z ↦ 2 * c - z`, does not change its circle
    average about `c`. -/
theorem circleAverage_comp_reflection {f : ℂ → E} {c : ℂ} {R : ℝ} :
    circleAverage (fun z => f (2 * c - z)) c R = circleAverage f c R := by
  -- Pointwise, the reflected circle of radius `R` is the circle of radius `-R`.
  have h : ∀ θ, 2 * c - circleMap c R θ = circleMap c (-R) θ := fun θ => by
    simp only [circleMap]
    push_cast
    ring
  rw [← circleAverage_neg_radius (R := R) (f := f), circleAverage_def, circleAverage_def]
  simp only [h]

/-- The circle average about `c` of a function that is odd about `c` on the circle of radius `|R|`
    — `f (2 * c - z) = -f z` there — vanishes. -/
theorem circleAverage_eq_zero_of_odd {f : ℂ → E} {c : ℂ} {R : ℝ}
    (hf : ∀ z ∈ Metric.sphere c |R|, f (2 * c - z) = -f z) :
    circleAverage f c R = 0 := by
  -- Reflection through `c` fixes the average and negates the function, so the average equals
  -- its own negative.
  have h : circleAverage f c R = -circleAverage f c R := calc
    circleAverage f c R = circleAverage (fun z => f (2 * c - z)) c R :=
      circleAverage_comp_reflection.symm
    _ = circleAverage (fun z => -f z) c R := circleAverage_congr_sphere fun z hz => hf z hz
    _ = -circleAverage f c R := by
      simpa using circleAverage_fun_smul (a := (-1 : ℝ)) (f := f) (c := c) (R := R)
  -- Adding the two sides gives `2 • circleAverage f c R = 0`; halving recovers the claim.
  have h2 : (2 : ℝ) • circleAverage f c R = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  simpa using h2

end Real

/-- The circle average of a strongly measurable function is strongly measurable as a function of
    the radius. -/
theorem MeasureTheory.StronglyMeasurable.circleAverage {f : ℂ → E} (hf : StronglyMeasurable f)
    (c : ℂ) : StronglyMeasurable (Real.circleAverage f c) := by
  -- The average is `(2π)⁻¹` times the parametric integral over the angle of the jointly
  -- strongly measurable `(R, θ) ↦ f (circleMap c R θ)`.
  have heq : Real.circleAverage f c =
      fun R => (2 * Real.pi)⁻¹ • ∫ θ in Set.Ioc 0 (2 * Real.pi), f (circleMap c R θ) :=
    funext fun R => by
      rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rw [heq]
  exact ((hf.comp_measurable (Real.circleMap.continuous (c := c)).measurable).integral_prod_right'
    (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))).const_smul _
