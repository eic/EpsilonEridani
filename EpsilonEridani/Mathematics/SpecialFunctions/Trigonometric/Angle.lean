/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

/-!
# Trigonometric modulations under reversal of an angle

A combination `A cos(-θ) + B sin(-θ)` of a cosine and a sine modulation of the reversed angle
`-θ` is the combination of modulations of `θ` with the same cosine amplitude `A` and the opposite
sine amplitude `-B`, since the cosine is even and the sine is odd
(`Real.Angle.cos_neg`, `Real.Angle.sin_neg`). This is how the amplitudes of a modulated quantity
transform when the orientation in which the angles are measured is reversed, which negates every
oriented angle.

## Main statements

* `Real.Angle.mul_cos_neg_add_mul_sin_neg`: `A cos(-θ) + B sin(-θ) = A cos θ + (-B) sin θ`.
* `Real.Angle.sum_mul_cos_neg_add_mul_sin_neg`: the same for a finite sum of modulations.
-/

public section

namespace Real.Angle

/-- Reversing an angle keeps the cosine amplitude of a modulation and flips its sine amplitude:
`A cos(-θ) + B sin(-θ) = A cos θ + (-B) sin θ`. -/
theorem mul_cos_neg_add_mul_sin_neg (A B : ℝ) (θ : Angle) :
    A * cos (-θ) + B * sin (-θ) = A * cos θ + -B * sin θ := by
  rw [cos_neg, sin_neg, mul_neg, neg_mul]

/-- Reversing the angles of a finite sum of modulations keeps the cosine amplitudes `A i` and
flips the sine amplitudes `B i`. -/
theorem sum_mul_cos_neg_add_mul_sin_neg {ι : Type*} (s : Finset ι) (A B : ι → ℝ)
    (θ : ι → Angle) :
    ∑ i ∈ s, (A i * cos (-θ i) + B i * sin (-θ i)) =
      ∑ i ∈ s, (A i * cos (θ i) + -B i * sin (θ i)) :=
  Finset.sum_congr rfl fun i _ => mul_cos_neg_add_mul_sin_neg (A i) (B i) (θ i)

end Real.Angle
