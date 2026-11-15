/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Real.Sqrt

/-!
# Extensions of the real square root

A nonnegative real `x` is recovered from the square root of a product `x y` with a positive `y`
and the ratio of square roots: `√(x y) (√x / √y) = x` (`Real.sqrt_mul_mul_sqrt_div_sqrt`). It is
the step that writes a light-cone component of a four-vector as its transverse mass times the
exponential of its rapidity.
-/

public section

namespace Real

/-- `√(x y) (√x / √y) = x` for `x ≥ 0` and `y > 0`. -/
theorem sqrt_mul_mul_sqrt_div_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    √(x * y) * (√x / √y) = x := by
  rw [Real.sqrt_mul hx, mul_div_left_comm, mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hy).ne',
    Real.mul_self_sqrt hx]

end Real
