/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of polynomials against real powers on the unit interval

The integral over `[0, 1]` of a cubic polynomial times `z ^ s`, for a real exponent `s > -1`,
computed monomial by monomial from Mathlib's `integral_rpow`:

  `∫₀¹ (a₀ + a₁ z + a₂ z² + a₃ z³) z ^ s dz =
    a₀ / (s + 1) + a₁ / (s + 2) + a₂ / (s + 3) + a₃ / (s + 4)`.

This is the Mellin moment of a cubic polynomial at index `N = s + 1`. The regular parts of the
splitting kernels of collinear evolution are cubic polynomials, possibly divided by `z`, so their
moments in closed form all reduce to it (`EpsilonEridani.QFT.Factorization.Evolution.moment_pgq`
and its siblings in `Evolution/Kernel/LeadingOrder.lean`).

## Main statements

* `EpsilonEridani.integral_cubic_mul_rpow`: the integral of a cubic polynomial times `z ^ s` over
  `[0, 1]`, for `s > -1`.
-/

public section

namespace EpsilonEridani

open MeasureTheory

/-- The integral over `[0, 1]` of a cubic polynomial times `z ^ s`, monomial by monomial, for a
real exponent `s > -1`: `∫₀¹ (a₀ + a₁ z + a₂ z² + a₃ z³) z ^ s dz = ∑ₖ aₖ / (s + k + 1)`. -/
theorem integral_cubic_mul_rpow (a₀ a₁ a₂ a₃ : ℝ) {s : ℝ} (hs : -1 < s) :
    ∫ z in (0 : ℝ)..1, (a₀ + a₁ * z + a₂ * z ^ 2 + a₃ * z ^ 3) * z ^ s =
      a₀ / (s + 1) + a₁ / (s + 2) + a₂ / (s + 3) + a₃ / (s + 4) := by
  have hi (a : ℝ) {r : ℝ} (hr : -1 < r) :
      IntervalIntegrable (fun z : ℝ => a * z ^ r) volume 0 1 :=
    (intervalIntegral.intervalIntegrable_rpow' hr).const_mul a
  have hint {r : ℝ} (hr : -1 < r) : ∫ z in (0 : ℝ)..1, z ^ r = 1 / (r + 1) := by
    rw [integral_rpow (Or.inl hr), Real.one_rpow,
      Real.zero_rpow (by linarith : (0 : ℝ) < r + 1).ne', sub_zero]
  have h0 := hi a₀ hs
  have h1 := hi a₁ (by linarith : -1 < s + 1)
  have h2 := hi a₂ (by linarith : -1 < s + 2)
  have h3 := hi a₃ (by linarith : -1 < s + 3)
  have hsplit : ∫ z in (0 : ℝ)..1, (a₀ + a₁ * z + a₂ * z ^ 2 + a₃ * z ^ 3) * z ^ s =
      ∫ z in (0 : ℝ)..1,
        (a₀ * z ^ s + a₁ * z ^ (s + 1) + a₂ * z ^ (s + 2) + a₃ * z ^ (s + 3)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz _
    rw [show s + 2 = s + 1 + 1 by ring, show s + 3 = s + 1 + 1 + 1 by ring]
    simp only [Real.rpow_add_one hz]
    ring
  rw [hsplit, intervalIntegral.integral_add ((h0.add h1).add h2) h3,
    intervalIntegral.integral_add (h0.add h1) h2, intervalIntegral.integral_add h0 h1]
  simp only [intervalIntegral.integral_const_mul, hint hs, hint (by linarith : -1 < s + 1),
    hint (by linarith : -1 < s + 2), hint (by linarith : -1 < s + 3)]
  ring

end EpsilonEridani
