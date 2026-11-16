/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of polynomials against real powers on the unit interval

The integral over `[0, 1]` of a polynomial times `z ^ s`, for a real exponent `s > -1`,
computed monomial by monomial from Mathlib's `integral_rpow`:

  `∫₀¹ (∑ₖ aₖ z ^ k) z ^ s dz = ∑ₖ aₖ / (s + k + 1)`.

This is the Mellin moment of a polynomial at index `N = s + 1`. The regular parts of the
leading-order splitting kernels of collinear evolution are cubic polynomials, possibly divided by
`z`, so their moments in closed form reduce to the cubic case
(`EpsilonEridani.QFT.Factorization.Evolution.moment_pgq` and its siblings in
`Evolution/Kernel/LeadingOrder.lean`).

## Main statements

* `EpsilonEridani.integral_poly_mul_rpow`: the integral of a polynomial, given by its
  coefficients `a 0, …, a (n - 1)`, times `z ^ s` over `[0, 1]`, for `s > -1`.
* `EpsilonEridani.integral_cubic_mul_rpow`: its cubic case.
-/

public section

namespace EpsilonEridani

open MeasureTheory

/-- The integral over `[0, 1]` of a polynomial with coefficients `a 0, …, a (n - 1)` times
`z ^ s`, monomial by monomial, for a real exponent `s > -1`:
`∫₀¹ (∑ₖ aₖ z ^ k) z ^ s dz = ∑ₖ aₖ / (s + k + 1)`. -/
theorem integral_poly_mul_rpow (a : ℕ → ℝ) (n : ℕ) {s : ℝ} (hs : -1 < s) :
    ∫ z in (0 : ℝ)..1, (∑ k ∈ Finset.range n, a k * z ^ k) * z ^ s =
      ∑ k ∈ Finset.range n, a k / (s + k + 1) := by
  have hk (k : ℕ) : -1 < s + k := by
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith
  have hsplit : ∫ z in (0 : ℝ)..1, (∑ k ∈ Finset.range n, a k * z ^ k) * z ^ s =
      ∫ z in (0 : ℝ)..1, ∑ k ∈ Finset.range n, a k * z ^ (s + k) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (0 : ℝ)] with z hz _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.rpow_add_natCast hz]
    ring
  rw [hsplit, intervalIntegral.integral_finsetSum fun k _ =>
    (intervalIntegral.intervalIntegrable_rpow' (hk k)).const_mul (a k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (hk k)), Real.one_rpow,
    Real.zero_rpow (by linarith [hk k] : (0 : ℝ) < s + k + 1).ne', sub_zero]
  ring

/-- The integral over `[0, 1]` of a cubic polynomial times `z ^ s`, for a real exponent
`s > -1`: `∫₀¹ (a₀ + a₁ z + a₂ z² + a₃ z³) z ^ s dz = ∑ₖ aₖ / (s + k + 1)`, the case `n = 4` of
`integral_poly_mul_rpow`. -/
theorem integral_cubic_mul_rpow (a₀ a₁ a₂ a₃ : ℝ) {s : ℝ} (hs : -1 < s) :
    ∫ z in (0 : ℝ)..1, (a₀ + a₁ * z + a₂ * z ^ 2 + a₃ * z ^ 3) * z ^ s =
      a₀ / (s + 1) + a₁ / (s + 2) + a₂ / (s + 3) + a₃ / (s + 4) := by
  have h := integral_poly_mul_rpow (fun k => [a₀, a₁, a₂, a₃].getD k 0) 4 hs
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, List.getD_cons_zero,
    List.getD_cons_succ, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, pow_zero, pow_one, mul_one,
    add_zero] at h
  rw [h]
  ring

end EpsilonEridani
