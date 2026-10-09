/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Interval integrals of polynomial derivatives

For a polynomial `w : ℝ[X]`, the second-order operator `p ↦ derivative (w * derivative p)` on
`ℝ[X]` is symmetric under the interval integral on `[a, b]` whenever its leading coefficient `w`
vanishes at both endpoints: integrating it applied to `p` against `q` gives the same value as
integrating `p` against it applied to `q`. This is the Sturm–Liouville symmetry, with weight `1`,
for an operator whose leading coefficient vanishes at the endpoints, so that the boundary term
of the integration by parts drops. The Legendre polynomials of
`Mathematics/SpecialFunctions/Legendre/Basic.lean` are the eigenfunctions of the case
`w = 1 - X ^ 2` on `[-1, 1]`, and their orthogonality is one application of the symmetry.

## Main statements

* `Polynomial.integral_derivative_mul_derivative_mul`: the symmetry of
  `p ↦ derivative (w * derivative p)` under the interval integral on `[a, b]` when `w` vanishes
  at `a` and `b`.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace Polynomial

/-- The operator `p ↦ derivative (w * derivative p)` is **symmetric** under the interval integral
on `[a, b]` when its leading coefficient `w` vanishes at both endpoints: pairing it applied to `p`
with `q` gives the same integral as pairing `p` with it applied to `q`. This is the
Sturm–Liouville symmetry (with weight `1`); combined with the eigenfunction equation it makes the
eigenfunctions for distinct eigenvalues orthogonal. -/
theorem integral_derivative_mul_derivative_mul (w p q : ℝ[X]) {a b : ℝ} (ha : w.eval a = 0)
    (hb : w.eval b = 0) :
    ∫ x in a..b, (derivative (w * derivative p) * q).eval x =
      ∫ x in a..b, (p * derivative (w * derivative q)).eval x := by
  have key : derivative (w * derivative p) * q - p * derivative (w * derivative q) =
      derivative (w * (derivative p * q - p * derivative q)) := by
    simp only [derivative_mul, derivative_sub]
    ring
  rw [← sub_eq_zero, ← integral_sub ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)]
  simp_rw [← eval_sub, key]
  rw [integral_deriv_eq_sub' _ (_root_.funext fun x => Polynomial.deriv _)
    (fun x _ => Polynomial.differentiableAt _) (Polynomial.continuous _).continuousOn]
  -- the leading coefficient `w` vanishes at both endpoints, so the boundary term drops
  simp only [eval_mul, ha, hb, zero_mul, sub_self]

end Polynomial
