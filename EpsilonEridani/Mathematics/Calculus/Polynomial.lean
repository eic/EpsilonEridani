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

The weighted derivative operator `p ↦ derivative ((1 - X ^ 2) * derivative p)` on `ℝ[X]` is
symmetric under the interval integral on `[-1, 1]`: integrating it applied to `p` against `q`
gives the same value as integrating `p` against it applied to `q`. This is the Sturm–Liouville
symmetry for the weight `1 - x ^ 2` on `[-1, 1]`; the Legendre polynomials of
`Mathematics/SpecialFunctions/Legendre/Basic.lean` are the eigenfunctions of this operator, and
their orthogonality is one application of the symmetry proved here.

## Main statements

* `Polynomial.integral_derivative_one_sub_X_sq_mul_derivative_mul`: the symmetry of
  `p ↦ derivative ((1 - X ^ 2) * derivative p)` under the interval integral on `[-1, 1]`.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace Polynomial

/-- The weighted derivative operator `p ↦ derivative ((1 - X ^ 2) * derivative p)` is
**symmetric** under the interval integral on `[-1, 1]`: pairing it applied to `p` with `q`
gives the same integral as pairing `p` with it applied to `q`. This is the Sturm–Liouville
symmetry for the weight `1 - x ^ 2` on `[-1, 1]`; combined with the eigenfunction equation it
makes the eigenfunctions for distinct eigenvalues orthogonal. -/
theorem integral_derivative_one_sub_X_sq_mul_derivative_mul (p q : ℝ[X]) :
    ∫ x in (-1 : ℝ)..1, (derivative ((1 - X ^ 2) * derivative p) * q).eval x =
      ∫ x in (-1 : ℝ)..1, (p * derivative ((1 - X ^ 2) * derivative q)).eval x := by
  have key : derivative ((1 - X ^ 2) * derivative p) * q -
      p * derivative ((1 - X ^ 2) * derivative q) =
        derivative ((1 - X ^ 2) * (derivative p * q - p * derivative q)) := by
    simp only [derivative_mul, derivative_sub]
    ring
  rw [← sub_eq_zero, ← integral_sub ((Polynomial.continuous _).intervalIntegrable _ _)
    ((Polynomial.continuous _).intervalIntegrable _ _)]
  simp_rw [← eval_sub, key]
  rw [integral_deriv_eq_sub' _ (_root_.funext fun x => Polynomial.deriv _)
    (fun x _ => Polynomial.differentiableAt _) (Polynomial.continuous _).continuousOn]
  simp

end Polynomial
