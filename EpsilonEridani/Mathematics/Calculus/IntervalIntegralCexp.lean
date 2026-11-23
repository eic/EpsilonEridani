/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiating a finite Fourier integral in the frequency

For a continuous `f : ℝ → ℂ` and a bounded interval `[a, b]`, the finite Fourier integral
`y ↦ ∫ t in a..b, e^{i y t} f(t)` is differentiable, with derivative obtained by differentiating
under the integral sign: multiplication of the integrand by `i t`
(`hasDerivAt_integral_cexp_mul`). This turns multiplication by the integration variable into
differentiation in the frequency, which is how recurrences for a family of functions `f` (such as
Bonnet's recurrence for the Legendre polynomials) become differential relations for their
finite Fourier transforms (such as those between the spherical Bessel functions).
-/

@[expose] public section

open MeasureTheory intervalIntegral
open Complex (I)

namespace EpsilonEridani

/-- **Differentiation of a finite Fourier integral in the frequency**: for continuous `f`, the
derivative of `y ↦ ∫ t in a..b, e^{i y t} f(t)` is `∫ t in a..b, i t e^{i y t} f(t)`. -/
theorem hasDerivAt_integral_cexp_mul {f : ℝ → ℂ} (hf : Continuous f) (a b x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in a..b, Complex.exp (I * y * t) * f t)
      (∫ t in a..b, I * t * (Complex.exp (I * x * t) * f t)) x := by
  have hd : ∀ t y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (I * y * t) * f t)
      (I * t * (Complex.exp (I * y * t) * f t)) y := fun t y => by
    have h : HasDerivAt (fun y : ℝ => I * (y : ℂ) * t) (I * t) y := by
      simpa using (((hasDerivAt_id (y : ℂ)).const_mul I).mul_const (t : ℂ)).comp_ofReal
    convert h.cexp.mul_const (f t) using 1
    ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t => |t| * ‖f t‖)
    Filter.univ_mem (.of_forall fun y => (by fun_prop : Continuous _).aestronglyMeasurable)
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
    (by fun_prop : Continuous _).aestronglyMeasurable (.of_forall fun t _ y _ => ?_)
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
    (.of_forall fun t _ y _ => hd t y)).2
  simp [Complex.norm_exp]

end EpsilonEridani
