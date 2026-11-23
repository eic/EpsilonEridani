/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite Fourier integrals on an interval

For a function `f : ℝ → ℂ` integrable on a bounded interval `[a, b]`, the finite Fourier integral
`y ↦ ∫ t in a..b, e^{i y t} f(t)` is differentiable, with derivative obtained by differentiating
under the integral sign: multiplication of the integrand by `i t`
(`hasDerivAt_integral_cexp_mul`). This turns multiplication by the integration variable into
differentiation in the frequency, which is how recurrences for a family of functions `f` (such as
Bonnet's recurrence for the Legendre polynomials) become differential relations for their
finite Fourier transforms (such as those between the spherical Bessel functions).

The simplest such integral, of the constant `1` over `[-r, r]`, is
`∫₋ᵣʳ e^{i x t} dt = 2 r sinc (r x)` (`integral_cexp_eq_two_mul_sinc`), a rescaling of Mathlib's
`integral_exp_mul_I_eq_sinc`.
-/

@[expose] public section

open MeasureTheory intervalIntegral
open Complex (I)

namespace EpsilonEridani

/-- **Differentiation of a finite Fourier integral in the frequency**: for `f` integrable on
`[a, b]`, the derivative of `y ↦ ∫ t in a..b, e^{i y t} f(t)` is
`∫ t in a..b, i t e^{i y t} f(t)`. -/
theorem hasDerivAt_integral_cexp_mul {f : ℝ → ℂ} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in a..b, Complex.exp (I * y * t) * f t)
      (∫ t in a..b, I * t * (Complex.exp (I * x * t) * f t)) x := by
  have hd : ∀ t y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (I * y * t) * f t)
      (I * t * (Complex.exp (I * y * t) * f t)) y := fun t y => by
    have h : HasDerivAt (fun y : ℝ => I * (y : ℂ) * t) (I * t) y := by
      simpa using (((hasDerivAt_id (y : ℂ)).const_mul I).mul_const (t : ℂ)).comp_ofReal
    exact (h.cexp.mul_const (f t)).congr_deriv (by ring)
  -- a continuous function times `f` is measurable on `Set.uIoc a b`
  have hm : ∀ g : ℝ → ℂ, Continuous g →
      AEStronglyMeasurable (fun t => g t * f t) (volume.restrict (Set.uIoc a b)) := fun g hg =>
    hg.aestronglyMeasurable.mul (intervalIntegrable_iff.mp hf).aestronglyMeasurable
  have hF' : AEStronglyMeasurable (fun t : ℝ => I * t * (Complex.exp (I * x * t) * f t))
      (volume.restrict (Set.uIoc a b)) := by
    simpa only [mul_assoc] using hm (fun t : ℝ => I * t * Complex.exp (I * x * t)) (by fun_prop)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := x)
    (bound := fun t : ℝ => |t| * ‖f t‖)
    Filter.univ_mem (.of_forall fun y : ℝ => hm (fun t => Complex.exp (I * y * t)) (by fun_prop))
    (hf.continuousOn_mul
      (by fun_prop : Continuous fun t : ℝ => Complex.exp (I * x * t)).continuousOn)
    hF' (.of_forall fun t _ y _ => ?_) (hf.norm.continuousOn_mul continuous_abs.continuousOn)
    (.of_forall fun t _ y _ => hd t y)).2
  simp [Complex.norm_exp]

/-- The finite Fourier transform of the constant `1` on `[-r, r]`:
`∫₋ᵣʳ e^{i x t} dt = 2 r sinc (r x)`. -/
theorem integral_cexp_eq_two_mul_sinc (r x : ℝ) :
    ∫ t in -r..r, Complex.exp (I * x * t) = 2 * r * (Real.sinc (r * x) : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, Real.sinc_zero, Complex.ofReal_one, Complex.real_smul]
    push_cast
    ring
  · -- rescale `t ↦ x t` to Mathlib's `∫ e^{i u} du = 2 (x r) sinc (x r)` over `[-x r, x r]`
    have h := smul_integral_comp_mul_left (a := -r) (b := r)
      (fun u : ℝ => Complex.exp (u * I)) x
    rw [mul_neg, integral_exp_mul_I_eq_sinc, Complex.real_smul] at h
    have e : ∫ t in -r..r, Complex.exp (I * x * t) =
        ∫ t in -r..r, Complex.exp ((x * t : ℝ) * I) :=
      integral_congr fun t _ => by
        congr 1
        push_cast
        ring
    refine mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hx) ?_
    rw [e, mul_comm r x]
    push_cast at h ⊢
    linear_combination h

end EpsilonEridani
