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

For a function `f : ℝ → ℂ` continuous on a bounded interval `[a, b]`, the finite Fourier integral
`y ↦ ∫ t in a..b, e^{i y t} f(t)` is differentiable, with derivative obtained by differentiating
under the integral sign: multiplication of the integrand by `i t`
(`hasDerivAt_integral_cexp_mul`). This turns multiplication by the integration variable into
differentiation in the frequency, which is how recurrences for a family of functions `f` (such as
Bonnet's recurrence for the Legendre polynomials) become differential relations for their
finite Fourier transforms (such as those between the spherical Bessel functions).

The simplest such integral, of the constant `1` over `[-1, 1]`, is
`∫₋₁¹ e^{i x t} dt = 2 sinc x` (`integral_cexp_eq_two_mul_sinc`), a rescaling of Mathlib's
`integral_exp_mul_I_eq_sinc`.
-/

@[expose] public section

open MeasureTheory intervalIntegral
open Complex (I)

namespace EpsilonEridani

/-- **Differentiation of a finite Fourier integral in the frequency**: for `f` continuous on
`[a, b]`, the derivative of `y ↦ ∫ t in a..b, e^{i y t} f(t)` is
`∫ t in a..b, i t e^{i y t} f(t)`. -/
theorem hasDerivAt_integral_cexp_mul {f : ℝ → ℂ} {a b : ℝ} (hf : ContinuousOn f (Set.uIcc a b))
    (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in a..b, Complex.exp (I * y * t) * f t)
      (∫ t in a..b, I * t * (Complex.exp (I * x * t) * f t)) x := by
  have hd : ∀ t y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (I * y * t) * f t)
      (I * t * (Complex.exp (I * y * t) * f t)) y := fun t y => by
    have h : HasDerivAt (fun y : ℝ => I * (y : ℂ) * t) (I * t) y := by
      simpa using (((hasDerivAt_id (y : ℂ)).const_mul I).mul_const (t : ℂ)).comp_ofReal
    exact (h.cexp.mul_const (f t)).congr_deriv (by ring)
  -- every integrand in sight is continuous on `[a, b]`, hence on `Set.uIoc a b ⊆ [a, b]`
  have hc : ∀ g : ℝ → ℂ, Continuous g → ContinuousOn (fun t => g t * f t) (Set.uIcc a b) :=
    fun g hg => hg.continuousOn.mul hf
  have hm : ∀ g : ℝ → ℂ, Continuous g →
      AEStronglyMeasurable (fun t => g t * f t) (volume.restrict (Set.uIoc a b)) := fun g hg =>
    ((hc g hg).mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF' : AEStronglyMeasurable (fun t : ℝ => I * t * (Complex.exp (I * x * t) * f t))
      (volume.restrict (Set.uIoc a b)) := by
    simpa only [mul_assoc] using hm (fun t : ℝ => I * t * Complex.exp (I * x * t)) (by fun_prop)
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (x₀ := x)
    (bound := fun t : ℝ => |t| * ‖f t‖)
    Filter.univ_mem (.of_forall fun y : ℝ => hm (fun t => Complex.exp (I * y * t)) (by fun_prop))
    (hc (fun t => Complex.exp (I * x * t)) (by fun_prop)).intervalIntegrable hF'
    (.of_forall fun t _ y _ => ?_) (continuous_abs.continuousOn.mul hf.norm).intervalIntegrable
    (.of_forall fun t _ y _ => hd t y)).2
  simp [Complex.norm_exp]

/-- The finite Fourier transform of the constant `1` on `[-1, 1]`:
`∫₋₁¹ e^{i x t} dt = 2 sinc x`. -/
theorem integral_cexp_eq_two_mul_sinc (x : ℝ) :
    ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) = 2 * (Real.sinc x : ℂ) := by
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · -- rescale `t ↦ x t` to Mathlib's `∫₋ₓˣ e^{i u} du = 2 x sinc x`
    have h := smul_integral_comp_mul_left (a := -1) (b := 1)
      (fun u : ℝ => Complex.exp (u * I)) x
    rw [mul_neg_one, mul_one, integral_exp_mul_I_eq_sinc, Complex.real_smul] at h
    have e : ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) =
        ∫ t in (-1 : ℝ)..1, Complex.exp ((x * t : ℝ) * I) :=
      integral_congr fun t _ => by
        congr 1
        push_cast
        ring
    refine mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hx) ?_
    rw [e]
    linear_combination h

end EpsilonEridani
