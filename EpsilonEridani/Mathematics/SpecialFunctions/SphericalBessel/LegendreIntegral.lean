/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.Legendre.Basic
public import EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The Legendre integral representation of the spherical Bessel functions

The spherical Bessel function of the first kind of order `l` is, up to the factor `(-i) ^ l / 2`,
the Fourier transform of the Legendre polynomial `P_l` on `[-1, 1]`:

  `∫₋₁¹ e^{i x t} P_l(t) dt = 2 i ^ l j_l(x)`

(DLMF 10.54.2). Up to the factor `(2 l + 1) / 2`, these integrals are the coefficients of the
Legendre expansion of the plane wave `e^{i x t}` in `t`, so the representation is the analytic
input of the partial-wave expansion of a plane wave. It also bounds the `j_l` uniformly: since
`|e^{i x t}| = 1`, the Cauchy–Schwarz inequality and the Legendre normalisation
`∫₋₁¹ P_l² = 2 / (2 l + 1)` give `j_l(x) ^ 2 ≤ 1 / (2 l + 1)` on the whole line. In particular
`|j_l(x)| ≤ 1`, the inequality is strict for every `l ≠ 0`, and the bound `1` is attained, at the
origin, only by `j_0`.

## Main statements

* `integral_cexp_mul_legendre`: `∫₋₁¹ e^{i x t} P_l(t) dt = 2 i ^ l j_l(x)` for every real `x`.
* `ofReal_sphericalBesselJ_eq_integral`: the same identity solved for `j_l(x)`,
  `j_l(x) = (-i) ^ l / 2 ∫₋₁¹ e^{i x t} P_l(t) dt`.
* `sq_sphericalBesselJ_le`: `j_l(x) ^ 2 ≤ 1 / (2 l + 1)`.
* `abs_sphericalBesselJ_le_one` and `abs_sphericalBesselJ_lt_one`: `|j_l(x)| ≤ 1`, strictly for
  `l ≠ 0`.
* `exists_abs_sphericalBesselJ_eq_one_iff`: some `|j_l(x)|` equals `1` if and only if `l = 0`.

## Implementation notes

The representation is proved by induction on `l`. Differentiating under the integral sign turns
multiplication of `P_l(t)` by `t` into `-i d/dx`, so Bonnet's recurrence for the Legendre
polynomials becomes the derivative relation
`(2 l + 3) j_{l + 1}' = (l + 1) j_l - (l + 2) j_{l + 2}`
(`two_mul_add_three_mul_deriv_sphericalBesselJ_succ`), which determines `j_{l + 2}` from `j_l` and
`j_{l + 1}`. The base case is the elementary integral `∫₋₁¹ e^{i x t} dt = 2 sin x / x`.

## References

* NIST Digital Library of Mathematical Functions, §10.54 (integral representations).
* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §10.1.
-/

public section

open MeasureTheory intervalIntegral
open Complex (I)
open Polynomial EpsilonEridani.Polynomial

namespace EpsilonEridani

/-- The integrand `e^{i x t} p(t)`, differentiated in `x` under the integral sign over `[-1, 1]`:
the derivative of `x ↦ ∫₋₁¹ e^{i x t} p(t) dt` is `∫₋₁¹ i t e^{i x t} p(t) dt`. -/
private theorem hasDerivAt_integral_cexp_mul_eval (p : ℝ[X]) (x : ℝ) :
    HasDerivAt (fun y : ℝ => ∫ t in (-1 : ℝ)..1, Complex.exp (I * y * t) * ((p.eval t : ℝ) : ℂ))
      (∫ t in (-1 : ℝ)..1, I * t * (Complex.exp (I * x * t) * ((p.eval t : ℝ) : ℂ))) x := by
  have hd : ∀ t y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (I * y * t) * ((p.eval t : ℝ) : ℂ))
      (I * t * (Complex.exp (I * y * t) * ((p.eval t : ℝ) : ℂ))) y := fun t y => by
    have h : HasDerivAt (fun y : ℝ => I * (y : ℂ) * t) (I * t) y := by
      simpa using (((hasDerivAt_id (y : ℂ)).const_mul I).mul_const (t : ℂ)).comp_ofReal
    convert h.cexp.mul_const ((p.eval t : ℝ) : ℂ) using 1
    ring
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t => |t| * |p.eval t|)
    Filter.univ_mem (.of_forall fun y => (by fun_prop : Continuous _).aestronglyMeasurable)
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
    (by fun_prop : Continuous _).aestronglyMeasurable (.of_forall fun t _ y _ => ?_)
    ((by fun_prop : Continuous _).intervalIntegrable _ _)
    (.of_forall fun t _ y _ => hd t y)).2
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
    Complex.norm_exp]
  simp

/-- Bonnet's recurrence inside the Fourier integral over `[-1, 1]`:
`(2 n + 3) ∫ t e^{i x t} P_{n + 1} = (n + 2) ∫ e^{i x t} P_{n + 2} + (n + 1) ∫ e^{i x t} P_n`. -/
private theorem integral_mul_cexp_mul_legendre_succ (n : ℕ) (x : ℝ) :
    (2 * n + 3) * ∫ t in (-1 : ℝ)..1, (t : ℂ) * (Complex.exp (I * x * t) *
        (((legendre (n + 1)).eval t : ℝ) : ℂ)) =
      (n + 2) * (∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) *
          (((legendre (n + 2)).eval t : ℝ) : ℂ)) +
        (n + 1) * ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) *
          (((legendre n).eval t : ℝ) : ℂ) := by
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _)
    ((by fun_prop : Continuous _).intervalIntegrable _ _)]
  refine integral_congr fun t _ => ?_
  have h := congrArg (fun r : ℝ => (r : ℂ)) (add_two_mul_legendre_add_two_eval n t)
  push_cast at h
  linear_combination -Complex.exp (I * x * t) * h

/-- The order-zero case: `∫₋₁¹ e^{i x t} dt = 2 sinc x`. -/
private theorem integral_cexp_mul_legendre_zero (x : ℝ) :
    ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) * (((legendre 0).eval t : ℝ) : ℂ) =
      2 * (Real.sinc x : ℂ) := by
  simp only [legendre_zero, eval_one, Complex.ofReal_one, mul_one]
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · have hc : I * x ≠ 0 := mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx)
    rw [integral_exp_mul_complex hc, Real.sinc_of_ne_zero hx]
    simp only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg_one]
    have e₁ : Complex.exp (I * x) = Complex.cos x + Complex.sin x * I := by
      rw [mul_comm, Complex.exp_mul_I]
    have e₂ : Complex.exp (-(I * x)) = Complex.cos x - Complex.sin x * I := by
      rw [show -(I * (x : ℂ)) = -(x : ℂ) * I by ring, Complex.exp_mul_I, Complex.cos_neg,
        Complex.sin_neg]
      ring
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    rw [e₁, e₂]
    push_cast
    field_simp
    ring

/-- **The Legendre integral representation of the spherical Bessel functions**:
`∫₋₁¹ e^{i x t} P_l(t) dt = 2 i ^ l j_l(x)` for every real `x` (DLMF 10.54.2). Multiplied by
`(2 l + 1) / 2`, the left side is the `l`-th Legendre coefficient of the plane wave `e^{i x t}`. -/
theorem integral_cexp_mul_legendre (l : ℕ) (x : ℝ) :
    ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) * (((legendre l).eval t : ℝ) : ℂ) =
      2 * I ^ l * sphericalBesselJ l x := by
  -- the derivative of the right side, through the derivative of `j_l`
  have hj : ∀ (l : ℕ) (y : ℝ), HasDerivAt (fun y : ℝ => 2 * I ^ l * (sphericalBesselJ l y : ℂ))
      (2 * I ^ l * deriv (sphericalBesselJ l) y) y := fun l y =>
    ((differentiable_sphericalBesselJ l y).hasDerivAt.ofReal_comp).const_mul _
  -- if the representation holds at order `n`, differentiating it identifies the
  -- `t`-weighted integral of order `n` with the derivative of `j_n`
  have hdiff : ∀ (n : ℕ), (∀ y : ℝ, ∫ t in (-1 : ℝ)..1, Complex.exp (I * y * t) *
      (((legendre n).eval t : ℝ) : ℂ) = 2 * I ^ n * sphericalBesselJ n y) → ∀ y : ℝ,
      I * ∫ t in (-1 : ℝ)..1, (t : ℂ) * (Complex.exp (I * y * t) *
        (((legendre n).eval t : ℝ) : ℂ)) =
        2 * I ^ n * deriv (sphericalBesselJ n) y := fun n h y => by
    rw [← intervalIntegral.integral_const_mul, ← (hasDerivAt_integral_cexp_mul_eval (legendre n)
      y).unique ((hj n y).congr_of_eventuallyEq (.of_forall fun z => h z))]
    exact integral_congr fun t _ => by ring
  induction l using Nat.twoStepInduction generalizing x with
  | zero => simpa using integral_cexp_mul_legendre_zero x
  | one =>
    have h0 := hdiff 0 (fun y => by simpa using integral_cexp_mul_legendre_zero y) x
    simp only [legendre_zero, legendre_one, eval_one, eval_X, Complex.ofReal_one, mul_one,
      pow_zero, deriv_sphericalBesselJ_zero, Complex.ofReal_neg] at h0 ⊢
    have h1 : ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) * (t : ℂ) =
        ∫ t in (-1 : ℝ)..1, (t : ℂ) * Complex.exp (I * x * t) :=
      integral_congr fun t _ => mul_comm _ _
    rw [h1]
    linear_combination (-I) * h0 + (∫ t in (-1 : ℝ)..1, (t : ℂ) * Complex.exp (I * x * t)) *
      Complex.I_sq
  | more n h₀ h₁ =>
    have hd := hdiff (n + 1) h₁ x
    have hr := integral_mul_cexp_mul_legendre_succ n x
    have hl := congrArg (fun r : ℝ => (r : ℂ))
      (two_mul_add_three_mul_deriv_sphericalBesselJ_succ n x)
    push_cast at hl
    rw [h₀ x] at hr
    refine mul_left_cancel₀ (by norm_cast : ((n : ℂ) + 2) ≠ 0) ?_
    set K := ∫ t in (-1 : ℝ)..1, (t : ℂ) * (Complex.exp (I * x * t) *
      (((legendre (n + 1)).eval t : ℝ) : ℂ))
    linear_combination -hr - (2 * n + 3) * I * hd + 2 * I ^ n * hl +
      ((2 * n + 3) * (K - 2 * I ^ n * ((deriv (sphericalBesselJ (n + 1)) x : ℝ) : ℂ)) -
        2 * (n + 2) * I ^ n * ((sphericalBesselJ (n + 2) x : ℝ) : ℂ)) * Complex.I_sq

/-- The Legendre integral representation solved for the spherical Bessel function:
`j_l(x) = (-i) ^ l / 2 ∫₋₁¹ e^{i x t} P_l(t) dt` (DLMF 10.54.2). -/
theorem ofReal_sphericalBesselJ_eq_integral (l : ℕ) (x : ℝ) :
    (sphericalBesselJ l x : ℂ) = (-I) ^ l / 2 *
      ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) * (((legendre l).eval t : ℝ) : ℂ) := by
  have h : (-I) ^ l * I ^ l = 1 := by
    rw [← mul_pow, neg_mul, Complex.I_mul_I, neg_neg, one_pow]
  rw [integral_cexp_mul_legendre]
  linear_combination (-(sphericalBesselJ l x : ℂ)) * h

/-- **The uniform bound on the spherical Bessel functions**: `j_l(x) ^ 2 ≤ 1 / (2 l + 1)` for
every real `x`. It is attained at `l = 0`, `x = 0`, where `j_0(0) = 1`. -/
theorem sq_sphericalBesselJ_le (l : ℕ) (x : ℝ) : sphericalBesselJ l x ^ 2 ≤ 1 / (2 * l + 1) := by
  set A := ∫ t in (-1 : ℝ)..1, |(legendre l).eval t|
  set B := ∫ t in (-1 : ℝ)..1, (legendre l).eval t * (legendre l).eval t
  have hB : B = 2 / (2 * l + 1) := integral_legendre_mul_self l
  have hB₀ : 0 < B := hB ▸ by positivity
  -- `|e^{i x t}| = 1`, so `2 |j_l(x)| ≤ ∫₋₁¹ |P_l|`
  have hA : 2 * |sphericalBesselJ l x| ≤ A := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := -1) (b := 1)
      (f := fun t : ℝ => Complex.exp (I * x * t) * (((legendre l).eval t : ℝ) : ℂ))
      (by norm_num)
    rw [integral_cexp_mul_legendre] at h
    refine le_of_le_of_eq (by simpa [abs_mul] using h) (integral_congr fun t _ => ?_)
    rw [Complex.norm_exp]
    simp
  -- integrating `(c |P_l| - 1) ^ 2 ≥ 0`: `2 c ∫ |P_l| ≤ c ^ 2 ∫ P_l ^ 2 + 2` for every `c`
  have hc : ∀ c : ℝ, 2 * c * A ≤ c ^ 2 * B + 2 := fun c => by
    have h : 0 ≤ ∫ t in (-1 : ℝ)..1, (c * |(legendre l).eval t| - 1) ^ 2 :=
      integral_nonneg (by norm_num) fun t _ => sq_nonneg _
    have e : ∫ t in (-1 : ℝ)..1, (c * |(legendre l).eval t| - 1) ^ 2 =
        c ^ 2 * B - 2 * c * A + 2 := by
      have hp : ∀ t : ℝ, (c * |(legendre l).eval t| - 1) ^ 2 =
          c ^ 2 * ((legendre l).eval t * (legendre l).eval t) -
            2 * c * |(legendre l).eval t| + 1 := fun t => by
        rw [← abs_mul_abs_self ((legendre l).eval t)]
        ring
      simp_rw [hp]
      rw [integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _)
          intervalIntegrable_const,
        integral_sub ((by fun_prop : Continuous _).intervalIntegrable _ _)
          ((by fun_prop : Continuous _).intervalIntegrable _ _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      simp only [A, B]
      norm_num
    linarith
  -- the choice `c = A / B` gives `A ^ 2 ≤ 2 B = 4 / (2 l + 1)`
  have hAB : A ^ 2 ≤ 2 * B := by
    have h := hc (A / B)
    field_simp at h
    nlinarith
  have hB' : B * (2 * l + 1) = 2 := by
    rw [hB]
    field_simp
  have hsq : (2 * |sphericalBesselJ l x|) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA 2
  rw [mul_pow, sq_abs] at hsq
  have hl : (0 : ℝ) ≤ 2 * l + 1 := by positivity
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hsq hl, mul_le_mul_of_nonneg_right hAB hl]

/-- The spherical Bessel functions are bounded by one: `|j_l(x)| ≤ 1` for every real `x`. -/
theorem abs_sphericalBesselJ_le_one (l : ℕ) (x : ℝ) : |sphericalBesselJ l x| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  exact (sq_sphericalBesselJ_le l x).trans (div_le_one_of_le₀ (by linarith) (by positivity))

/-- For `l ≠ 0` the bound is strict: `|j_l(x)| < 1` for every real `x`. -/
theorem abs_sphericalBesselJ_lt_one {l : ℕ} (hl : l ≠ 0) (x : ℝ) : |sphericalBesselJ l x| < 1 := by
  rw [← sq_lt_one_iff_abs_lt_one]
  have : (1 : ℝ) ≤ l := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hl)
  exact (sq_sphericalBesselJ_le l x).trans_lt ((div_lt_one (by positivity)).mpr (by linarith))

/-- The bound `|j_l(x)| ≤ 1` is attained only at order zero: some `|j_l(x)|` equals `1` if and
only if `l = 0`, and then at `x = 0`, where `j_0(0) = 1`. -/
theorem exists_abs_sphericalBesselJ_eq_one_iff (l : ℕ) :
    (∃ x, |sphericalBesselJ l x| = 1) ↔ l = 0 := by
  refine ⟨fun ⟨x, hx⟩ => by_contra fun hl => (abs_sphericalBesselJ_lt_one hl x).ne hx,
    fun hl => ⟨0, by simp [hl]⟩⟩

end EpsilonEridani
