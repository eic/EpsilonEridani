/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Calculus.IntervalIntegralCexp
public import EpsilonEridani.Mathematics.CauchySchwarz
public import EpsilonEridani.Mathematics.SpecialFunctions.Legendre.Basic
public import EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic

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
* `sq_sphericalBesselJ_le`: `j_l(x) ^ 2 ≤ 1 / (2 l + 1)`.
* `abs_sphericalBesselJ_le_one` and `abs_sphericalBesselJ_lt_one`: `|j_l(x)| ≤ 1`, strictly for
  `l ≠ 0`.
* `abs_sphericalBesselJ_eq_one_iff`: `|j_l(x)| = 1` if and only if `l = 0` and `x = 0`; and
  `exists_abs_sphericalBesselJ_eq_one_iff`: some `|j_l(x)|` equals `1` if and only if `l = 0`.

## Implementation notes

The representation is proved by induction on `l`. Differentiating under the integral sign
(`hasDerivAt_integral_cexp_mul`) turns multiplication of `P_l(t)` by `t` into `-i d/dx`, so
Bonnet's recurrence for the Legendre polynomials, integrated against `e^{i x t}`
(`EpsilonEridani.Polynomial.add_two_smul_integral_legendre_add_two_smul`), becomes the
derivative relation `(2 l + 3) j_{l + 1}' = (l + 1) j_l - (l + 2) j_{l + 2}`
(`two_mul_add_three_mul_deriv_sphericalBesselJ_succ`), which determines `j_{l + 2}` from `j_l`
and `j_{l + 1}`. The base case is the elementary integral `∫₋₁¹ e^{i x t} dt = 2 sin x / x`
(`integral_cexp_eq_two_mul_sinc`).

## References

* NIST Digital Library of Mathematical Functions, §10.54 (integral representations).
* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §10.1.
-/

public section

open MeasureTheory intervalIntegral
open Complex (I)
open Polynomial EpsilonEridani.Polynomial

namespace EpsilonEridani

/-- Differentiating the representation at order `n`: if `∫₋₁¹ e^{i y t} P_n(t) dt = 2 i ^ n j_n(y)`
for every `y`, then the `t`-weighted integral satisfies
`i ∫₋₁¹ t e^{i x t} P_n(t) dt = 2 i ^ n j_n'(x)`. -/
private theorem I_mul_integral_mul_cexp_mul_legendre {n : ℕ}
    (h : ∀ y : ℝ, ∫ t in (-1 : ℝ)..1, Complex.exp (I * y * t) * (((legendre n).eval t : ℝ) : ℂ) =
      2 * I ^ n * sphericalBesselJ n y) (x : ℝ) :
    I * ∫ t in (-1 : ℝ)..1, (t : ℂ) * (Complex.exp (I * x * t) *
      (((legendre n).eval t : ℝ) : ℂ)) = 2 * I ^ n * deriv (sphericalBesselJ n) x := by
  have hj : HasDerivAt (fun y : ℝ => 2 * I ^ n * (sphericalBesselJ n y : ℂ))
      (2 * I ^ n * deriv (sphericalBesselJ n) x) x :=
    ((differentiable_sphericalBesselJ n x).hasDerivAt.ofReal_comp).const_mul _
  have hP : IntervalIntegrable (fun t : ℝ => (((legendre n).eval t : ℝ) : ℂ)) volume (-1) 1 :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul,
    ← (hasDerivAt_integral_cexp_mul hP x).unique (hj.congr_of_eventuallyEq (.of_forall h))]
  exact integral_congr fun t _ => by ring

/-- **The Legendre integral representation of the spherical Bessel functions**:
`∫₋₁¹ e^{i x t} P_l(t) dt = 2 i ^ l j_l(x)` for every real `x` (DLMF 10.54.2). Multiplied by
`(2 l + 1) / 2`, the left side is the `l`-th Legendre coefficient of the plane wave `e^{i x t}`. -/
theorem integral_cexp_mul_legendre (l : ℕ) (x : ℝ) :
    ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) * (((legendre l).eval t : ℝ) : ℂ) =
      2 * I ^ l * sphericalBesselJ l x := by
  have h0 : ∀ y : ℝ, ∫ t in (-1 : ℝ)..1, Complex.exp (I * y * t) *
      (((legendre 0).eval t : ℝ) : ℂ) = 2 * I ^ 0 * sphericalBesselJ 0 y := fun y => by
    simpa using integral_cexp_eq_two_mul_sinc 1 y
  induction l using Nat.twoStepInduction generalizing x with
  | zero => exact h0 x
  | one =>
    have h := I_mul_integral_mul_cexp_mul_legendre h0 x
    simp only [legendre_zero, legendre_one, eval_one, eval_X, Complex.ofReal_one, mul_one,
      pow_zero, pow_one, deriv_sphericalBesselJ_zero, Complex.ofReal_neg] at h ⊢
    -- multiply by `i`: the left side becomes `i ∫ t e^{i x t} = -2 j_1(x)`, the right side
    -- `i · 2 i j_1(x) = 2 i ^ 2 j_1(x)`, and `i ^ 2 = -1`
    refine mul_left_cancel₀ Complex.I_ne_zero ?_
    rw [integral_congr fun t _ => mul_comm _ _, h]
    linear_combination (-2 * (sphericalBesselJ 1 x : ℂ)) * Complex.I_sq
  | more n h₀ h₁ =>
    set K := ∫ t in (-1 : ℝ)..1, (t : ℂ) * (Complex.exp (I * x * t) *
      (((legendre (n + 1)).eval t : ℝ) : ℂ))
    -- differentiating the order-`n + 1` representation: `K = 2 i ^ n j_{n + 1}'(x)`
    have hK : K = 2 * I ^ n * deriv (sphericalBesselJ (n + 1)) x := by
      refine mul_left_cancel₀ Complex.I_ne_zero ?_
      rw [I_mul_integral_mul_cexp_mul_legendre h₁ x, pow_succ]
      ring
    -- Bonnet's recurrence against the weight `e^{i x t}`
    have hr := add_two_smul_integral_legendre_add_two_smul n
      ((by fun_prop : Continuous fun t : ℝ => Complex.exp (I * x * t)).intervalIntegrable _ _)
    have e : ∀ p : ℝ[X], ∫ t in (-1 : ℝ)..1, p.eval t • Complex.exp (I * x * t) =
        ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) * ((p.eval t : ℝ) : ℂ) :=
      fun p => integral_congr fun t _ => by rw [Complex.real_smul, mul_comm]
    have eK : ∫ t in (-1 : ℝ)..1, (t * (legendre (n + 1)).eval t) • Complex.exp (I * x * t) =
        K := integral_congr fun t _ => by
      rw [Complex.real_smul, Complex.ofReal_mul]
      ring
    rw [e, e, eK, h₀ x] at hr
    simp only [Complex.real_smul] at hr
    push_cast at hr
    have hl := congrArg (fun r : ℝ => (r : ℂ))
      (two_mul_add_three_mul_deriv_sphericalBesselJ_succ n x)
    push_cast at hl
    have hI : I ^ (n + 2) = -I ^ n := by rw [pow_add, Complex.I_sq, mul_neg_one]
    rw [hI]
    refine mul_left_cancel₀ (by norm_cast : ((n : ℂ) + 2) ≠ 0) ?_
    linear_combination hr + (2 * n + 3) * hK + 2 * I ^ n * hl

/-- **The uniform bound on the spherical Bessel functions**: `j_l(x) ^ 2 ≤ 1 / (2 l + 1)` for
every real `x`. It is attained at `l = 0`, `x = 0`, where `j_0(0) = 1`. -/
theorem sq_sphericalBesselJ_le (l : ℕ) (x : ℝ) : sphericalBesselJ l x ^ 2 ≤ 1 / (2 * l + 1) := by
  set A := ∫ t in (-1 : ℝ)..1, |(legendre l).eval t|
  -- `|e^{i x t}| = 1`, so `2 |j_l(x)| ≤ ∫₋₁¹ |P_l|`
  have hA : 2 * |sphericalBesselJ l x| ≤ A := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := -1) (b := 1)
      (f := fun t : ℝ => Complex.exp (I * x * t) * (((legendre l).eval t : ℝ) : ℂ))
      (by norm_num)
    have hnorm : ∀ t : ℝ,
        ‖Complex.exp (I * x * t) * (((legendre l).eval t : ℝ) : ℂ)‖ = |(legendre l).eval t| :=
      fun t => by
        rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
        simp
    rw [integral_cexp_mul_legendre, integral_congr fun t _ => hnorm t] at h
    simpa [abs_mul] using h
  -- Cauchy–Schwarz on `[-1, 1]`, of length `2`: `(∫₋₁¹ |P_l|) ^ 2 ≤ 2 ∫₋₁¹ P_l ^ 2`
  have hAB : A ^ 2 ≤ 2 * (2 / (2 * l + 1)) := by
    have h := CauchySchwarz.sq_setIntegral_abs_le_measureReal_mul_setIntegral_sq
      (μ := volume) (S := Set.Icc (-1 : ℝ) 1) (G := fun t => (legendre l).eval t)
      measure_Icc_lt_top.ne ((memLp_two_iff_integrable_sq
        (legendre l).continuous.aestronglyMeasurable).2
        (by fun_prop : Continuous _).integrableOn_Icc)
    have hI : volume.real (Set.Icc (-1 : ℝ) 1) = 2 := by
      rw [Real.volume_real_Icc_of_le (by norm_num)]
      norm_num
    -- the Legendre normalisation as a set integral over `[-1, 1]`
    have hN : ∫ t in Set.Icc (-1 : ℝ) 1, (legendre l).eval t ^ 2 = 2 / (2 * l + 1) := by
      simpa [sq] using setIntegral_Icc_legendre_mul_legendre l l
    rwa [hI, hN, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
      at h
  have hN' : 2 / (2 * l + 1) * (2 * l + 1) = (2 : ℝ) := by
    field_simp
  have hsq : (2 * |sphericalBesselJ l x|) ^ 2 ≤ A ^ 2 :=
    pow_le_pow_left₀ (by positivity) hA 2
  rw [mul_pow, sq_abs] at hsq
  have hl : (0 : ℝ) ≤ 2 * l + 1 := by positivity
  rw [le_div_iff₀ (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right hsq hl, mul_le_mul_of_nonneg_right hAB hl, hN']

/-- The spherical Bessel functions are bounded by one: `|j_l(x)| ≤ 1` for every real `x`. -/
theorem abs_sphericalBesselJ_le_one (l : ℕ) (x : ℝ) : |sphericalBesselJ l x| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  exact (sq_sphericalBesselJ_le l x).trans (div_le_one_of_le₀ (by linarith) (by positivity))

/-- For `l ≠ 0` the bound is strict: `|j_l(x)| < 1` for every real `x`. -/
theorem abs_sphericalBesselJ_lt_one {l : ℕ} (hl : l ≠ 0) (x : ℝ) : |sphericalBesselJ l x| < 1 := by
  rw [← sq_lt_one_iff_abs_lt_one]
  have : (1 : ℝ) ≤ l := Nat.one_le_cast.mpr (Nat.one_le_iff_ne_zero.mpr hl)
  exact (sq_sphericalBesselJ_le l x).trans_lt ((div_lt_one (by positivity)).mpr (by linarith))

/-- The bound `|j_l(x)| ≤ 1` is attained only by `j_0` at the origin: `|j_l(x)| = 1` if and only
if `l = 0` and `x = 0`. -/
@[simp]
theorem abs_sphericalBesselJ_eq_one_iff (l : ℕ) (x : ℝ) :
    |sphericalBesselJ l x| = 1 ↔ l = 0 ∧ x = 0 := by
  refine ⟨fun h => ?_, fun ⟨hl, hx⟩ => by simp [hl, hx]⟩
  obtain rfl : l = 0 := by_contra fun hl => (abs_sphericalBesselJ_lt_one hl x).ne h
  refine ⟨rfl, by_contra fun hx => ?_⟩
  -- away from the origin `|j_0(x)| = |sin x| / |x| < 1`
  rw [sphericalBesselJ_zero, Real.sinc_of_ne_zero hx, abs_div,
    div_eq_one_iff_eq (abs_ne_zero.mpr hx)] at h
  exact (Real.abs_sin_lt_abs hx).ne h

/-- Some `|j_l(x)|` equals `1` if and only if `l = 0`. -/
theorem exists_abs_sphericalBesselJ_eq_one_iff (l : ℕ) :
    (∃ x, |sphericalBesselJ l x| = 1) ↔ l = 0 := by
  simp

end EpsilonEridani
