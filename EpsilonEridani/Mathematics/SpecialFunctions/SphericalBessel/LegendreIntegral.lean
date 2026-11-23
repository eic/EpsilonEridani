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
* `ofReal_sphericalBesselJ_eq_integral`: the same identity solved for `j_l(x)`,
  `j_l(x) = (-i) ^ l / 2 ∫₋₁¹ e^{i x t} P_l(t) dt`.
* `sq_sphericalBesselJ_le`: `j_l(x) ^ 2 ≤ 1 / (2 l + 1)`.
* `abs_sphericalBesselJ_le_one` and `abs_sphericalBesselJ_lt_one`: `|j_l(x)| ≤ 1`, strictly for
  `l ≠ 0`.
* `exists_abs_sphericalBesselJ_eq_one_iff`: some `|j_l(x)|` equals `1` if and only if `l = 0`.

## Implementation notes

The representation is proved by induction on `l`. Differentiating under the integral sign
(`hasDerivAt_integral_cexp_mul`) turns multiplication of `P_l(t)` by `t` into `-i d/dx`, so
Bonnet's recurrence for the Legendre polynomials, integrated against `e^{i x t}`
(`Polynomial.add_two_smul_integral_legendre_add_two_smul`), becomes the derivative relation
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

/-- The order-zero case: `∫₋₁¹ e^{i x t} dt = 2 sinc x`. -/
private theorem integral_cexp_mul_legendre_zero (x : ℝ) :
    ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) * (((legendre 0).eval t : ℝ) : ℂ) =
      2 * (Real.sinc x : ℂ) := by
  simp only [legendre_zero, eval_one, Complex.ofReal_one, mul_one]
  rcases eq_or_ne x 0 with rfl | hx
  · norm_num
  · -- rescale `t ↦ x t` to Mathlib's `∫₋ₓˣ e^{i u} du = 2 x sinc x`
    have h := smul_integral_comp_mul_left (a := -1) (b := 1)
      (fun u : ℝ => Complex.exp (u * I)) x
    rw [mul_neg_one, mul_one, integral_exp_mul_I_eq_sinc] at h
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx
    rw [Complex.real_smul] at h
    refine mul_left_cancel₀ hx' ?_
    have e : ∫ t in (-1 : ℝ)..1, Complex.exp (I * x * t) =
        ∫ t in (-1 : ℝ)..1, Complex.exp ((x * t : ℝ) * I) :=
      integral_congr fun t _ => by push_cast; ring_nf
    rw [e]
    linear_combination h

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
    rw [← intervalIntegral.integral_const_mul, ← (hasDerivAt_integral_cexp_mul
      (f := fun t => (((legendre n).eval t : ℝ) : ℂ)) (by fun_prop) (-1) 1 y).unique
      ((hj n y).congr_of_eventuallyEq (.of_forall fun z => h z))]
    exact integral_congr fun t _ => by ring
  induction l using Nat.twoStepInduction generalizing x with
  | zero => simpa using integral_cexp_mul_legendre_zero x
  | one =>
    have h0 := hdiff 0 (fun y => by simpa using integral_cexp_mul_legendre_zero y) x
    simp only [legendre_zero, legendre_one, eval_one, eval_X, Complex.ofReal_one, mul_one,
      pow_zero, pow_one, deriv_sphericalBesselJ_zero, Complex.ofReal_neg] at h0 ⊢
    -- multiply by `i`: the left side becomes `i ∫ t e^{i x t} = -2 j_1(x)`, and `i · i = -1`
    refine mul_left_cancel₀ Complex.I_ne_zero ?_
    rw [integral_congr fun t _ => mul_comm _ _, h0,
      show I * (2 * I * (sphericalBesselJ 1 x : ℂ)) = 2 * (I * I) * sphericalBesselJ 1 x by ring,
      Complex.I_mul_I]
    ring
  | more n h₀ h₁ =>
    set K := ∫ t in (-1 : ℝ)..1, (t : ℂ) * (Complex.exp (I * x * t) *
      (((legendre (n + 1)).eval t : ℝ) : ℂ))
    -- differentiating the order-`n + 1` representation: `K = 2 i ^ n j_{n + 1}'(x)`
    have hK : K = 2 * I ^ n * deriv (sphericalBesselJ (n + 1)) x := by
      refine mul_left_cancel₀ Complex.I_ne_zero ?_
      rw [hdiff (n + 1) h₁ x, pow_succ]
      ring
    -- Bonnet's recurrence against the weight `e^{i x t}`
    have hr := add_two_smul_integral_legendre_add_two_smul n
      (w := fun t : ℝ => Complex.exp (I * x * t)) (by fun_prop)
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
  -- `|e^{i x t}| = 1`, so `2 |j_l(x)| ≤ ∫₋₁¹ |P_l|`
  have hA : 2 * |sphericalBesselJ l x| ≤ A := by
    have h := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (a := -1) (b := 1)
      (f := fun t : ℝ => Complex.exp (I * x * t) * (((legendre l).eval t : ℝ) : ℂ))
      (by norm_num)
    rw [integral_cexp_mul_legendre] at h
    refine le_of_le_of_eq (by simpa [abs_mul] using h) (integral_congr fun t _ => ?_)
    rw [Complex.norm_exp]
    simp
  -- Cauchy–Schwarz on `[-1, 1]`, of length `2`: `(∫₋₁¹ |P_l|) ^ 2 ≤ 2 ∫₋₁¹ P_l ^ 2`
  have hAB : A ^ 2 ≤ 2 * B := by
    have h := CauchySchwarz.sq_setIntegral_abs_le_measureReal_mul_setIntegral_sq
      (μ := volume) (S := Set.Icc (-1 : ℝ) 1) (G := fun t => (legendre l).eval t)
      measure_Icc_lt_top.ne ((memLp_two_iff_integrable_sq
        (legendre l).continuous.aestronglyMeasurable).2
        (by fun_prop : Continuous _).integrableOn_Icc)
    simp only [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
      (by norm_num : (-1 : ℝ) ≤ 1), Real.volume_real_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      sq] at h
    norm_num at h
    rw [sq]
    exact h
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
