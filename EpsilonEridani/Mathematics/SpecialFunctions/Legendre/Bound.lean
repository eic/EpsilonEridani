/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.Legendre.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# The bound `|Pₙ (x)| ≤ 1` on `[-1, 1]`

Every Legendre polynomial is bounded by one in absolute value on the closed interval `[-1, 1]`,
and for `n ≥ 1` the bound is attained only at the endpoints `x = ±1`. This is the estimate that
makes a partial-wave expansion `∑ aₙ Pₙ (cos θ)` with summable coefficients converge absolutely
and uniformly in the angle; through the representation `jₗ (x) = (-i)ˡ / 2 ∫₋₁¹ Pₗ (t) e^{ixt} dt`
it also bounds the spherical Bessel functions by one.

## Main statements

* `abs_eval_legendre_le_one`: `|Pₙ (x)| ≤ 1` for `x ∈ [-1, 1]`;
* `abs_eval_legendre_lt_one`: `|Pₙ (x)| < 1` for `n ≠ 0` and `x ∈ (-1, 1)`;
* `abs_eval_legendre_eq_one_iff`: on `[-1, 1]`, `|Pₙ (x)| = 1` exactly when `n = 0` or `|x| = 1`.

## Implementation notes

The proof uses Sonine's function. With `λ = n (n + 1)`, the polynomial

  `Gₙ = λ Pₙ² + (1 - X²) Pₙ'²`

has derivative `Gₙ' = 2 X Pₙ'²` by Legendre's differential equation
(`one_sub_X_sq_mul_derivative_derivative_legendre`), so `Gₙ` is non-decreasing on
`[0, 1]`. Since `Gₙ (1) = λ` and `λ Pₙ (x)² ≤ Gₙ (x)` for `|x| ≤ 1`, this gives `Pₙ (x)² ≤ 1` on
`[0, 1]`, and parity extends it to `[-1, 0]`. If `Pₙ (x)² = 1` at some `x ∈ [0, 1)`, then `Gₙ`
is constant on `[x, 1]`, hence constant as a polynomial, which forces `Pₙ' = 0` and `n = 0`.

## References

* [G. Szegő, *Orthogonal Polynomials*, 4th ed., AMS Colloquium Publications 23 (1975), ch. VII]
* [NIST Digital Library of Mathematical Functions, §18.14(i)](https://dlmf.nist.gov/18.14)
-/

public section

namespace EpsilonEridani

namespace Polynomial

open _root_.Polynomial Set

/-- By parity, `|Pₙ (-x)| = |Pₙ (x)|`. -/
private theorem abs_eval_legendre_neg (n : ℕ) (x : ℝ) :
    |(legendre n).eval (-x)| = |(legendre n).eval x| := by
  simp [abs_mul]

/-- Sonine's function `Gₙ = n (n + 1) Pₙ² + (1 - X²) Pₙ'²` of the Legendre polynomial `Pₙ`. -/
private noncomputable def sonine (n : ℕ) : ℝ[X] :=
  ((n : ℝ[X]) * ((n : ℝ[X]) + 1)) * legendre n ^ 2 + (1 - X ^ 2) * derivative (legendre n) ^ 2

/-- The derivative of Sonine's function is `Gₙ' = 2 X Pₙ'²`. -/
private theorem derivative_sonine (n : ℕ) :
    derivative (sonine n) = 2 * X * derivative (legendre n) ^ 2 := by
  have h := one_sub_X_sq_mul_derivative_derivative_legendre n
  simp only [sonine, derivative_add, derivative_mul, derivative_sub, derivative_one,
    derivative_X, derivative_natCast, derivative_sq, zero_sub, zero_mul, zero_add, add_zero,
    mul_one, C_ofNat]
  linear_combination 2 * derivative (legendre n) * h

private theorem eval_sonine (n : ℕ) (x : ℝ) : (sonine n).eval x =
    n * (n + 1) * (legendre n).eval x ^ 2 + (1 - x ^ 2) * (derivative (legendre n)).eval x ^ 2 := by
  simp [sonine]

/-- `Gₙ (1) = n (n + 1)`. -/
private theorem eval_one_sonine (n : ℕ) : (sonine n).eval 1 = n * (n + 1) := by
  simp [eval_sonine]

/-- Sonine's function dominates `n (n + 1) Pₙ²` on `[-1, 1]`. -/
private theorem mul_sq_le_eval_sonine (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    n * (n + 1) * (legendre n).eval x ^ 2 ≤ (sonine n).eval x := by
  have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  rw [eval_sonine]
  exact le_add_of_nonneg_right (by positivity)

/-- Sonine's function is non-decreasing on `[0, 1]`. -/
private theorem monotoneOn_eval_sonine (n : ℕ) :
    MonotoneOn (fun x => (sonine n).eval x) (Icc 0 1) := by
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) (sonine n).continuousOn
    (sonine n).differentiableOn fun x hx => ?_
  rw [interior_Icc] at hx
  rw [Polynomial.deriv, derivative_sonine]
  simp only [eval_mul, eval_ofNat, eval_X, eval_pow]
  have := hx.1.le
  positivity

/-- On `[0, 1]`, `Pₙ (x)² ≤ 1`. -/
private theorem sq_eval_legendre_le_one_of_nonneg (n : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (legendre n).eval x ^ 2 ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  have hl : (0 : ℝ) < n * (n + 1) := by positivity
  have h₁ : (sonine n).eval x ≤ (sonine n).eval 1 :=
    monotoneOn_eval_sonine n hx (right_mem_Icc.2 zero_le_one) hx.2
  have h₂ := mul_sq_le_eval_sonine n ⟨by linarith [hx.1], hx.2⟩
  rw [eval_one_sonine] at h₁
  nlinarith

/-- **The Legendre polynomials are bounded by one** on `[-1, 1]`: `|Pₙ (x)| ≤ 1`. -/
theorem abs_eval_legendre_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(legendre n).eval x| ≤ 1 := by
  rcases le_total 0 x with h | h
  · exact (sq_le_one_iff_abs_le_one _).1 (sq_eval_legendre_le_one_of_nonneg n ⟨h, hx.2⟩)
  · rw [← neg_neg x, abs_eval_legendre_neg]
    exact (sq_le_one_iff_abs_le_one _).1
      (sq_eval_legendre_le_one_of_nonneg n ⟨by linarith, by linarith [hx.1]⟩)

/-- On `[0, 1)`, `Pₙ (x)² < 1` unless `n = 0`. -/
private theorem sq_eval_legendre_lt_one_of_nonneg {n : ℕ} (hn : n ≠ 0) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) : (legendre n).eval x ^ 2 < 1 := by
  refine (sq_eval_legendre_le_one_of_nonneg n (Ico_subset_Icc_self hx)).lt_of_ne fun hP => hn ?_
  -- `Gₙ` is squeezed between `Gₙ (x) ≥ n (n + 1) = Gₙ (1)` and `Gₙ (1)` on `[x, 1]`.
  have hconst : ∀ y ∈ Icc x 1, (sonine n).eval y = (C ((n : ℝ) * (n + 1))).eval y := by
    intro y hy
    have hx' : x ∈ Icc (0 : ℝ) 1 := Ico_subset_Icc_self hx
    have hy' : y ∈ Icc (0 : ℝ) 1 := ⟨hx.1.trans hy.1, hy.2⟩
    have hle : (sonine n).eval y ≤ (sonine n).eval 1 :=
      monotoneOn_eval_sonine n hy' (right_mem_Icc.2 zero_le_one) hy'.2
    have hge : (sonine n).eval x ≤ (sonine n).eval y := monotoneOn_eval_sonine n hx' hy' hy.1
    have hlow := mul_sq_le_eval_sonine n (x := x) ⟨by linarith [hx.1], hx.2.le⟩
    rw [hP, mul_one] at hlow
    rw [eval_one_sonine] at hle
    rw [eval_C]
    linarith
  -- A polynomial constant on an infinite set is constant, so `2 X Pₙ'² = Gₙ' = 0`.
  have hG : sonine n = C ((n : ℝ) * (n + 1)) :=
    eq_of_infinite_eval_eq _ _ ((Icc_infinite hx.2).mono hconst)
  have hd := derivative_sonine n
  rw [hG, derivative_C, eq_comm] at hd
  have hP' : derivative (legendre n) = 0 := by simpa [X_ne_zero] using hd
  -- A polynomial of degree `n` with vanishing derivative has `n = 0`.
  simpa [natDegree_legendre] using derivative_eq_zero.1 hP'

/-- For `n ≠ 0`, the bound is strict in the open interval: `|Pₙ (x)| < 1` for `x ∈ (-1, 1)`. -/
theorem abs_eval_legendre_lt_one {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    |(legendre n).eval x| < 1 := by
  rcases le_total 0 x with h | h
  · exact (sq_lt_one_iff_abs_lt_one _).1 (sq_eval_legendre_lt_one_of_nonneg hn ⟨h, hx.2⟩)
  · rw [← neg_neg x, abs_eval_legendre_neg]
    exact (sq_lt_one_iff_abs_lt_one _).1
      (sq_eval_legendre_lt_one_of_nonneg hn ⟨by linarith, by linarith [hx.1]⟩)

/-- On `[-1, 1]`, the bound `|Pₙ (x)| ≤ 1` is attained exactly for the constant `P₀ = 1` and at
the endpoints `x = ±1`. -/
theorem abs_eval_legendre_eq_one_iff {n : ℕ} {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    |(legendre n).eval x| = 1 ↔ n = 0 ∨ |x| = 1 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hc
    simp only [not_or] at hc
    have hx' : x ∈ Ioo (-1 : ℝ) 1 := by
      rcases hx with ⟨h₁, h₂⟩
      refine ⟨h₁.lt_of_ne fun e => hc.2 ?_, h₂.lt_of_ne fun e => hc.2 ?_⟩
      · simp [← e]
      · simp [e]
    exact (abs_eval_legendre_lt_one hc.1 hx').ne h
  · rintro (rfl | h)
    · simp
    · rcases abs_eq (zero_le_one' ℝ) |>.1 h with rfl | rfl
      · simp
      · simp

end Polynomial

end EpsilonEridani
