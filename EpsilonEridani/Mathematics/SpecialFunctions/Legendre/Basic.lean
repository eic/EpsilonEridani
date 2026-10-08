/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Calculus.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Legendre polynomials

The Legendre polynomials `Pₙ : ℝ[X]` are defined by Bonnet's three-term recurrence

  `P₀ = 1`, `P₁ = X`, `(n + 2) Pₙ₊₂ = (2n + 3) X Pₙ₊₁ - (n + 1) Pₙ`,

and this file develops their algebraic theory and their orthogonality on `[-1, 1]`. They are the
angular functions of the partial-wave expansion: a function of the angle between two directions
is expanded in `Pₙ (cos θ)`, and orthogonality is what makes the coefficients of that expansion
unique.

## Main definitions

* `EpsilonEridani.Polynomial.legendre n`: the Legendre polynomial `Pₙ`.

## Main statements

* `legendre_add_two`: the three-term recurrence;
* `natDegree_legendre`, `leadingCoeff_legendre`: `Pₙ` has degree `n` and leading coefficient
  `(2n choose n) / 2ⁿ`;
* `legendre_comp_neg_X`: the parity relation `Pₙ (-X) = (-1)ⁿ Pₙ`;
* `legendre_eval_one`, `legendre_eval_neg_one`: `Pₙ (1) = 1` and `Pₙ (-1) = (-1)ⁿ`;
* `derivative_legendre_succ`, `X_mul_derivative_legendre_succ`,
  `one_sub_X_sq_mul_derivative_legendre_succ`: the ladder relations for the derivatives;
* `derivative_one_sub_X_sq_mul_derivative_legendre`: Legendre's differential equation
  `((1 - X²) Pₙ')' = -n (n + 1) Pₙ`;
* `integral_legendre_mul_legendre`: the orthogonality relation
  `∫₋₁¹ Pₘ Pₙ = if m = n then 2 / (2n + 1) else 0`.

Mathlib's `Polynomial.shiftedLegendre` is the integer-coefficient family on `[0, 1]` given by
explicit coefficients, with its Rodrigues formula. The two are related by
`Pₙ (x) = shiftedLegendre n ((1 - x) / 2)`; that identification is not formalised here.

## References

* [M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, ch. 8 and 22]
* [NIST Digital Library of Mathematical Functions, §18.3, §18.8, §18.9](https://dlmf.nist.gov/18)
-/

@[expose] public section

namespace EpsilonEridani

namespace Polynomial

open _root_.Polynomial

/-- The **Legendre polynomial** `Pₙ`, defined by `P₀ = 1`, `P₁ = X` and Bonnet's recurrence
`(n + 2) Pₙ₊₂ = (2n + 3) X Pₙ₊₁ - (n + 1) Pₙ` (see `legendre_add_two`). -/
noncomputable def legendre : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => C ((n + 2 : ℝ)⁻¹) *
      ((2 * n + 3 : ℝ[X]) * X * legendre (n + 1) - (n + 1 : ℝ[X]) * legendre n)

/-- `P₀ = 1`. -/
@[simp] theorem legendre_zero : legendre 0 = 1 := by rw [legendre]

/-- `P₁ = X`. -/
@[simp] theorem legendre_one : legendre 1 = X := by rw [legendre]

/-- **Bonnet's recurrence** `(n + 2) Pₙ₊₂ = (2n + 3) X Pₙ₊₁ - (n + 1) Pₙ`, the defining relation
of the Legendre polynomials. -/
theorem legendre_add_two (n : ℕ) : (n + 2 : ℝ[X]) * legendre (n + 2) =
    (2 * n + 3 : ℝ[X]) * X * legendre (n + 1) - (n + 1 : ℝ[X]) * legendre n := by
  rw [legendre, ← mul_assoc]
  convert one_mul _
  have hcoeff : (n + 2 : ℝ[X]) = C (n + 2 : ℝ) := rfl
  rw [hcoeff, ← C_mul, mul_inv_cancel₀ (by positivity), C_1]

/-- Bonnet's recurrence evaluated at a point. -/
theorem legendre_eval_add_two (n : ℕ) (x : ℝ) : (n + 2) * (legendre (n + 2)).eval x =
    (2 * n + 3) * x * (legendre (n + 1)).eval x - (n + 1) * (legendre n).eval x := by
  simpa using congrArg (eval x) (legendre_add_two n)

/-- `P₂ = (3X² - 1) / 2`. -/
theorem legendre_two : legendre 2 = C 2⁻¹ * (3 * X ^ 2 - 1) := by
  refine funext fun x => ?_
  have h := legendre_eval_add_two 0 x
  norm_num at h
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_one, eval_ofNat]
  linear_combination h / 2

/-- `P₃ = (5X³ - 3X) / 2`. -/
theorem legendre_three : legendre 3 = C 2⁻¹ * (5 * X ^ 3 - 3 * X) := by
  refine funext fun x => ?_
  have h := legendre_eval_add_two 1 x
  norm_num [legendre_two] at h
  simp only [eval_mul, eval_C, eval_sub, eval_pow, eval_X, eval_ofNat]
  linear_combination h / 3

/-- Every Legendre polynomial takes the value `1` at `1`. -/
@[simp] theorem legendre_eval_one (n : ℕ) : (legendre n).eval 1 = 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    have h := legendre_eval_add_two n 1
    rw [h₀, h₁] at h
    exact mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) (by linear_combination h)

/-- **Parity** of the Legendre polynomials: `Pₙ (-X) = (-1)ⁿ Pₙ`. -/
theorem legendre_comp_neg_X (n : ℕ) : (legendre n).comp (-X) = (-1) ^ n * legendre n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n h₀ h₁ =>
    have hne : (n + 2 : ℝ[X]) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    refine mul_left_cancel₀ hne ?_
    have h := congrArg (·.comp (-X)) (legendre_add_two n)
    simp only [mul_comp, sub_comp, add_comp, natCast_comp, ofNat_comp, one_comp, X_comp, h₀, h₁,
      Nat.cast_ofNat] at h
    linear_combination h - (-1) ^ n * legendre_add_two n

/-- Parity of the Legendre polynomials, evaluated at a point. -/
theorem legendre_eval_neg (n : ℕ) (x : ℝ) :
    (legendre n).eval (-x) = (-1) ^ n * (legendre n).eval x := by
  simpa using congrArg (eval x) (legendre_comp_neg_X n)

/-- `Pₙ (-1) = (-1)ⁿ`. -/
@[simp] theorem legendre_eval_neg_one (n : ℕ) : (legendre n).eval (-1) = (-1) ^ n := by
  simp [legendre_eval_neg]

/-- Bonnet's recurrence read off on coefficients. -/
private theorem coeff_legendre_add_two (n k : ℕ) :
    (n + 2) * (legendre (n + 2)).coeff (k + 1) =
      (2 * n + 3) * (legendre (n + 1)).coeff k - (n + 1) * (legendre n).coeff (k + 1) := by
  have h := congrArg (coeff · (k + 1)) (legendre_add_two n)
  simpa [add_mul, sub_mul, mul_assoc, coeff_X_mul] using h

/-- `Pₙ` has no coefficient above degree `n`. -/
theorem coeff_legendre_of_lt {n k : ℕ} (h : n < k) : (legendre n).coeff k = 0 := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simp [coeff_one, h.ne']
  | one => simp [coeff_X, h.ne]
  | more n h₀ h₁ =>
    obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h' := coeff_legendre_add_two n k
    rw [h₀ (by omega), h₁ (by omega)] at h'
    exact (mul_eq_zero.mp (h'.trans (by ring))).resolve_left (by positivity)

/-- The coefficient of `Xⁿ` in `Pₙ`, which is its leading coefficient, is `(2n choose n) / 2ⁿ`. -/
theorem coeff_legendre_self (n : ℕ) : (legendre n).coeff n = n.centralBinom / 2 ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [Nat.centralBinom]
  | more n _ h₁ =>
    have h := coeff_legendre_add_two n (n + 1)
    rw [h₁, coeff_legendre_of_lt (n := n) (k := n + 1 + 1) (by omega)] at h
    have hc : ((n + 2 : ℕ) : ℝ) * (n + 2).centralBinom = 2 * (2 * (n + 1 : ℕ) + 1) *
        (n + 1).centralBinom := by exact_mod_cast Nat.succ_mul_centralBinom_succ (n + 1)
    push_cast at hc
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    rw [h, mul_zero, sub_zero, ← mul_div_assoc, ← mul_div_assoc, hc, pow_succ _ (n + 1)]
    field_simp
    ring

private theorem coeff_legendre_self_ne_zero (n : ℕ) : (legendre n).coeff n ≠ 0 := by
  rw [coeff_legendre_self]
  exact div_ne_zero (by exact_mod_cast n.centralBinom_ne_zero) (by positivity)

/-- No Legendre polynomial vanishes. -/
theorem legendre_ne_zero (n : ℕ) : legendre n ≠ 0 := fun h =>
  coeff_legendre_self_ne_zero n (by rw [h, coeff_zero])

/-- `Pₙ` has degree exactly `n`. -/
@[simp] theorem natDegree_legendre (n : ℕ) : (legendre n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero
    (natDegree_le_iff_coeff_eq_zero.mpr fun _ h => coeff_legendre_of_lt (by exact_mod_cast h))
    (coeff_legendre_self_ne_zero n)

/-- `Pₙ` has degree exactly `n`. -/
@[simp] theorem degree_legendre (n : ℕ) : (legendre n).degree = n :=
  (degree_eq_iff_natDegree_eq (legendre_ne_zero n)).mpr (natDegree_legendre n)

/-- The leading coefficient of `Pₙ` is `(2n choose n) / 2ⁿ`. -/
@[simp] theorem leadingCoeff_legendre (n : ℕ) :
    (legendre n).leadingCoeff = n.centralBinom / 2 ^ n := by
  rw [leadingCoeff, natDegree_legendre, coeff_legendre_self]

/-- One rung of the derivative ladder: the lowering relation at `n` gives the raising relation at
`n + 1`, through the derivative of Bonnet's recurrence. -/
private theorem derivative_legendre_add_two_of {n : ℕ}
    (h : X * derivative (legendre (n + 1)) =
      derivative (legendre n) + (n + 1 : ℝ[X]) * legendre (n + 1)) :
    derivative (legendre (n + 2)) =
      X * derivative (legendre (n + 1)) + (n + 2 : ℝ[X]) * legendre (n + 1) := by
  have hd := congrArg derivative (legendre_add_two n)
  simp only [derivative_mul, derivative_add, derivative_sub, derivative_natCast, derivative_ofNat,
    derivative_X, derivative_one, mul_zero, add_zero, zero_add, zero_mul, mul_one] at hd
  have hne : (n + 2 : ℝ[X]) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  refine mul_left_cancel₀ hne ?_
  linear_combination hd + (n + 1) * h

private theorem derivative_legendre_ladder (n : ℕ) :
    X * derivative (legendre (n + 1)) =
        derivative (legendre n) + (n + 1 : ℝ[X]) * legendre (n + 1) ∧
      (1 - X ^ 2) * derivative (legendre (n + 1)) =
        (n + 1 : ℝ[X]) * (legendre n - X * legendre (n + 1)) := by
  induction n with
  | zero => constructor <;> simp [sq]
  | succ n ih =>
    have hb := derivative_legendre_add_two_of ih.1
    have hr := legendre_add_two n
    push_cast
    constructor
    · linear_combination X * hb - ih.2 - hr
    · linear_combination (1 - X ^ 2) * hb + X * ih.2 + X * hr

/-- The raising relation `P'ₙ₊₁ = X P'ₙ + (n + 1) Pₙ`. -/
theorem derivative_legendre_succ (n : ℕ) :
    derivative (legendre (n + 1)) = X * derivative (legendre n) + (n + 1 : ℝ[X]) * legendre n := by
  cases n with
  | zero => simp
  | succ n =>
    convert derivative_legendre_add_two_of (derivative_legendre_ladder n).1 using 3
    push_cast
    ring

/-- The lowering relation `X P'ₙ₊₁ = P'ₙ + (n + 1) Pₙ₊₁`. -/
theorem X_mul_derivative_legendre_succ (n : ℕ) :
    X * derivative (legendre (n + 1)) =
      derivative (legendre n) + (n + 1 : ℝ[X]) * legendre (n + 1) :=
  (derivative_legendre_ladder n).1

/-- The relation `(1 - X²) P'ₙ₊₁ = (n + 1) (Pₙ - X Pₙ₊₁)`, which expresses the derivative through
the family itself. -/
theorem one_sub_X_sq_mul_derivative_legendre_succ (n : ℕ) :
    (1 - X ^ 2) * derivative (legendre (n + 1)) =
      (n + 1 : ℝ[X]) * (legendre n - X * legendre (n + 1)) :=
  (derivative_legendre_ladder n).2

/-- **Legendre's differential equation** in Sturm–Liouville form:
`((1 - X²) P'ₙ)' = -n (n + 1) Pₙ`. -/
theorem derivative_one_sub_X_sq_mul_derivative_legendre (n : ℕ) :
    derivative ((1 - X ^ 2) * derivative (legendre n)) =
      -((n : ℝ[X]) * ((n : ℝ[X]) + 1)) * legendre n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [one_sub_X_sq_mul_derivative_legendre_succ]
    simp only [derivative_mul, derivative_sub, derivative_add, derivative_natCast, derivative_one,
      derivative_X, zero_mul, zero_add, one_mul]
    push_cast
    linear_combination -(n + 1 : ℝ[X]) * X_mul_derivative_legendre_succ n

section Orthogonality

open MeasureTheory intervalIntegral

/-- **Orthogonality of the Legendre polynomials** on `[-1, 1]`: distinct members are orthogonal
with respect to Lebesgue measure. -/
theorem integral_legendre_mul_legendre_of_ne {m n : ℕ} (h : m ≠ n) :
    ∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x = 0 := by
  have hs := integral_derivative_one_sub_X_sq_mul_derivative_mul (legendre m) (legendre n)
  have e : ∀ (k : ℕ) (p q : ℝ[X]) (x : ℝ), eval x (-((k : ℝ[X]) * (k + 1)) * p * q) =
      -((k : ℝ) * (k + 1)) * (eval x p * eval x q) := fun k p q x => by simp; ring
  rw [derivative_one_sub_X_sq_mul_derivative_legendre,
    derivative_one_sub_X_sq_mul_derivative_legendre, mul_comm (legendre m)] at hs
  simp_rw [e, mul_comm (eval _ (legendre n)), intervalIntegral.integral_const_mul] at hs
  have hmn : (m : ℝ) * (m + 1) ≠ n * (n + 1) := by
    intro he
    have : m * (m + 1) = n * (n + 1) := by exact_mod_cast he
    rcases Nat.lt_or_gt_of_ne h with hlt | hlt
    · exact (Nat.mul_lt_mul'' hlt (Nat.succ_lt_succ hlt)).ne this
    · exact (Nat.mul_lt_mul'' hlt (Nat.succ_lt_succ hlt)).ne' this
  exact (mul_eq_zero.mp (by linear_combination hs : ((n : ℝ) * (n + 1) - m * (m + 1)) *
    ∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x = 0)).resolve_left
    (sub_ne_zero.mpr hmn.symm)

/-- Bonnet's recurrence for `Pₙ₊₂`, paired with a polynomial `q` on `[-1, 1]`. -/
private theorem integral_legendre_add_two_mul (n : ℕ) (q : ℝ[X]) :
    (n + 2) * ∫ x in (-1 : ℝ)..1, (legendre (n + 2)).eval x * q.eval x =
      (2 * n + 3) * (∫ x in (-1 : ℝ)..1, x * (legendre (n + 1)).eval x * q.eval x) -
        (n + 1) * ∫ x in (-1 : ℝ)..1, (legendre n).eval x * q.eval x := by
  simp_rw [← intervalIntegral.integral_const_mul]
  rw [← integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  exact integral_congr fun x _ => by
    linear_combination q.eval x * legendre_eval_add_two n x

/-- **Normalisation of the Legendre polynomials**: `∫₋₁¹ Pₙ² = 2 / (2n + 1)`. -/
theorem integral_legendre_mul_self (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre n).eval x * (legendre n).eval x = 2 / (2 * n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp [← sq, integral_pow]; norm_num
  | more n _ h₁ =>
    -- pair the recurrence for `Pₙ₊₂` with `Pₙ₊₂`, and the one for `Pₙ₊₃` with `Pₙ₊₁`;
    -- both produce the mixed integral `K = ∫ x Pₙ₊₁ Pₙ₊₂`
    have hA := integral_legendre_add_two_mul n (legendre (n + 2))
    have hB := integral_legendre_add_two_mul (n + 1) (legendre (n + 1))
    rw [integral_legendre_mul_legendre_of_ne (by omega : n ≠ n + 2), mul_zero, sub_zero] at hA
    rw [integral_legendre_mul_legendre_of_ne (by omega : n + 1 + 2 ≠ n + 1), h₁, mul_zero] at hB
    have hK : ∫ x in (-1 : ℝ)..1, x * (legendre (n + 1 + 1)).eval x * (legendre (n + 1)).eval x =
        ∫ x in (-1 : ℝ)..1, x * (legendre (n + 1)).eval x * (legendre (n + 2)).eval x :=
      integral_congr fun x _ => by ring
    rw [hK] at hB
    set K := ∫ x in (-1 : ℝ)..1, x * (legendre (n + 1)).eval x * (legendre (n + 2)).eval x
    have h3 : (2 * n + 3 : ℝ) * (2 / (2 * n + 3)) = 2 := by field_simp
    push_cast at hB ⊢
    rw [eq_div_iff (by positivity)]
    refine mul_left_cancel₀ (by positivity : (n + 2 : ℝ) ≠ 0) ?_
    linear_combination (2 * n + 5) * hA - (2 * n + 3) * hB + (n + 2) * h3

/-- **The Legendre orthogonality relation**:
`∫₋₁¹ Pₘ Pₙ = if m = n then 2 / (2n + 1) else 0`. -/
theorem integral_legendre_mul_legendre (m n : ℕ) :
    ∫ x in (-1 : ℝ)..1, (legendre m).eval x * (legendre n).eval x =
      if m = n then (2 / (2 * n + 1) : ℝ) else 0 := by
  split_ifs with h
  · subst h
    exact integral_legendre_mul_self m
  · exact integral_legendre_mul_legendre_of_ne h

end Orthogonality

end Polynomial

end EpsilonEridani
