/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Gegenbauer polynomials of index `3/2`

The Gegenbauer (ultraspherical) polynomials `C_n^{(λ)}` of index `λ` are the orthogonal
polynomials on `[-1, 1]` for the weight `(1 - x²)^{λ - 1/2}`. This file defines the family of
index `λ = 3/2`, whose weight is `1 - x²`, by the three-term recurrence

  `C₀ = 1`,  `C₁ = 3 X`,  `(n + 2) C_{n+2} = (2n + 5) X C_{n+1} - (n + 3) C_n`,

which is the specialisation to `λ = 3/2` of
`(n + 1) C_{n+1}^{(λ)} = 2 (n + λ) X C_n^{(λ)} - (n + 2λ - 1) C_{n-1}^{(λ)}`
(Szegő, (4.7.17); DLMF 18.9.1).

The index-`3/2` family is the one that diagonalises the evolution kernel of the leading-twist
light-cone distribution amplitude of a pseudoscalar meson: such an amplitude is expanded as
`6 u (1 - u) ∑ₙ aₙ C_n^{(3/2)}(2u - 1)` in the light-cone fraction `u`. The basic algebraic
properties proved here, the degree, the leading coefficient, the parity and the endpoint values,
are the input of the weighted-`L²` theory of the family.

The index is fixed at `3/2` rather than carried as a parameter: the weighted-`L²` theory built on
this family uses the weight `1 - x²` of this index only. The polynomials are defined over any field
`R`, the recurrence dividing by `n + 2`; the parity statements and the degree bound hold there,
while the recurrence in division-free form, the exact degree, the leading coefficient and the
endpoint value assume that `R` has characteristic zero. The real family is
`gegenbauerThreeHalves ℝ`.

## Main definitions

* `EpsilonEridani.gegenbauerThreeHalves R n`: the Gegenbauer polynomial `C_n^{(3/2)}` in `R[X]`.

## Main statements

* `EpsilonEridani.C_mul_gegenbauerThreeHalves_add_two`: the division-free three-term recurrence.
* `EpsilonEridani.natDegree_gegenbauerThreeHalves`: `C_n^{(3/2)}` has degree `n`.
* `EpsilonEridani.leadingCoeff_gegenbauerThreeHalves`: its leading coefficient is `(2n + 1)‼ / n!`.
* `EpsilonEridani.gegenbauerThreeHalves_comp_neg_X`: the parity
  `C_n^{(3/2)}(-X) = (-1)ⁿ C_n^{(3/2)}(X)`.
* `EpsilonEridani.coeff_gegenbauerThreeHalves_eq_zero_of_odd`: `C_n^{(3/2)}` has only monomials of
  the parity of `n`.
* `EpsilonEridani.gegenbauerThreeHalves_eval_one`: the endpoint value
  `C_n^{(3/2)}(1) = (n + 2).choose 2`.

## References

* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, 4th edition (1975),
  chapter IV, §4.7.
* NIST Digital Library of Mathematical Functions, §18.3, §18.6 and §18.9.
-/

public section

namespace EpsilonEridani

open Polynomial
open scoped Nat

variable (R : Type*) [Field R]

/-- The `n`-th Gegenbauer polynomial `C_n^{(3/2)}` of index `3/2`, defined by the
three-term recurrence `C₀ = 1`, `C₁ = 3 X` and
`C_{n+2} = ((2n + 5) X C_{n+1} - (n + 3) C_n) / (n + 2)`. -/
noncomputable def gegenbauerThreeHalves : ℕ → R[X]
  | 0 => 1
  | 1 => C 3 * X
  | n + 2 => C ((n : R) + 2)⁻¹ * (C (2 * (n : R) + 5) * X * gegenbauerThreeHalves (n + 1) -
      C ((n : R) + 3) * gegenbauerThreeHalves n)

/-- `C_0^{(3/2)} = 1`. -/
@[simp]
theorem gegenbauerThreeHalves_zero : gegenbauerThreeHalves R 0 = 1 := by
  simp [gegenbauerThreeHalves]

/-- `C_1^{(3/2)} = 3 X`. -/
@[simp]
theorem gegenbauerThreeHalves_one : gegenbauerThreeHalves R 1 = C 3 * X := by
  simp [gegenbauerThreeHalves]

/-- The defining recurrence `C_{n+2} = ((2n + 5) X C_{n+1} - (n + 3) C_n) / (n + 2)`. -/
theorem gegenbauerThreeHalves_add_two (n : ℕ) :
    gegenbauerThreeHalves R (n + 2) = C ((n : R) + 2)⁻¹ *
      (C (2 * (n : R) + 5) * X * gegenbauerThreeHalves R (n + 1) -
        C ((n : R) + 3) * gegenbauerThreeHalves R n) := by
  rw [gegenbauerThreeHalves]

/-! ### Parity -/

/-- The parity of the index-`3/2` Gegenbauer polynomials:
`C_n^{(3/2)}(-X) = (-1)ⁿ C_n^{(3/2)}(X)`. -/
@[simp]
theorem gegenbauerThreeHalves_comp_neg_X :
    ∀ n : ℕ, (gegenbauerThreeHalves R n).comp (-X) = (-1) ^ n * gegenbauerThreeHalves R n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by
    rw [gegenbauerThreeHalves_add_two]
    simp only [mul_comp, sub_comp, C_comp, X_comp, gegenbauerThreeHalves_comp_neg_X n,
      gegenbauerThreeHalves_comp_neg_X (n + 1)]
    ring

/-- The parity of `C_n^{(3/2)}` at a point: `C_n^{(3/2)}(-x) = (-1)ⁿ C_n^{(3/2)}(x)`. -/
@[simp]
theorem gegenbauerThreeHalves_eval_neg (n : ℕ) (x : R) :
    (gegenbauerThreeHalves R n).eval (-x) = (-1) ^ n * (gegenbauerThreeHalves R n).eval x := by
  simpa [eval_comp, -gegenbauerThreeHalves_comp_neg_X] using
    congrArg (eval x) (gegenbauerThreeHalves_comp_neg_X R n)

/-- `C_n^{(3/2)}` contains only monomials `Xᵏ` with `k ≡ n (mod 2)`. -/
theorem coeff_gegenbauerThreeHalves_eq_zero_of_odd :
    ∀ {n k : ℕ}, Odd (n + k) → (gegenbauerThreeHalves R n).coeff k = 0
  | 0, k, ⟨m, hm⟩ => by
    simp [coeff_one]
    omega
  | 1, k, ⟨m, hm⟩ => by
    simp [coeff_X]
    omega
  | n + 2, 0, h => by
    have h₀ := coeff_gegenbauerThreeHalves_eq_zero_of_odd (n := n) (k := 0) (by grind)
    simp [gegenbauerThreeHalves_add_two, mul_assoc, h₀]
  | n + 2, k + 1, h => by
    have h₁ := coeff_gegenbauerThreeHalves_eq_zero_of_odd (n := n + 1) (k := k) (by grind)
    have h₀ := coeff_gegenbauerThreeHalves_eq_zero_of_odd (n := n) (k := k + 1) (by grind)
    simp only [gegenbauerThreeHalves_add_two, coeff_C_mul, coeff_sub, mul_assoc, coeff_X_mul, h₀,
      h₁, mul_zero, sub_zero]

/-! ### Degree -/

/-- `C_n^{(3/2)}` has degree at most `n`. -/
theorem natDegree_gegenbauerThreeHalves_le : ∀ n : ℕ, (gegenbauerThreeHalves R n).natDegree ≤ n
  | 0 => by simp
  | 1 => by simpa using natDegree_C_mul_le (3 : R) X
  | n + 2 => by
    rw [gegenbauerThreeHalves_add_two]
    refine (natDegree_C_mul_le _ _).trans <| (natDegree_sub_le _ _).trans <| max_le ?_ ?_
    · rw [mul_assoc]
      refine (natDegree_C_mul_le _ _).trans <| natDegree_mul_le.trans ?_
      have := natDegree_gegenbauerThreeHalves_le (n + 1)
      have := natDegree_X_le (R := R)
      omega
    · exact (natDegree_C_mul_le _ _).trans <|
        (natDegree_gegenbauerThreeHalves_le n).trans (by omega)

variable [CharZero R]

/-- The three-term recurrence of the index-`3/2` Gegenbauer polynomials, in division-free form:
`(n + 2) C_{n+2} = (2n + 5) X C_{n+1} - (n + 3) C_n`. -/
theorem C_mul_gegenbauerThreeHalves_add_two (n : ℕ) :
    C ((n : R) + 2) * gegenbauerThreeHalves R (n + 2) =
      C (2 * (n : R) + 5) * X * gegenbauerThreeHalves R (n + 1) -
        C ((n : R) + 3) * gegenbauerThreeHalves R n := by
  have h : (n : R) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  simp only [gegenbauerThreeHalves_add_two, ← mul_assoc, ← C_mul, mul_inv_cancel₀ h, C_1, one_mul]

/-! ### Endpoint values -/

/-- The value of `C_n^{(3/2)}` at `1` is `(n + 2).choose 2 = (n + 1)(n + 2) / 2`. -/
@[simp]
theorem gegenbauerThreeHalves_eval_one :
    ∀ n : ℕ, (gegenbauerThreeHalves R n).eval 1 = ((n + 2).choose 2 : ℕ)
  | 0 => by simp
  | 1 => by norm_num
  | n + 2 => by
    have h : (n : R) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    rw [gegenbauerThreeHalves_add_two]
    simp only [eval_mul, eval_sub, eval_C, eval_X, gegenbauerThreeHalves_eval_one n,
      gegenbauerThreeHalves_eval_one (n + 1)]
    have : NeZero (2 : R) := ⟨by norm_num⟩
    rw [Nat.cast_choose_two R, Nat.cast_choose_two R, Nat.cast_choose_two R]
    push_cast
    field_simp
    ring

/-! ### Leading coefficient and exact degree -/

/-- The coefficient of `Xⁿ` in `C_n^{(3/2)}` is `(2n + 1)‼ / n!`. -/
theorem coeff_gegenbauerThreeHalves_self : ∀ n : ℕ,
    (gegenbauerThreeHalves R n).coeff n = ((2 * n + 1)‼ : ℕ) / (n ! : ℕ)
  | 0 => by simp
  | 1 => by norm_num [Nat.doubleFactorial]
  | n + 2 => by
    have h : (n : R) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hn : (gegenbauerThreeHalves R n).coeff (n + 2) = 0 :=
      coeff_eq_zero_of_natDegree_lt
        ((natDegree_gegenbauerThreeHalves_le R n).trans_lt (by omega))
    have hf : ((n + 1)! : R) ≠ 0 := by exact_mod_cast (n + 1).factorial_ne_zero
    simp only [gegenbauerThreeHalves_add_two, coeff_C_mul, coeff_sub, mul_assoc, coeff_X_mul, hn,
      coeff_gegenbauerThreeHalves_self (n + 1), mul_add, Nat.doubleFactorial_add_two,
      Nat.factorial_succ (n + 1)]
    push_cast [add_assoc, one_add_one_eq_two]
    field_simp
    ring

/-- The leading coefficient `(2n + 1)‼ / n!` of `C_n^{(3/2)}` is nonzero. -/
theorem coeff_gegenbauerThreeHalves_self_ne_zero (n : ℕ) :
    (gegenbauerThreeHalves R n).coeff n ≠ 0 := by
  rw [coeff_gegenbauerThreeHalves_self]
  exact div_ne_zero (by exact_mod_cast (Nat.doubleFactorial_pos _).ne')
    (by exact_mod_cast (Nat.factorial_pos _).ne')

/-- `C_n^{(3/2)}` has degree exactly `n`. -/
@[simp]
theorem natDegree_gegenbauerThreeHalves (n : ℕ) : (gegenbauerThreeHalves R n).natDegree = n :=
  natDegree_eq_of_le_of_coeff_ne_zero (natDegree_gegenbauerThreeHalves_le R n)
    (coeff_gegenbauerThreeHalves_self_ne_zero R n)

/-- `C_n^{(3/2)}` is a nonzero polynomial. -/
theorem gegenbauerThreeHalves_ne_zero (n : ℕ) : gegenbauerThreeHalves R n ≠ 0 := by
  intro h
  simpa [h] using coeff_gegenbauerThreeHalves_self_ne_zero R n

/-- `C_n^{(3/2)}` has degree exactly `n`, as a `WithBot ℕ`. -/
@[simp]
theorem degree_gegenbauerThreeHalves (n : ℕ) : (gegenbauerThreeHalves R n).degree = n := by
  rw [degree_eq_natDegree (gegenbauerThreeHalves_ne_zero R n), natDegree_gegenbauerThreeHalves]

/-- The leading coefficient of `C_n^{(3/2)}` is `(2n + 1)‼ / n!`. -/
@[simp]
theorem leadingCoeff_gegenbauerThreeHalves (n : ℕ) :
    (gegenbauerThreeHalves R n).leadingCoeff = ((2 * n + 1)‼ : ℕ) / (n ! : ℕ) := by
  rw [leadingCoeff, natDegree_gegenbauerThreeHalves, coeff_gegenbauerThreeHalves_self]

end EpsilonEridani
