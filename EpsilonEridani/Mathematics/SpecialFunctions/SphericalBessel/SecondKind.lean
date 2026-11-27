/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic

/-!
# Spherical Bessel functions of the second kind

The spherical Bessel function of the second kind of order `l`, `y_l`, is the solution of the
spherical Bessel equation `x ^ 2 y'' + 2 x y' + (x ^ 2 - l (l + 1)) y = 0` that starts from
`y_0(x) = -cos x / x` and obeys the same three-term recurrence in the order as the first-kind
family `j_l` of `EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`:

  `y_{l + 2}(x) = (2 l + 3) / x * y_{l + 1}(x) - y_l(x)`.

Unlike `j_l`, `y_l` is singular at the origin, where it diverges like `x ^ (-(l + 1))`. The
definition therefore splits off that power: `x ^ (l + 1) y_l(x)` is the function
`sphericalBesselYMulPow l`, defined on the whole line by the recurrence
`G_{l + 2} = (2 l + 3) G_{l + 1} - x ^ 2 G_l` from `G_0 = -cos x` and `G_1 = -cos x - x sin x`,
which involves no division. It is real analytic and even, its value at the origin is
`-(2 l - 1)‼`, and its derivative obeys `G_{l + 1}' = x G_l`, the counterpart of the Rayleigh step
of `sphericalBesselJDivPow`. Then `y_l(x) = G_l(x) / x ^ (l + 1)`. At `x = 0` this is Lean's
junk value `0` (`sphericalBesselY_apply_zero`); every statement about `y_l` that is not a pure
algebraic identity carries the hypothesis `x ≠ 0`.

Mathlib has no Bessel function of the second kind, and its `Complex.besselJ` is of the first kind
only.

## Main definitions

* `EpsilonEridani.sphericalBesselY l x`: the spherical Bessel function `y_l(x)`, for `x ≠ 0`.
* `EpsilonEridani.sphericalBesselYMulPow l x`: the even analytic factor `x ^ (l + 1) y_l(x)`
  (`sphericalBesselYMulPow_eq_mul_of_ne_zero`), defined on the whole line.

## Main statements

* `sphericalBesselY_zero` and `sphericalBesselY_one`: the closed forms
  `y_0(x) = -cos x / x` and `y_1(x) = -cos x / x ^ 2 - sin x / x`.
* `mul_sphericalBesselY_add_two` and `sphericalBesselY_add_two_of_ne_zero`: the three-term
  recurrence in the order, the same as that of `j_l`.
* `analyticAt_sphericalBesselYMulPow`, `sphericalBesselYMulPow_neg` and
  `hasDerivAt_sphericalBesselYMulPow_succ`: the factor `x ^ (l + 1) y_l(x)` is analytic and even
  on the whole line, and the derivative of `G_{l + 1}` is `x G_l`.
* `sphericalBesselY_neg`: the parity `y_l(-x) = (-1) ^ (l + 1) y_l(x)`.
* `hasDerivAt_sphericalBesselY_of_ne_zero` and `hasDerivAt_sphericalBesselY_succ'_of_ne_zero`:
  the two derivative relations, which raise and lower the order, the same ladder pair as for
  `j_l`.
* `sphericalBesselY_equation`: `y_l` solves the spherical Bessel equation of order `l` off the
  origin.
* `sphericalBesselYMulPow_apply_zero`, `tendsto_pow_mul_sphericalBesselY_nhdsNE_zero` and
  `tendsto_sphericalBesselY_nhdsGT_zero`: the behaviour at the origin,
  `x ^ (l + 1) y_l(x) → -(2 l - 1)‼`, so that `y_l(x) → -∞` as `x → 0⁺`.
* `sphericalBesselJ_succ_mul_sphericalBesselY_sub_sphericalBesselJ_mul_sphericalBesselY_succ`
  and `wronskian_sphericalBesselJ_sphericalBesselY`: the cross product
  `j_{l + 1} y_l - j_l y_{l + 1} = x⁻²` and the Wronskian `j_l y_l' - j_l' y_l = x⁻²`. The
  Wronskian has no zero, so `j_l` and `y_l` are linearly independent solutions.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §10.1
  (10.1.12, 10.1.19–10.1.22).
* NIST Digital Library of Mathematical Functions, §10.47 (the equation and the parity),
  §10.49(i) (`y_0` and `y_1`), §10.50 (the Wronskian and the cross product), §10.51 (recurrence
  and derivatives) and §10.52(i) (the limiting form at the origin).
-/

public section

open Filter Topology Real
open scoped Nat

namespace EpsilonEridani

/-- The function `x ^ (l + 1) y_l(x)`, the even analytic factor of the spherical Bessel function
of the second kind (`sphericalBesselYMulPow_eq_mul_of_ne_zero`), defined on the whole line by the
recurrence `G_{l + 2} = (2 l + 3) G_{l + 1} - x ^ 2 G_l` from `G_0 = -cos x` and
`G_1 = -cos x - x sin x`. -/
noncomputable def sphericalBesselYMulPow : ℕ → ℝ → ℝ
  | 0, x => -cos x
  | 1, x => -cos x - x * sin x
  | l + 2, x =>
    (2 * l + 3 : ℝ) * sphericalBesselYMulPow (l + 1) x - x ^ 2 * sphericalBesselYMulPow l x

local notation "G" => sphericalBesselYMulPow

/-- `sphericalBesselYMulPow` of order zero is `-cos x`. -/
@[simp]
theorem sphericalBesselYMulPow_zero (x : ℝ) : sphericalBesselYMulPow 0 x = -cos x := by
  rw [sphericalBesselYMulPow]

/-- `sphericalBesselYMulPow` of order one is `-cos x - x sin x`. -/
@[simp]
theorem sphericalBesselYMulPow_one (x : ℝ) :
    sphericalBesselYMulPow 1 x = -cos x - x * sin x := by
  rw [sphericalBesselYMulPow]

/-- The recurrence defining `sphericalBesselYMulPow`:
`G_{l + 2}(x) = (2 l + 3) G_{l + 1}(x) - x ^ 2 G_l(x)`, on the whole line. -/
theorem sphericalBesselYMulPow_add_two (l : ℕ) (x : ℝ) :
    sphericalBesselYMulPow (l + 2) x =
      (2 * l + 3) * sphericalBesselYMulPow (l + 1) x - x ^ 2 * sphericalBesselYMulPow l x := by
  rw [sphericalBesselYMulPow]

/-- Every `sphericalBesselYMulPow l` is real analytic on the whole line. -/
@[fun_prop]
theorem analyticAt_sphericalBesselYMulPow (l : ℕ) (x : ℝ) :
    AnalyticAt ℝ (sphericalBesselYMulPow l) x := by
  induction l using Nat.twoStepInduction generalizing x with
  | zero =>
    have h : G 0 = fun y => -cos y := funext sphericalBesselYMulPow_zero
    rw [h]
    fun_prop
  | one =>
    have h : G 1 = fun y => -cos y - y * sin y := funext sphericalBesselYMulPow_one
    rw [h]
    fun_prop
  | more l ih₀ ih₁ =>
    have h : G (l + 2) = fun y => (2 * l + 3 : ℝ) * G (l + 1) y - y ^ 2 * G l y :=
      funext (sphericalBesselYMulPow_add_two l)
    have h₀ : AnalyticAt ℝ (G l) x := ih₀ x
    have h₁ : AnalyticAt ℝ (G (l + 1)) x := ih₁ x
    rw [h]
    fun_prop

/-- Every `sphericalBesselYMulPow l` is smooth. -/
@[fun_prop]
theorem contDiff_sphericalBesselYMulPow (l : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (sphericalBesselYMulPow l) :=
  AnalyticOnNhd.contDiff fun x _ => analyticAt_sphericalBesselYMulPow l x

/-- Every `sphericalBesselYMulPow l` is differentiable. -/
@[fun_prop]
theorem differentiable_sphericalBesselYMulPow (l : ℕ) :
    Differentiable ℝ (sphericalBesselYMulPow l) :=
  fun x => (analyticAt_sphericalBesselYMulPow l x).differentiableAt

/-- Every `sphericalBesselYMulPow l` is continuous. -/
@[fun_prop]
theorem continuous_sphericalBesselYMulPow (l : ℕ) : Continuous (sphericalBesselYMulPow l) :=
  (differentiable_sphericalBesselYMulPow l).continuous

/-- Every `sphericalBesselYMulPow l` is even. -/
@[simp]
theorem sphericalBesselYMulPow_neg (l : ℕ) (x : ℝ) :
    sphericalBesselYMulPow l (-x) = sphericalBesselYMulPow l x := by
  induction l using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more l ih₀ ih₁ => simp [sphericalBesselYMulPow_add_two, ih₀, ih₁]

/-- The value of `sphericalBesselYMulPow l` at the origin, `-(2 l - 1)‼`, the limiting value of
`x ^ (l + 1) y_l(x)` as `x → 0` (`tendsto_pow_mul_sphericalBesselY_nhdsNE_zero`). At `l = 0` the
truncated subtraction gives `0‼ = 1`. -/
@[simp]
theorem sphericalBesselYMulPow_apply_zero (l : ℕ) :
    sphericalBesselYMulPow l 0 = -(((2 * l - 1)‼ : ℕ) : ℝ) := by
  induction l using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more l _ ih₁ =>
    have hl : 2 * (l + 2) - 1 = 2 * (l + 1) - 1 + 2 := by omega
    have hl' : ((2 * (l + 1) - 1 : ℕ) : ℝ) = 2 * l + 1 := by
      rw [show 2 * (l + 1) - 1 = 2 * l + 1 by omega]
      push_cast
      ring
    rw [sphericalBesselYMulPow_add_two, ih₁, hl, Nat.doubleFactorial_add_two, Nat.cast_mul,
      Nat.cast_add, hl']
    push_cast
    ring

/-- The derivative of `sphericalBesselYMulPow 0 = -cos` is `sin`. -/
theorem hasDerivAt_sphericalBesselYMulPow_zero (x : ℝ) :
    HasDerivAt (sphericalBesselYMulPow 0) (sin x) x := by
  have h : G 0 = fun y => -cos y := funext sphericalBesselYMulPow_zero
  rw [h]
  simpa only [Pi.neg_def, neg_neg] using (hasDerivAt_cos x).neg

/-- The derivative of `sphericalBesselYMulPow 0 = -cos` is `sin`. -/
@[simp, grind =]
theorem deriv_sphericalBesselYMulPow_zero (x : ℝ) :
    deriv (sphericalBesselYMulPow 0) x = sin x :=
  (hasDerivAt_sphericalBesselYMulPow_zero x).deriv

/-- The order-zero case of `hasDerivAt_sphericalBesselYMulPow_succ`: `G_1' = x G_0`. -/
private lemma hasDerivAt_sphericalBesselYMulPow_one (x : ℝ) :
    HasDerivAt (G 1) (x * G 0 x) x := by
  have h : G 1 = fun y => -cos y - y * sin y := funext sphericalBesselYMulPow_one
  rw [h]
  refine ((hasDerivAt_cos x).neg.sub ((hasDerivAt_id' x).mul (hasDerivAt_sin x))).congr_deriv ?_
  simp only [sphericalBesselYMulPow_zero]
  ring

/-- The counterpart of the Rayleigh step, on the whole line: the derivative of
`sphericalBesselYMulPow (l + 1)` is `x` times `sphericalBesselYMulPow l`. For `x ≠ 0` it is the
lowering relation `y_{l + 1}' = y_l - (l + 2) / x * y_{l + 1}`
(`hasDerivAt_sphericalBesselY_succ'_of_ne_zero`). -/
theorem hasDerivAt_sphericalBesselYMulPow_succ (l : ℕ) (x : ℝ) :
    HasDerivAt (sphericalBesselYMulPow (l + 1)) (x * sphericalBesselYMulPow l x) x := by
  induction l using Nat.twoStepInduction generalizing x with
  | zero => exact hasDerivAt_sphericalBesselYMulPow_one x
  | one =>
    have h : G 2 = fun y => (2 * ((0 : ℕ) : ℝ) + 3) * G 1 y - y ^ 2 * G 0 y :=
      funext (sphericalBesselYMulPow_add_two 0)
    rw [h]
    refine (((hasDerivAt_sphericalBesselYMulPow_one x).const_mul _).sub
      ((hasDerivAt_pow 2 x).mul (hasDerivAt_sphericalBesselYMulPow_zero x))).congr_deriv ?_
    simp only [sphericalBesselYMulPow_zero, sphericalBesselYMulPow_one]
    push_cast
    ring
  | more l ih₀ ih₁ =>
    have h : G (l + 3) = fun y => (2 * ((l + 1 : ℕ) : ℝ) + 3) * G (l + 2) y - y ^ 2 * G (l + 1) y :=
      funext (sphericalBesselYMulPow_add_two (l + 1))
    rw [h]
    refine (((ih₁ x).const_mul _).sub ((hasDerivAt_pow 2 x).mul (ih₀ x))).congr_deriv ?_
    rw [sphericalBesselYMulPow_add_two l x]
    push_cast
    ring

/-- The derivative of `sphericalBesselYMulPow (l + 1)` is `x` times `sphericalBesselYMulPow l`,
on the whole line. -/
@[simp, grind =]
theorem deriv_sphericalBesselYMulPow_succ (l : ℕ) (x : ℝ) :
    deriv (sphericalBesselYMulPow (l + 1)) x = x * sphericalBesselYMulPow l x :=
  (hasDerivAt_sphericalBesselYMulPow_succ l x).deriv

/-! ### The spherical Bessel functions of the second kind -/

/-- The spherical Bessel function of the second kind of order `l`,
`y_l(x) = sphericalBesselYMulPow l x / x ^ (l + 1)` (`sphericalBesselY_def`). It is meaningful for
`x ≠ 0`; at `x = 0`, where `y_l` diverges (`tendsto_sphericalBesselY_nhdsGT_zero`), the division
returns Lean's junk value `0`. -/
noncomputable def sphericalBesselY (l : ℕ) (x : ℝ) : ℝ := sphericalBesselYMulPow l x / x ^ (l + 1)

/-- The spherical Bessel function `y_l(x)` is `sphericalBesselYMulPow l x` divided by
`x ^ (l + 1)`. -/
theorem sphericalBesselY_def (l : ℕ) (x : ℝ) :
    sphericalBesselY l x = sphericalBesselYMulPow l x / x ^ (l + 1) :=
  (rfl)

/-- The value at the origin is Lean's junk value `0`, where `y_l` itself diverges
(`tendsto_sphericalBesselY_nhdsGT_zero`). -/
@[simp]
theorem sphericalBesselY_apply_zero (l : ℕ) : sphericalBesselY l 0 = 0 := by
  rw [sphericalBesselY_def, zero_pow (Nat.succ_ne_zero l), div_zero]

/-- For `x ≠ 0`, the even analytic factor `sphericalBesselYMulPow l x` is `x ^ (l + 1) y_l(x)`. -/
theorem sphericalBesselYMulPow_eq_mul_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    sphericalBesselYMulPow l x = x ^ (l + 1) * sphericalBesselY l x := by
  rw [sphericalBesselY_def, mul_div_cancel₀ _ (pow_ne_zero _ hx)]

/-- The order-zero spherical Bessel function of the second kind, `y_0(x) = -cos x / x`. -/
@[simp]
theorem sphericalBesselY_zero (x : ℝ) : sphericalBesselY 0 x = -cos x / x := by
  rw [sphericalBesselY_def, sphericalBesselYMulPow_zero, zero_add, pow_one]

/-- The order-one spherical Bessel function of the second kind,
`y_1(x) = -cos x / x ^ 2 - sin x / x`. -/
@[simp]
theorem sphericalBesselY_one (x : ℝ) :
    sphericalBesselY 1 x = -cos x / x ^ 2 - sin x / x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sphericalBesselY_def, sphericalBesselYMulPow_one]
    field_simp
    ring

/-- Every `y_l` is real analytic off the origin. -/
@[fun_prop]
theorem analyticAt_sphericalBesselY (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    AnalyticAt ℝ (sphericalBesselY l) x :=
  (analyticAt_sphericalBesselYMulPow l x).div (analyticAt_id.pow _) (pow_ne_zero _ hx)

/-- Every `y_l` is smooth off the origin. -/
@[fun_prop]
theorem contDiffAt_sphericalBesselY (l : ℕ) {x : ℝ} {n : WithTop ℕ∞} (hx : x ≠ 0) :
    ContDiffAt ℝ n (sphericalBesselY l) x :=
  (analyticAt_sphericalBesselY l hx).contDiffAt

/-- Every `y_l` is differentiable off the origin. -/
@[fun_prop]
theorem differentiableAt_sphericalBesselY (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    DifferentiableAt ℝ (sphericalBesselY l) x :=
  (analyticAt_sphericalBesselY l hx).differentiableAt

/-- Every `y_l` is continuous off the origin. -/
@[fun_prop]
theorem continuousAt_sphericalBesselY (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    ContinuousAt (sphericalBesselY l) x :=
  (differentiableAt_sphericalBesselY l hx).continuousAt

/-- The parity of the spherical Bessel functions of the second kind:
`y_l(-x) = (-1) ^ (l + 1) y_l(x)`. -/
@[simp]
theorem sphericalBesselY_neg (l : ℕ) (x : ℝ) :
    sphericalBesselY l (-x) = (-1) ^ (l + 1) * sphericalBesselY l x := by
  rw [sphericalBesselY_def, sphericalBesselY_def, sphericalBesselYMulPow_neg, neg_pow]
  rcases neg_one_pow_eq_or ℝ (l + 1) with h | h <;> simp [h, div_neg]

/-- The three-term recurrence in the order:
`x y_{l + 2}(x) = (2 l + 3) y_{l + 1}(x) - x y_l(x)`, the same as that of `j_l`
(`mul_sphericalBesselJ_add_two`). It holds trivially at `x = 0`, where both sides are the junk
value `0`. -/
@[grind =]
theorem mul_sphericalBesselY_add_two (l : ℕ) (x : ℝ) :
    x * sphericalBesselY (l + 2) x =
      (2 * l + 3) * sphericalBesselY (l + 1) x - x * sphericalBesselY l x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · simp only [sphericalBesselY_def, sphericalBesselYMulPow_add_two]
    field_simp
    ring

/-- The three-term recurrence in the order:
`y_{l + 2}(x) = (2 l + 3) / x * y_{l + 1}(x) - y_l(x)` for `x ≠ 0`. -/
theorem sphericalBesselY_add_two_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    sphericalBesselY (l + 2) x =
      (2 * l + 3) / x * sphericalBesselY (l + 1) x - sphericalBesselY l x := by
  field_simp
  linear_combination mul_sphericalBesselY_add_two l x

/-- The derivative relation lowering the order,
`y_{l + 1}' = y_l - (l + 2) / x * y_{l + 1}` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselY_succ'_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (sphericalBesselY (l + 1))
      (sphericalBesselY l x - (l + 2) / x * sphericalBesselY (l + 1) x) x := by
  have h : sphericalBesselY (l + 1) = fun y => G (l + 1) y / y ^ (l + 1 + 1) :=
    funext (sphericalBesselY_def (l + 1))
  rw [h]
  refine ((hasDerivAt_sphericalBesselYMulPow_succ l x).div (hasDerivAt_pow _ x)
    (pow_ne_zero _ hx)).congr_deriv ?_
  simp only [sphericalBesselY_def, Nat.add_sub_cancel]
  field_simp
  push_cast
  ring

/-- The derivative relation raising the order, `y_l' = l / x * y_l - y_{l + 1}` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselY_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (sphericalBesselY l)
      (l / x * sphericalBesselY l x - sphericalBesselY (l + 1) x) x := by
  rcases l with _ | l
  · have h : sphericalBesselY 0 = fun y => G 0 y / y ^ (0 + 1) := funext (sphericalBesselY_def 0)
    rw [h]
    refine ((hasDerivAt_sphericalBesselYMulPow_zero x).div (hasDerivAt_pow _ x)
      (pow_ne_zero _ hx)).congr_deriv ?_
    simp only [Nat.cast_zero, zero_add, sphericalBesselY_one, sphericalBesselYMulPow_zero]
    field_simp
    ring
  · refine (hasDerivAt_sphericalBesselY_succ'_of_ne_zero l hx).congr_deriv ?_
    rw [sphericalBesselY_add_two_of_ne_zero l hx]
    push_cast
    field_simp
    ring

/-- The derivative of `y_l` for `x ≠ 0`, `y_l' = l / x * y_l - y_{l + 1}`. -/
@[grind =]
theorem deriv_sphericalBesselY_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (sphericalBesselY l) x = l / x * sphericalBesselY l x - sphericalBesselY (l + 1) x :=
  (hasDerivAt_sphericalBesselY_of_ne_zero l hx).deriv

/-- The derivative of `y_{l + 1}` for `x ≠ 0`, `y_{l + 1}' = y_l - (l + 2) / x * y_{l + 1}`. -/
@[grind =]
theorem deriv_sphericalBesselY_succ'_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (sphericalBesselY (l + 1)) x =
      sphericalBesselY l x - (l + 2) / x * sphericalBesselY (l + 1) x :=
  (hasDerivAt_sphericalBesselY_succ'_of_ne_zero l hx).deriv

/-- The second derivative of `y_l` for `x ≠ 0`, as a `HasDerivAt` statement:
`y_l'' = -(2 / x) y_l' + (l (l + 1) / x ^ 2 - 1) y_l`. -/
theorem hasDerivAt_deriv_sphericalBesselY_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (deriv (sphericalBesselY l))
      (-(2 / x) * deriv (sphericalBesselY l) x +
        (l * (l + 1) / x ^ 2 - 1) * sphericalBesselY l x) x := by
  -- near `x`, the derivative is given by the raising relation
  have hev : (fun y => (l : ℝ) * y⁻¹ * sphericalBesselY l y - sphericalBesselY (l + 1) y) =ᶠ[𝓝 x]
      deriv (sphericalBesselY l) := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    rw [deriv_sphericalBesselY_of_ne_zero l hy, div_eq_mul_inv]
  refine ((((hasDerivAt_inv hx).const_mul (l : ℝ)).mul
    (hasDerivAt_sphericalBesselY_of_ne_zero l hx)).sub
    (hasDerivAt_sphericalBesselY_succ'_of_ne_zero l hx)).congr_of_eventuallyEq hev.symm
    |>.congr_deriv ?_
  rw [deriv_sphericalBesselY_of_ne_zero l hx]
  field_simp
  ring

/-- The second derivative of `y_l` for `x ≠ 0`:
`y_l'' = -(2 / x) y_l' + (l (l + 1) / x ^ 2 - 1) y_l`. -/
@[grind =]
theorem deriv_deriv_sphericalBesselY_of_ne_zero (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (sphericalBesselY l)) x =
      -(2 / x) * deriv (sphericalBesselY l) x +
        (l * (l + 1) / x ^ 2 - 1) * sphericalBesselY l x :=
  (hasDerivAt_deriv_sphericalBesselY_of_ne_zero l hx).deriv

/-- `y_l` solves the spherical Bessel equation of order `l` off the origin:
`x ^ 2 y_l'' + 2 x y_l' + (x ^ 2 - l (l + 1)) y_l = 0` for `x ≠ 0`. -/
theorem sphericalBesselY_equation (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    x ^ 2 * deriv (deriv (sphericalBesselY l)) x + 2 * x * deriv (sphericalBesselY l) x +
      (x ^ 2 - l * (l + 1)) * sphericalBesselY l x = 0 := by
  rw [deriv_deriv_sphericalBesselY_of_ne_zero l hx]
  field_simp
  ring

/-! ### Behaviour at the origin -/

/-- The leading behaviour at the origin: `x ^ (l + 1) y_l(x) → -(2 l - 1)‼` as `x → 0`, so `y_l`
diverges like `x ^ (-(l + 1))`. -/
theorem tendsto_pow_mul_sphericalBesselY_nhdsNE_zero (l : ℕ) :
    Tendsto (fun x => x ^ (l + 1) * sphericalBesselY l x) (𝓝[≠] 0)
      (𝓝 (-(((2 * l - 1)‼ : ℕ) : ℝ))) := by
  rw [← sphericalBesselYMulPow_apply_zero]
  refine (((continuous_sphericalBesselYMulPow l).tendsto 0).mono_left
    nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact sphericalBesselYMulPow_eq_mul_of_ne_zero l hx

/-- `y_l(x) → -∞` as `x → 0⁺`. -/
theorem tendsto_sphericalBesselY_nhdsGT_zero (l : ℕ) :
    Tendsto (sphericalBesselY l) (𝓝[>] 0) atBot := by
  have hG : Tendsto (G l) (𝓝[>] 0) (𝓝 (G l 0)) :=
    ((continuous_sphericalBesselYMulPow l).tendsto 0).mono_left nhdsWithin_le_nhds
  have hneg : G l 0 < 0 := by
    rw [sphericalBesselYMulPow_apply_zero, neg_lt_zero]
    exact_mod_cast Nat.doubleFactorial_pos _
  have hpow : Tendsto (fun x : ℝ => x⁻¹ ^ (l + 1)) (𝓝[>] 0) atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero l)).comp tendsto_inv_nhdsGT_zero
  refine (hG.neg_mul_atTop hneg hpow).congr fun x => ?_
  rw [sphericalBesselY_def, inv_pow, div_eq_mul_inv]

/-! ### The cross product and the Wronskian -/

/-- The cross product of the two kinds, `j_{l + 1} y_l - j_l y_{l + 1} = x⁻²` for `x ≠ 0`. -/
theorem sphericalBesselJ_succ_mul_sphericalBesselY_sub_sphericalBesselJ_mul_sphericalBesselY_succ
    (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    sphericalBesselJ (l + 1) x * sphericalBesselY l x -
      sphericalBesselJ l x * sphericalBesselY (l + 1) x = (x ^ 2)⁻¹ := by
  induction l with
  | zero =>
    simp only [sphericalBesselJ_one, sphericalBesselJ_zero, sinc_of_ne_zero hx,
      sphericalBesselY_zero, zero_add, sphericalBesselY_one]
    field_simp
    linear_combination x * sin_sq_add_cos_sq x
  | succ l ih =>
    rw [sphericalBesselJ_add_two_of_ne_zero l hx, sphericalBesselY_add_two_of_ne_zero l hx]
    linear_combination ih

/-- The Wronskian of the two kinds, `j_l y_l' - j_l' y_l = x⁻²` for `x ≠ 0`, in the convention of
`Polynomial.wronskian`. It has no zero, so `j_l` and `y_l` are linearly independent solutions of
the spherical Bessel equation of order `l` on each half-line. -/
theorem wronskian_sphericalBesselJ_sphericalBesselY (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    sphericalBesselJ l x * deriv (sphericalBesselY l) x -
      deriv (sphericalBesselJ l) x * sphericalBesselY l x = (x ^ 2)⁻¹ := by
  rw [deriv_sphericalBesselY_of_ne_zero l hx, deriv_sphericalBesselJ_of_ne_zero l hx,
    ← sphericalBesselJ_succ_mul_sphericalBesselY_sub_sphericalBesselJ_mul_sphericalBesselY_succ
      l hx]
  ring

end EpsilonEridani
