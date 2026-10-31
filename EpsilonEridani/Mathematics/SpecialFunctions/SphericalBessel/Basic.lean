/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import EpsilonEridani.Mathematics.Calculus.EvenFunction
public import EpsilonEridani.Mathematics.SpecialFunctions.Trigonometric.Sinc

/-!
# Spherical Bessel functions of the first kind

The spherical Bessel function of the first kind of order `l` is given by the Rayleigh formula

  `j_l(x) = x ^ l * (-(1 / x) d/dx) ^ l (sin x / x)`.

The function `sin x / x` is `Real.sinc`. The iterates of `-(1 / x) d/dx` are taken with the
operator `f ↦ -dslope (deriv f) 0`, which maps analytic functions to analytic functions
(`AnalyticAt.dslope`), so every iterate, and with it every `sphericalBesselJ l`, is
real analytic on the whole line. Every iterate is moreover even, so its derivative vanishes at the
origin. For such `f` the operator agrees with `-f' x / x` for `x ≠ 0`, and at `x = 0` it takes the
value `-f''(0)`, the limit of `-f' x / x` as `x → 0`.

Mathlib's `Complex.besselJ` is the Bessel function of the first kind of complex order and
argument. The spherical functions are its half-integer-order special case: `j_l(x)` is
`√(π / (2 * x)) * Complex.besselJ (l + 1 / 2) x` away from the origin (DLMF §10.47). That
development is not the basis here: its analyticity is available on the slit plane
`Complex.slitPlane` (`Complex.analyticAt_besselJ`), with the whole-plane form
(`Complex.analyticAt_besselJ_int`) restricted to integer order, and it is complex-valued, so it
provides neither the whole-line real analyticity of `j_l` nor its value at the removable
singularity `x = 0`. The Rayleigh formula above supplies both directly.

## Main definitions

* `EpsilonEridani.sphericalBesselJ l x`: the spherical Bessel function `j_l(x)`; the Rayleigh
  formula defining it is `sphericalBesselJ_def` together with `sphericalBesselJDivPow_def`.
* `EpsilonEridani.sphericalBesselJDivPow l x`: the even analytic factor
  `(-(1 / x) d/dx) ^ l (sin x / x)`, with `j_l(x) = x ^ l * sphericalBesselJDivPow l x`; it is
  `j_l(x) / x ^ l` for `x ≠ 0` and its limit `1 / (2 l + 1)‼` at the origin.

## Main statements

* `sphericalBesselJ_zero`: `j_0(x) = sinc x`, and `sphericalBesselJ_one` gives the closed
  form `j_1(x) = sin x / x ^ 2 - cos x / x`.
* `analyticAt_sphericalBesselJ`: each `j_l` is real analytic on the whole line.
* `sphericalBesselJ_apply_zero`: `j_0(0) = 1` and `j_l(0) = 0` for `l ≠ 0`.
* `tendsto_sphericalBesselJ_div_pow_nhdsNE_zero`: the leading behaviour
  `j_l(x) / x ^ l → 1 / (2 l + 1)‼` at the origin.
* `sphericalBesselJ_neg`: the parity `j_l(-x) = (-1) ^ l j_l(x)`.
* `sphericalBesselJDivPow_zero` and `sphericalBesselJDivPow_succ`: the factor `j_l(x) / x ^ l`
  of order zero is `sinc`, and the one of order `l + 1` is `-(1 / x) d/dx` of the one of order
  `l`.
* `sphericalBesselJDivPow_apply_zero`: the value `1 / (2 l + 1)‼` of `j_l(x) / x ^ l` at
  the origin, and `hasDerivAt_sphericalBesselJDivPow` with `deriv_sphericalBesselJDivPow`:
  its Rayleigh step, the derivative of `j_l(x) / x ^ l` is `-x` times `j_{l + 1}(x) / x ^ (l + 1)`.
* `sphericalBesselJDivPow_add_two`: the three-term recurrence of the factors `j_l(x) / x ^ l` on
  the whole line, which is the even factor of `mul_sphericalBesselJ_add_two` and stays informative
  at the origin.
* `mul_sphericalBesselJ_add_two`: the three-term recurrence in the order on the whole line, and
  `sphericalBesselJ_add_two`: its form solved for `j_{l + 2}(x)`, for `x ≠ 0`.
* `mul_deriv_sphericalBesselJ` and `mul_deriv_sphericalBesselJ_succ'`: the two derivative
  relations, which raise and lower the order. They form a ladder pair. They hold on the whole
  line but degenerate to `0 = 0` at the origin; `hasDerivAt_sphericalBesselJ` and
  `hasDerivAt_sphericalBesselJ_succ'` are their forms for `x ≠ 0`, and the derivative at the
  origin is `hasDerivAt_sphericalBesselJ_apply_zero`.
* `hasDerivAt_sphericalBesselJ_apply_zero`: the derivative at the origin, `j_1'(0) = 1 / 3` and
  `j_l'(0) = 0` for `l ≠ 1`; `deriv_deriv_sphericalBesselJ_apply_zero`: the second derivative
  there, `j_0''(0) = -1 / 3`, `j_2''(0) = 2 / 15` and `j_l''(0) = 0` otherwise.
* `sphericalBesselJ_equation`: `j_l` solves the spherical Bessel equation
  `x ^ 2 y'' + 2 x y' + (x ^ 2 - l (l + 1)) y = 0` on the whole line; at the origin it
  degenerates to `0 = 0`.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §10.1.
* NIST Digital Library of Mathematical Functions, §10.47 (the equation), §10.49(ii) (Rayleigh's
  formula), §10.51 (recurrence and derivatives) and §10.52 (limiting forms).
-/

@[expose] public section

open Filter Topology Real
open scoped Nat

namespace EpsilonEridani

/-- The function `(-(1 / x) d/dx) ^ l (sin x / x)`, the even analytic factor in
`j_l(x) = x ^ l * sphericalBesselJDivPow l x` (`sphericalBesselJ_def`): it equals `j_l(x) / x ^ l`
for `x ≠ 0`, and at the origin it takes the limiting value `1 / (2 l + 1)‼`
(`sphericalBesselJDivPow_apply_zero`). The operator
`-(1 / x) d/dx` is `f ↦ -dslope (deriv f) 0` (`sphericalBesselJDivPow_def`), which agrees with
`-f' x / x` for `x ≠ 0` on the even functions it is applied to and takes the limiting value at
`x = 0`. -/
noncomputable def sphericalBesselJDivPow (l : ℕ) : ℝ → ℝ :=
  (fun f : ℝ → ℝ => -dslope (deriv f) 0)^[l] sinc

/-- The function `j_l(x) / x ^ l` is the `l`-th iterate of `-(1 / x) d/dx` on
`sin x / x`, with `-(1 / x) d/dx` taken as `f ↦ -dslope (deriv f) 0`. -/
theorem sphericalBesselJDivPow_def (l : ℕ) :
    sphericalBesselJDivPow l = (fun f : ℝ → ℝ => -dslope (deriv f) 0)^[l] sinc :=
  (rfl)

local notation "G" => sphericalBesselJDivPow

/-- `sphericalBesselJDivPow` of order zero is `sin x / x`. -/
@[simp]
theorem sphericalBesselJDivPow_zero (x : ℝ) : sphericalBesselJDivPow 0 x = sinc x := (rfl)

/-- The Rayleigh step: `j_{l + 1}(x) / x ^ (l + 1)` is `-(1 / x) d/dx` applied to
`j_l(x) / x ^ l`, with `-(1 / x) d/dx` taken as
`f ↦ -dslope (deriv f) 0`. -/
theorem sphericalBesselJDivPow_succ (l : ℕ) :
    sphericalBesselJDivPow (l + 1) = -dslope (deriv (sphericalBesselJDivPow l)) 0 :=
  Function.iterate_succ_apply' _ l sinc

/-- The spherical Bessel function of the first kind of order `l`, given by the Rayleigh formula
`j_l(x) = x ^ l * (-(1 / x) d/dx) ^ l (sin x / x)` (`sphericalBesselJ_def` and
`sphericalBesselJDivPow_def`). The resulting function is analytic on the whole line
(`analyticAt_sphericalBesselJ`). -/
noncomputable def sphericalBesselJ (l : ℕ) (x : ℝ) : ℝ := x ^ l * sphericalBesselJDivPow l x

/-- The spherical Bessel function `j_l(x)` is `x ^ l` times `sphericalBesselJDivPow l x`. -/
theorem sphericalBesselJ_def (l : ℕ) (x : ℝ) :
    sphericalBesselJ l x = x ^ l * sphericalBesselJDivPow l x :=
  (rfl)

private lemma analyticOnNhd_divPow (l : ℕ) : AnalyticOnNhd ℝ (G l) Set.univ := by
  induction l with
  | zero => exact fun x _ => analyticAt_sinc x
  | succ l ih =>
    rw [sphericalBesselJDivPow_succ]
    exact (ih.deriv.dslope 0).neg

/-- Every `sphericalBesselJDivPow l` is real analytic on the whole line. -/
@[fun_prop]
theorem analyticAt_sphericalBesselJDivPow (l : ℕ) (x : ℝ) :
    AnalyticAt ℝ (sphericalBesselJDivPow l) x :=
  analyticOnNhd_divPow l x (Set.mem_univ x)

/-- Every `sphericalBesselJDivPow l` is smooth. -/
@[fun_prop]
theorem contDiff_sphericalBesselJDivPow (l : ℕ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (sphericalBesselJDivPow l) :=
  AnalyticOnNhd.contDiff fun x _ => analyticAt_sphericalBesselJDivPow l x

/-- Every `sphericalBesselJDivPow l` is differentiable. -/
@[fun_prop]
theorem differentiable_sphericalBesselJDivPow (l : ℕ) :
    Differentiable ℝ (sphericalBesselJDivPow l) :=
  fun x => (analyticAt_sphericalBesselJDivPow l x).differentiableAt

/-- Every `sphericalBesselJDivPow l` is continuous. -/
@[fun_prop]
theorem continuous_sphericalBesselJDivPow (l : ℕ) : Continuous (sphericalBesselJDivPow l) :=
  (differentiable_sphericalBesselJDivPow l).continuous

/-- Every `sphericalBesselJDivPow l` is even. -/
@[simp]
theorem sphericalBesselJDivPow_neg (l : ℕ) (x : ℝ) :
    sphericalBesselJDivPow l (-x) = sphericalBesselJDivPow l x := by
  induction l generalizing x with
  | zero => simp only [sphericalBesselJDivPow_zero, sinc_neg]
  | succ l ih =>
    -- the derivative of the even function `G l` is odd
    have hodd : ∀ y, deriv (G l) (-y) = -deriv (G l) y := Function.Even.odd_deriv ih
    have h0 : deriv (G l) 0 = 0 := (Function.Even.odd_deriv ih).map_zero
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp only [sphericalBesselJDivPow_succ, Pi.neg_apply, dslope_of_ne _ hx,
        dslope_of_ne _ (neg_ne_zero.mpr hx), slope_def_field, h0, hodd x]
      ring

/-- The derivative of `G l` vanishes at the origin, as it is even. -/
private lemma deriv_divPow_zero (l : ℕ) : deriv (G l) 0 = 0 :=
  (Function.Even.odd_deriv (sphericalBesselJDivPow_neg l)).map_zero

/-- The Rayleigh step on the whole line: the derivative of `sphericalBesselJDivPow l` is `-x`
times `sphericalBesselJDivPow (l + 1)`. -/
theorem hasDerivAt_sphericalBesselJDivPow (l : ℕ) (x : ℝ) :
    HasDerivAt (sphericalBesselJDivPow l) (-x * sphericalBesselJDivPow (l + 1) x) x := by
  have h := sub_smul_dslope_of_zero (deriv_divPow_zero l) x
  rw [sub_zero, smul_eq_mul] at h
  -- h: x * dslope (deriv (G l)) 0 x = deriv (G l) x
  rw [sphericalBesselJDivPow_succ, Pi.neg_apply]
  have : (-x) * (-dslope (deriv (G l)) 0 x) = x * dslope (deriv (G l)) 0 x := by ring
  rw [this, h]
  exact (differentiable_sphericalBesselJDivPow l x).hasDerivAt

/-- The derivative of `sphericalBesselJDivPow l` is `-x` times `sphericalBesselJDivPow (l + 1)`,
on the whole line. -/
@[simp]
theorem deriv_sphericalBesselJDivPow (l : ℕ) (x : ℝ) :
    deriv (sphericalBesselJDivPow l) x = -x * sphericalBesselJDivPow (l + 1) x :=
  (hasDerivAt_sphericalBesselJDivPow l x).deriv

/-- The first derivative of `x G 0 = sin x`: `G 0 - x ^ 2 G 1 = cos x`. -/
private lemma divPow_one (x : ℝ) : G 0 x - x ^ 2 * G 1 x = cos x := by
  have h : ∀ y, y * G 0 y = sin y := fun y => by rw [sphericalBesselJDivPow_zero, mul_sinc]
  linear_combination ((hasDerivAt_id' x).mul (hasDerivAt_sphericalBesselJDivPow 0 x)).unique
    ((hasDerivAt_sin x).congr_of_eventuallyEq (.of_forall h))

/-- The base case of the recurrence: `x ^ 2 G 2 - 3 G 1 + G 0 = 0`. -/
private lemma divPow_recurrence_zero (x : ℝ) :
    x ^ 2 * G 2 x - 3 * G 1 x + G 0 x = 0 := by
  -- second derivative: `x (x ^ 2 G 2 - 3 G 1 + G 0) = 0`
  have h2 : ∀ y, y * (y ^ 2 * G 2 y - 3 * G 1 y + G 0 y) = 0 := by
    intro y
    linear_combination ((hasDerivAt_sphericalBesselJDivPow 0 y).sub
      ((hasDerivAt_pow 2 y).mul (hasDerivAt_sphericalBesselJDivPow 1 y))).unique
      ((hasDerivAt_cos y).congr_of_eventuallyEq (.of_forall divPow_one)) +
      y * sphericalBesselJDivPow_zero y + mul_sinc y
  -- the bracket vanishes off the origin, hence everywhere by continuity
  refine congrFun (Continuous.ext_on (dense_compl_singleton 0)
    (f := fun y => y ^ 2 * G 2 y - 3 * G 1 y + G 0 y) (by fun_prop) continuous_const
    fun y hy => ?_) x
  exact (mul_eq_zero.mp (h2 y)).resolve_left (Set.mem_compl_singleton_iff.mp hy)

/-- The three-term recurrence of the functions `j_l(x) / x ^ l` on the whole line:
`x ^ 2 * sphericalBesselJDivPow (l + 2) x - (2 * l + 3) * sphericalBesselJDivPow (l + 1) x
+ sphericalBesselJDivPow l x = 0`. Unlike `mul_sphericalBesselJ_add_two`, which multiplies it
by `x ^ (l + 1)`, it does not degenerate to `0 = 0` at the origin. -/
theorem sphericalBesselJDivPow_add_two (l : ℕ) (x : ℝ) :
    x ^ 2 * sphericalBesselJDivPow (l + 2) x - (2 * l + 3) * sphericalBesselJDivPow (l + 1) x +
      sphericalBesselJDivPow l x = 0 := by
  induction l generalizing x with
  | zero => simpa using divPow_recurrence_zero x
  | succ l ih =>
    -- differentiating the recurrence of order `l` gives `-x` times the one of order `l + 1`
    have h : ∀ y, y * (y ^ 2 * G (l + 3) y - (2 * (l + 1 : ℕ) + 3) * G (l + 2) y
        + G (l + 1) y) = 0 := by
      intro y
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
      have hd := ((hsq.mul (hasDerivAt_sphericalBesselJDivPow (l + 2) y)).sub
        ((hasDerivAt_sphericalBesselJDivPow (l + 1) y).const_mul (2 * (l : ℝ) + 3))).add
        (hasDerivAt_sphericalBesselJDivPow l y)
      have hstep : 2 * y * G (l + 2) y + y ^ 2 * (-y * G (l + 3) y) -
          (2 * l + 3) * (-y * G (l + 2) y) + -y * G (l + 1) y = 0 :=
        hd.unique ((hasDerivAt_const y 0).congr_of_eventuallyEq (.of_forall ih))
      push_cast
      linear_combination -hstep
    -- the bracket vanishes off the origin, hence everywhere by continuity
    refine congrFun (Continuous.ext_on (dense_compl_singleton 0)
      (f := fun y => y ^ 2 * G (l + 3) y - (2 * (l + 1 : ℕ) + 3) * G (l + 2) y + G (l + 1) y)
      (by fun_prop) continuous_const fun y hy => ?_) x
    exact (mul_eq_zero.mp (h y)).resolve_left (Set.mem_compl_singleton_iff.mp hy)

/-- The value of `j_l(x) / x ^ l` at the origin, `1 / (2 l + 1)‼`. -/
@[simp]
theorem sphericalBesselJDivPow_apply_zero (l : ℕ) :
    sphericalBesselJDivPow l 0 = (((2 * l + 1)‼ : ℕ) : ℝ)⁻¹ := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h := sphericalBesselJDivPow_add_two l 0
    have hl : 2 * (l + 1) + 1 = 2 * l + 1 + 2 := by ring
    rw [hl, Nat.doubleFactorial_add_two, Nat.cast_mul, mul_inv, ← ih]
    push_cast
    field_simp
    linear_combination -h

/-! ### The spherical Bessel functions of the first kind -/

/-- The order-zero spherical Bessel function is `sin x / x`. -/
@[simp]
theorem sphericalBesselJ_zero (x : ℝ) : sphericalBesselJ 0 x = sinc x := by
  rw [sphericalBesselJ, pow_zero, one_mul, sphericalBesselJDivPow_zero]

/-- Every spherical Bessel function `j_l` is real analytic on the whole line. -/
@[fun_prop]
theorem analyticAt_sphericalBesselJ (l : ℕ) (x : ℝ) : AnalyticAt ℝ (sphericalBesselJ l) x :=
  (analyticAt_id.pow l).mul (analyticAt_sphericalBesselJDivPow l x)

/-- Every spherical Bessel function `j_l` is smooth. -/
@[fun_prop]
theorem contDiff_sphericalBesselJ (l : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (sphericalBesselJ l) :=
  AnalyticOnNhd.contDiff fun x _ => analyticAt_sphericalBesselJ l x

/-- Every spherical Bessel function `j_l` is differentiable. -/
@[fun_prop]
theorem differentiable_sphericalBesselJ (l : ℕ) : Differentiable ℝ (sphericalBesselJ l) :=
  fun x => (analyticAt_sphericalBesselJ l x).differentiableAt

/-- Every spherical Bessel function `j_l` is continuous. -/
@[fun_prop]
theorem continuous_sphericalBesselJ (l : ℕ) : Continuous (sphericalBesselJ l) :=
  (differentiable_sphericalBesselJ l).continuous

/-- The value at the origin: `j_0(0) = 1`, and `j_l(0) = 0` for every `l ≠ 0`. -/
@[simp]
theorem sphericalBesselJ_apply_zero (l : ℕ) :
    sphericalBesselJ l 0 = if l = 0 then 1 else 0 := by
  rcases l with _ | l
  · simp
  · simp [sphericalBesselJ]

/-- The leading behaviour at the origin: `j_l(x) / x ^ l → 1 / (2 l + 1)‼` as `x → 0`. -/
theorem tendsto_sphericalBesselJ_div_pow_nhdsNE_zero (l : ℕ) :
    Tendsto (fun x => sphericalBesselJ l x / x ^ l) (𝓝[≠] 0)
      (𝓝 (((2 * l + 1)‼ : ℕ) : ℝ)⁻¹) := by
  rw [← sphericalBesselJDivPow_apply_zero]
  refine (((continuous_sphericalBesselJDivPow l).tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [sphericalBesselJ, mul_div_cancel_left₀ _ (pow_ne_zero l hx)]

/-- The parity of the spherical Bessel functions: `j_l(-x) = (-1) ^ l j_l(x)`. -/
@[simp]
theorem sphericalBesselJ_neg (l : ℕ) (x : ℝ) :
    sphericalBesselJ l (-x) = (-1) ^ l * sphericalBesselJ l x := by
  rw [sphericalBesselJ, sphericalBesselJ, sphericalBesselJDivPow_neg, neg_pow, mul_assoc]

/-- The three-term recurrence in the order on the whole line:
`x j_{l + 2}(x) = (2 l + 3) j_{l + 1}(x) - x j_l(x)`. -/
theorem mul_sphericalBesselJ_add_two (l : ℕ) (x : ℝ) :
    x * sphericalBesselJ (l + 2) x =
      (2 * l + 3) * sphericalBesselJ (l + 1) x - x * sphericalBesselJ l x := by
  simp only [sphericalBesselJ]
  linear_combination x ^ (l + 1) * sphericalBesselJDivPow_add_two l x

/-- The three-term recurrence in the order:
`j_{l + 2}(x) = (2 l + 3) / x * j_{l + 1}(x) - j_l(x)` for `x ≠ 0`. -/
theorem sphericalBesselJ_add_two (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    sphericalBesselJ (l + 2) x =
      (2 * l + 3) / x * sphericalBesselJ (l + 1) x - sphericalBesselJ l x := by
  field_simp
  linear_combination mul_sphericalBesselJ_add_two l x

/-- The product rule for `j_l(x) = x ^ l G l x`, on the whole line. -/
private lemma hasDerivAt_sphericalBesselJ_aux (l : ℕ) (x : ℝ) :
    HasDerivAt (sphericalBesselJ l) (l * x ^ (l - 1) * G l x + x ^ l * (-x * G (l + 1) x)) x :=
  (hasDerivAt_pow l x).mul (hasDerivAt_sphericalBesselJDivPow l x)

/-- The derivative relation raising the order on the whole line,
`x j_l'(x) = l j_l(x) - x j_{l + 1}(x)`. At the origin it degenerates to `0 = 0` and carries no
information about `j_l'(0)`; that is `hasDerivAt_sphericalBesselJ_apply_zero`. -/
theorem mul_deriv_sphericalBesselJ (l : ℕ) (x : ℝ) :
    x * deriv (sphericalBesselJ l) x =
      l * sphericalBesselJ l x - x * sphericalBesselJ (l + 1) x := by
  rw [(hasDerivAt_sphericalBesselJ_aux l x).deriv]
  simp only [sphericalBesselJ]
  rcases l with _ | l
  · ring
  · rw [Nat.add_sub_cancel]
    ring

/-- The derivative relation lowering the order on the whole line,
`x j_{l + 1}'(x) = x j_l(x) - (l + 2) j_{l + 1}(x)`. At the origin it degenerates to `0 = 0` and
carries no information about `j_{l + 1}'(0)`; that is `hasDerivAt_sphericalBesselJ_apply_zero`. -/
theorem mul_deriv_sphericalBesselJ_succ' (l : ℕ) (x : ℝ) :
    x * deriv (sphericalBesselJ (l + 1)) x =
      x * sphericalBesselJ l x - (l + 2) * sphericalBesselJ (l + 1) x := by
  have h := mul_deriv_sphericalBesselJ (l + 1) x
  push_cast at h
  linear_combination h - mul_sphericalBesselJ_add_two l x

/-- The derivative relation raising the order, `j_l' = l / x * j_l - j_{l + 1}` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselJ (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (sphericalBesselJ l)
      (l / x * sphericalBesselJ l x - sphericalBesselJ (l + 1) x) x := by
  refine (differentiable_sphericalBesselJ l x).hasDerivAt.congr_deriv ?_
  field_simp
  linear_combination mul_deriv_sphericalBesselJ l x

/-- The derivative relation lowering the order,
`j_{l + 1}' = j_l - (l + 2) / x * j_{l + 1}` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselJ_succ' (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (sphericalBesselJ (l + 1))
      (sphericalBesselJ l x - (l + 2) / x * sphericalBesselJ (l + 1) x) x := by
  refine (differentiable_sphericalBesselJ (l + 1) x).hasDerivAt.congr_deriv ?_
  field_simp
  linear_combination mul_deriv_sphericalBesselJ_succ' l x

/-- The derivative of `j_l` for `x ≠ 0`, `j_l' = l / x * j_l - j_{l + 1}`. -/
theorem deriv_sphericalBesselJ (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (sphericalBesselJ l) x = l / x * sphericalBesselJ l x - sphericalBesselJ (l + 1) x :=
  (hasDerivAt_sphericalBesselJ l hx).deriv

/-- The derivative of `j_{l + 1}` for `x ≠ 0`, `j_{l + 1}' = j_l - (l + 2) / x * j_{l + 1}`. -/
theorem deriv_sphericalBesselJ_succ' (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (sphericalBesselJ (l + 1)) x =
      sphericalBesselJ l x - (l + 2) / x * sphericalBesselJ (l + 1) x :=
  (hasDerivAt_sphericalBesselJ_succ' l hx).deriv

/-- The derivative at the origin: `j_1'(0) = 1 / 3`, and `j_l'(0) = 0` for every `l ≠ 1`. -/
theorem hasDerivAt_sphericalBesselJ_apply_zero (l : ℕ) :
    HasDerivAt (sphericalBesselJ l) (if l = 1 then 3⁻¹ else 0) 0 := by
  convert hasDerivAt_sphericalBesselJ_aux l 0 using 1
  rcases l with _ | _ | l
  · simp
  · simp [sphericalBesselJDivPow_apply_zero]
  · simp

/-- The derivative at the origin: `j_1'(0) = 1 / 3`, and `j_l'(0) = 0` for every `l ≠ 1`. -/
@[simp]
theorem deriv_sphericalBesselJ_apply_zero (l : ℕ) :
    deriv (sphericalBesselJ l) 0 = if l = 1 then 3⁻¹ else 0 :=
  (hasDerivAt_sphericalBesselJ_apply_zero l).deriv

/-- The order-one spherical Bessel function, `j_1(x) = sin x / x ^ 2 - cos x / x`. -/
@[simp]
theorem sphericalBesselJ_one (x : ℝ) : sphericalBesselJ 1 x = sin x / x ^ 2 - cos x / x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h := divPow_one x
    rw [sphericalBesselJDivPow_zero, sinc_of_ne_zero hx] at h
    rw [sphericalBesselJ, pow_one]
    field_simp at h ⊢
    linear_combination -h

/-- The second derivative of `j_l` for `x ≠ 0`:
`j_l'' = -(2 / x) j_l' + (l (l + 1) / x ^ 2 - 1) j_l`. -/
theorem deriv_deriv_sphericalBesselJ (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (sphericalBesselJ l)) x =
      -(2 / x) * deriv (sphericalBesselJ l) x +
        (l * (l + 1) / x ^ 2 - 1) * sphericalBesselJ l x := by
  have hev : deriv (sphericalBesselJ l) =ᶠ[𝓝 x]
      fun y => l * y⁻¹ * sphericalBesselJ l y - sphericalBesselJ (l + 1) y := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    rw [deriv_sphericalBesselJ l hy, div_eq_mul_inv]
  have hd : HasDerivAt (fun y => l * y⁻¹ * sphericalBesselJ l y - sphericalBesselJ (l + 1) y)
      (l * -(x ^ 2)⁻¹ * sphericalBesselJ l x +
          l * x⁻¹ * (l / x * sphericalBesselJ l x - sphericalBesselJ (l + 1) x) -
        (sphericalBesselJ l x - (l + 2) / x * sphericalBesselJ (l + 1) x)) x :=
    (((hasDerivAt_inv hx).const_mul (l : ℝ)).mul
      (hasDerivAt_sphericalBesselJ l hx)).sub (hasDerivAt_sphericalBesselJ_succ' l hx)
  rw [hev.deriv_eq, hd.deriv, deriv_sphericalBesselJ l hx]
  field_simp
  ring

/-- The second derivative at the origin: `j_0''(0) = -1 / 3`, `j_2''(0) = 2 / 15`, and
`j_l''(0) = 0` for every other `l`. -/
@[simp]
theorem deriv_deriv_sphericalBesselJ_apply_zero (l : ℕ) :
    deriv (deriv (sphericalBesselJ l)) 0 = if l = 0 then -3⁻¹ else if l = 2 then 2 / 15 else 0 := by
  have hd : deriv (sphericalBesselJ l) =
      fun y => l * y ^ (l - 1) * G l y - y ^ (l + 1) * G (l + 1) y :=
    funext fun y => by rw [(hasDerivAt_sphericalBesselJ_aux l y).deriv]; ring
  have h : HasDerivAt (fun y => l * y ^ (l - 1) * G l y - y ^ (l + 1) * G (l + 1) y) _ 0 :=
    (((hasDerivAt_pow (l - 1) 0).const_mul (l : ℝ)).mul
      (hasDerivAt_sphericalBesselJDivPow l 0)).sub
        ((hasDerivAt_pow (l + 1) 0).mul (hasDerivAt_sphericalBesselJDivPow (l + 1) 0))
  rw [hd, h.deriv]
  rcases l with _ | _ | _ | l <;> norm_num [Nat.doubleFactorial]

/-- `j_l` solves the spherical Bessel equation of order `l` on the whole line:
`x ^ 2 j_l'' + 2 x j_l' + (x ^ 2 - l (l + 1)) j_l = 0`. At the origin it degenerates to `0 = 0`
and carries no information about `j_l''(0)` or `j_l'(0)`; those are
`deriv_deriv_sphericalBesselJ_apply_zero` and `deriv_sphericalBesselJ_apply_zero`. -/
theorem sphericalBesselJ_equation (l : ℕ) (x : ℝ) :
    x ^ 2 * deriv (deriv (sphericalBesselJ l)) x + 2 * x * deriv (sphericalBesselJ l) x +
      (x ^ 2 - l * (l + 1)) * sphericalBesselJ l x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases l with _ | l <;> simp
  · rw [deriv_deriv_sphericalBesselJ l hx]
    field_simp
    ring

end EpsilonEridani
