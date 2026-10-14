/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import EpsilonEridani.Mathematics.Analysis.Analytic.DSlope
public import EpsilonEridani.Mathematics.Analysis.Calculus.Deriv.EvenFunction
public import EpsilonEridani.Mathematics.SpecialFunctions.Trigonometric.Sinc

/-!
# Spherical Bessel functions of the first kind

The spherical Bessel function of the first kind of order `l` is given by the Rayleigh formula

  `j_l(x) = x ^ l * (-(1 / x) d/dx) ^ l (sin x / x)`.

The function `sin x / x` is `Real.sinc`. The iterates of `-(1 / x) d/dx` are taken with the
operator `f ↦ -dslope (deriv f) 0`, which maps analytic functions to analytic functions
(`EpsilonEridani.analyticAt_dslope`), so every iterate, and with it every `sphericalBesselJ l`, is
real analytic on the whole line. Every iterate is moreover even, so its derivative vanishes at the
origin. For such `f` the operator agrees with `-f' x / x` for `x ≠ 0`, and at `x = 0` it takes the
value `-f''(0)`, the limit of `-f' x / x` as `x → 0`.

## Main definitions

* `EpsilonEridani.Real.sphericalBesselJ l x`: the spherical Bessel function `j_l(x)`; the Rayleigh
  formula defining it is `sphericalBesselJ_def` together with `reducedSphericalBesselJ_def`.
* `EpsilonEridani.Real.reducedSphericalBesselJ l x`: the even analytic factor
  `(-(1 / x) d/dx) ^ l (sin x / x)`, with `j_l(x) = x ^ l * reducedSphericalBesselJ l x`.

## Main statements

* `sphericalBesselJ_zero`: `j_0 = sinc`, and `sphericalBesselJ_one` gives the closed
  form `j_1(x) = sin x / x ^ 2 - cos x / x`.
* `analyticAt_sphericalBesselJ`: each `j_l` is real analytic on the whole line.
* `sphericalBesselJ_apply_zero`: `j_0(0) = 1` and `j_l(0) = 0` for `l ≠ 0`.
* `tendsto_sphericalBesselJ_div_pow`: the leading behaviour `j_l(x) / x ^ l → 1 / (2 l + 1)‼` at
  the origin.
* `sphericalBesselJ_neg`: the parity `j_l(-x) = (-1) ^ l j_l(x)`.
* `reducedSphericalBesselJ_apply_zero`: the value `1 / (2 l + 1)‼` of the reduced function at the
  origin, and `hasDerivAt_reducedSphericalBesselJ`: its Rayleigh step, the derivative of the
  reduced function of order `l` is `-x` times the one of order `l + 1`.
* `mul_sphericalBesselJ_add_two`: the three-term recurrence in the order on the whole line, and
  `sphericalBesselJ_add_two`: its form solved for `j_{l + 2}(x)`, for `x ≠ 0`.
* `mul_deriv_sphericalBesselJ` and `mul_deriv_sphericalBesselJ_succ`: the two derivative
  relations on the whole line, which raise and lower the order. They form a ladder pair.
  `hasDerivAt_sphericalBesselJ` and `hasDerivAt_sphericalBesselJ_succ` are their forms for
  `x ≠ 0`.
* `hasDerivAt_sphericalBesselJ_apply_zero`: the derivative at the origin, `j_1'(0) = 1 / 3` and
  `j_l'(0) = 0` for `l ≠ 1`.
* `sphericalBesselJ_equation`: `j_l` solves the spherical Bessel equation
  `x ^ 2 y'' + 2 x y' + (x ^ 2 - l (l + 1)) y = 0` on the whole line.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §10.1.
* NIST Digital Library of Mathematical Functions, §10.47 (the equation), §10.49(ii) (Rayleigh's
  formula), §10.51 (recurrence and derivatives) and §10.52 (limiting forms).
-/

@[expose] public section

open Filter Topology Real
open scoped Nat

open EpsilonEridani

namespace EpsilonEridani.Real

/-- The reduced spherical Bessel function `(-(1 / x) d/dx) ^ l (sin x / x)`, the even analytic
factor in `j_l(x) = x ^ l * reducedSphericalBesselJ l x` (`sphericalBesselJ_def`). The operator
`-(1 / x) d/dx` is `f ↦ -dslope (deriv f) 0` (`reducedSphericalBesselJ_def`), which agrees with
`-f' x / x` for `x ≠ 0` on the even functions it is applied to and takes the limiting value at
`x = 0`. -/
noncomputable def reducedSphericalBesselJ (l : ℕ) : ℝ → ℝ :=
  (fun f : ℝ → ℝ => -dslope (deriv f) 0)^[l] sinc

/-- The reduced spherical Bessel function is the `l`-th iterate of `-(1 / x) d/dx` on
`sin x / x`, with `-(1 / x) d/dx` taken as `f ↦ -dslope (deriv f) 0`. -/
theorem reducedSphericalBesselJ_def (l : ℕ) :
    reducedSphericalBesselJ l = (fun f : ℝ → ℝ => -dslope (deriv f) 0)^[l] sinc :=
  (rfl)

local notation "G" => reducedSphericalBesselJ

/-- The reduced spherical Bessel function of order zero is `sin x / x`. -/
@[simp]
theorem reducedSphericalBesselJ_zero : reducedSphericalBesselJ 0 = sinc := (rfl)

private lemma reduced_succ (l : ℕ) : G (l + 1) = -dslope (deriv (G l)) 0 :=
  Function.iterate_succ_apply' _ l sinc

/-- The spherical Bessel function of the first kind of order `l`, given by the Rayleigh formula
`j_l(x) = x ^ l * (-(1 / x) d/dx) ^ l (sin x / x)` (`sphericalBesselJ_def` and
`reducedSphericalBesselJ_def`). The resulting function is analytic on the whole line
(`analyticAt_sphericalBesselJ`). -/
noncomputable def sphericalBesselJ (l : ℕ) (x : ℝ) : ℝ := x ^ l * reducedSphericalBesselJ l x

/-- The spherical Bessel function `j_l(x)` is `x ^ l` times the reduced function of order `l`. -/
theorem sphericalBesselJ_def (l : ℕ) (x : ℝ) :
    sphericalBesselJ l x = x ^ l * reducedSphericalBesselJ l x :=
  (rfl)

private lemma analyticOnNhd_reduced (l : ℕ) : AnalyticOnNhd ℝ (G l) Set.univ := by
  induction l with
  | zero =>
    rw [reducedSphericalBesselJ_zero]
    exact fun x _ => analyticAt_sinc x
  | succ l ih =>
    rw [reduced_succ]
    exact ((analyticOnNhd_dslope (s := Set.univ)).mpr ih.deriv).neg

/-- Every reduced spherical Bessel function is real analytic on the whole line. -/
@[fun_prop]
theorem analyticAt_reducedSphericalBesselJ (l : ℕ) (x : ℝ) :
    AnalyticAt ℝ (reducedSphericalBesselJ l) x :=
  analyticOnNhd_reduced l x (Set.mem_univ x)

/-- Every reduced spherical Bessel function is differentiable. -/
@[fun_prop]
theorem differentiable_reducedSphericalBesselJ (l : ℕ) :
    Differentiable ℝ (reducedSphericalBesselJ l) :=
  fun x => (analyticAt_reducedSphericalBesselJ l x).differentiableAt

/-- Every reduced spherical Bessel function is continuous. -/
@[fun_prop]
theorem continuous_reducedSphericalBesselJ (l : ℕ) : Continuous (reducedSphericalBesselJ l) :=
  (differentiable_reducedSphericalBesselJ l).continuous

/-- Every reduced spherical Bessel function is even. -/
@[simp]
theorem reducedSphericalBesselJ_neg (l : ℕ) (x : ℝ) :
    reducedSphericalBesselJ l (-x) = reducedSphericalBesselJ l x := by
  induction l generalizing x with
  | zero => rw [reducedSphericalBesselJ_zero, sinc_neg]
  | succ l ih =>
    -- the derivative of the even function `G l` is odd
    have hodd : ∀ y, deriv (G l) (-y) = -deriv (G l) y := Function.Even.deriv ih
    have h0 : deriv (G l) 0 = 0 := (Function.Even.deriv ih).map_zero
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · simp only [reduced_succ, Pi.neg_apply, dslope_of_ne _ hx,
        dslope_of_ne _ (neg_ne_zero.mpr hx), slope_def_field, h0, hodd x]
      ring

/-- The derivative of `G l` vanishes at the origin, as it is even. -/
private lemma deriv_reduced_zero (l : ℕ) : deriv (G l) 0 = 0 :=
  (Function.Even.deriv (reducedSphericalBesselJ_neg l)).map_zero

/-- The Rayleigh step on the whole line: the derivative of the reduced function of order `l` is
`-x` times the reduced function of order `l + 1`. -/
theorem hasDerivAt_reducedSphericalBesselJ (l : ℕ) (x : ℝ) :
    HasDerivAt (reducedSphericalBesselJ l) (-x * reducedSphericalBesselJ (l + 1) x) x := by
  have h := sub_smul_dslope (deriv (G l)) 0 x
  rw [deriv_reduced_zero, sub_zero, sub_zero, smul_eq_mul] at h
  -- h: deriv (G l) x = x * dslope (deriv (G l)) 0 x
  rw [reduced_succ, Pi.neg_apply]
  have : (-x) * (-dslope (deriv (G l)) 0 x) = x * dslope (deriv (G l)) 0 x := by ring
  rw [this, h]
  exact (differentiable_reducedSphericalBesselJ l x).hasDerivAt

/-- `x G 0 = sin x`. -/
private lemma mul_reduced_zero (x : ℝ) : x * G 0 x = sin x := by
  rw [reducedSphericalBesselJ_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sinc_of_ne_zero hx, mul_div_cancel₀ _ hx]

/-- The first derivative of `x G 0 = sin x`: `G 0 - x ^ 2 G 1 = cos x`. -/
private lemma reduced_one (x : ℝ) : G 0 x - x ^ 2 * G 1 x = cos x := by
  have hd :=
    ((hasDerivAt_id' x).mul (hasDerivAt_reducedSphericalBesselJ 0 x)).sub (hasDerivAt_sin x)
  linear_combination hd.unique ((hasDerivAt_const x 0).congr_of_eventuallyEq
    (.of_forall fun z => sub_eq_zero.mpr (mul_reduced_zero z)))

/-- The base case of the recurrence: `x ^ 2 G 2 - 3 G 1 + G 0 = 0`. -/
private lemma reduced_recurrence_zero (x : ℝ) :
    x ^ 2 * G 2 x - 3 * G 1 x + G 0 x = 0 := by
  -- second derivative: `x (x ^ 2 G 2 - 3 G 1 + G 0) = 0`
  have h2 : ∀ y, y * (y ^ 2 * G 2 y - 3 * G 1 y + G 0 y) = 0 := by
    intro y
    have hd := ((hasDerivAt_reducedSphericalBesselJ 0 y).sub ((hasDerivAt_pow 2 y).mul
      (hasDerivAt_reducedSphericalBesselJ 1 y))).sub (hasDerivAt_cos y)
    linear_combination hd.unique ((hasDerivAt_const y 0).congr_of_eventuallyEq
      (.of_forall fun z => sub_eq_zero.mpr (reduced_one z))) + mul_reduced_zero y
  -- `x * f x = 0` everywhere and `f` continuous force `f = 0`, also at the origin
  exact congrFun (Continuous.ext_on (dense_compl_singleton 0) (by fun_prop) continuous_const
    fun y hy => (mul_eq_zero.mp (h2 y)).resolve_left hy) x

/-- The three-term recurrence of the reduced functions,
`x ^ 2 G (l + 2) - (2 l + 3) G (l + 1) + G l = 0`, on the whole line. -/
private lemma reduced_recurrence (l : ℕ) (x : ℝ) :
    x ^ 2 * G (l + 2) x - (2 * l + 3) * G (l + 1) x + G l x = 0 := by
  induction l generalizing x with
  | zero => simpa using reduced_recurrence_zero x
  | succ l ih =>
    -- differentiating the recurrence of order `l` gives `-x` times the one of order `l + 1`
    have h : ∀ y, y * (y ^ 2 * G (l + 3) y - (2 * (l + 1 : ℕ) + 3) * G (l + 2) y
        + G (l + 1) y) = 0 := by
      intro y
      have hd := (((hasDerivAt_pow 2 y).mul (hasDerivAt_reducedSphericalBesselJ (l + 2) y)).sub
        ((hasDerivAt_reducedSphericalBesselJ (l + 1) y).const_mul (2 * (l : ℝ) + 3))).add
        (hasDerivAt_reducedSphericalBesselJ l y)
      have := hd.unique ((hasDerivAt_const y 0).congr_of_eventuallyEq (.of_forall ih))
      push_cast at this ⊢
      norm_num at this
      linear_combination -this
    exact congrFun (Continuous.ext_on (dense_compl_singleton 0) (by fun_prop) continuous_const
      fun y hy => (mul_eq_zero.mp (h y)).resolve_left hy) x

/-- The value of the reduced functions at the origin, `1 / (2 l + 1)‼`. -/
theorem reducedSphericalBesselJ_apply_zero (l : ℕ) :
    reducedSphericalBesselJ l 0 = (((2 * l + 1)‼ : ℕ) : ℝ)⁻¹ := by
  induction l with
  | zero => simp
  | succ l ih =>
    have h := reduced_recurrence l 0
    have hl : 2 * (l + 1) + 1 = 2 * l + 1 + 2 := by ring
    rw [hl, Nat.doubleFactorial_add_two, Nat.cast_mul, mul_inv, ← ih]
    push_cast
    field_simp
    linear_combination -h

/-! ### The spherical Bessel functions of the first kind -/

/-- The order-zero spherical Bessel function is `sin x / x`. -/
@[simp]
theorem sphericalBesselJ_zero : sphericalBesselJ 0 = sinc := by
  funext x
  rw [sphericalBesselJ, pow_zero, one_mul, reducedSphericalBesselJ_zero]

/-- Every spherical Bessel function `j_l` is real analytic on the whole line. -/
@[fun_prop]
theorem analyticAt_sphericalBesselJ (l : ℕ) (x : ℝ) : AnalyticAt ℝ (sphericalBesselJ l) x :=
  (analyticAt_id.pow l).mul (analyticAt_reducedSphericalBesselJ l x)

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
theorem tendsto_sphericalBesselJ_div_pow (l : ℕ) :
    Tendsto (fun x => sphericalBesselJ l x / x ^ l) (𝓝[≠] 0)
      (𝓝 (((2 * l + 1)‼ : ℕ) : ℝ)⁻¹) := by
  rw [← reducedSphericalBesselJ_apply_zero]
  refine (((continuous_reducedSphericalBesselJ l).tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [sphericalBesselJ, mul_div_cancel_left₀ _ (pow_ne_zero l hx)]

/-- The parity of the spherical Bessel functions: `j_l(-x) = (-1) ^ l j_l(x)`. -/
@[simp]
theorem sphericalBesselJ_neg (l : ℕ) (x : ℝ) :
    sphericalBesselJ l (-x) = (-1) ^ l * sphericalBesselJ l x := by
  rw [sphericalBesselJ, sphericalBesselJ, reducedSphericalBesselJ_neg, neg_pow, mul_assoc]

/-- The three-term recurrence in the order on the whole line:
`x j_{l + 2}(x) = (2 l + 3) j_{l + 1}(x) - x j_l(x)`. -/
theorem mul_sphericalBesselJ_add_two (l : ℕ) (x : ℝ) :
    x * sphericalBesselJ (l + 2) x =
      (2 * l + 3) * sphericalBesselJ (l + 1) x - x * sphericalBesselJ l x := by
  simp only [sphericalBesselJ]
  linear_combination x ^ (l + 1) * reduced_recurrence l x

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
  (hasDerivAt_pow l x).mul (hasDerivAt_reducedSphericalBesselJ l x)

/-- The derivative relation raising the order on the whole line,
`x j_l'(x) = l j_l(x) - x j_{l + 1}(x)`. -/
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
`x j_{l + 1}'(x) = x j_l(x) - (l + 2) j_{l + 1}(x)`. -/
theorem mul_deriv_sphericalBesselJ_succ (l : ℕ) (x : ℝ) :
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
theorem hasDerivAt_sphericalBesselJ_succ (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (sphericalBesselJ (l + 1))
      (sphericalBesselJ l x - (l + 2) / x * sphericalBesselJ (l + 1) x) x := by
  refine (differentiable_sphericalBesselJ (l + 1) x).hasDerivAt.congr_deriv ?_
  field_simp
  linear_combination mul_deriv_sphericalBesselJ_succ l x

/-- The derivative of `j_l` for `x ≠ 0`, `j_l' = l / x * j_l - j_{l + 1}`. -/
theorem deriv_sphericalBesselJ (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (sphericalBesselJ l) x = l / x * sphericalBesselJ l x - sphericalBesselJ (l + 1) x :=
  (hasDerivAt_sphericalBesselJ l hx).deriv

/-- The derivative of `j_{l + 1}` for `x ≠ 0`, `j_{l + 1}' = j_l - (l + 2) / x * j_{l + 1}`. -/
theorem deriv_sphericalBesselJ_succ (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    deriv (sphericalBesselJ (l + 1)) x =
      sphericalBesselJ l x - (l + 2) / x * sphericalBesselJ (l + 1) x :=
  (hasDerivAt_sphericalBesselJ_succ l hx).deriv

/-- The derivative at the origin: `j_1'(0) = 1 / 3`, and `j_l'(0) = 0` for every `l ≠ 1`. -/
theorem hasDerivAt_sphericalBesselJ_apply_zero (l : ℕ) :
    HasDerivAt (sphericalBesselJ l) (if l = 1 then 3⁻¹ else 0) 0 := by
  convert hasDerivAt_sphericalBesselJ_aux l 0 using 1
  rcases l with _ | _ | l
  · simp
  · simp [reducedSphericalBesselJ_apply_zero]
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
  · have h := reduced_one x
    rw [reducedSphericalBesselJ_zero, sinc_of_ne_zero hx] at h
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
      (hasDerivAt_sphericalBesselJ l hx)).sub (hasDerivAt_sphericalBesselJ_succ l hx)
  rw [hev.deriv_eq, hd.deriv, deriv_sphericalBesselJ l hx]
  field_simp
  ring

/-- `j_l` solves the spherical Bessel equation of order `l` on the whole line:
`x ^ 2 j_l'' + 2 x j_l' + (x ^ 2 - l (l + 1)) j_l = 0`. -/
theorem sphericalBesselJ_equation (l : ℕ) (x : ℝ) :
    x ^ 2 * deriv (deriv (sphericalBesselJ l)) x + 2 * x * deriv (sphericalBesselJ l) x +
      (x ^ 2 - l * (l + 1)) * sphericalBesselJ l x = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rcases l with _ | l <;> simp
  · rw [deriv_deriv_sphericalBesselJ l hx]
    field_simp
    ring

end EpsilonEridani.Real
