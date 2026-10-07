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
public import EpsilonEridani.Mathematics.Analysis.Normed.Module.SMulEqZero

/-!
# Spherical Bessel functions of the first kind

The spherical Bessel function of the first kind of order `l` is given by the Rayleigh formula

  `j_l(x) = x ^ l * (-(1 / x) d/dx) ^ l (sin x / x)`.

The function `sin x / x` is `Real.sinc`. Every iterate of `-(1 / x) d/dx` applied to it is an
even function, so its derivative vanishes at the origin and `f' x / x` has a removable singularity
there. The iterates are therefore taken with the operator `f ↦ -dslope (deriv f) 0`, which agrees
with `-(1 / x) f'` away from the origin when `deriv f 0 = 0`, and fills in the limit at the
origin. All functions this operator is applied to are even with vanishing derivative at 0. All
iterates are then real analytic on the whole line, and so is every `sphericalBesselJ l`.

## Main definitions

* `EpsilonEridani.Real.sphericalBesselJ l x`: the spherical Bessel function `j_l(x)`; the Rayleigh
  formula defining it is `sphericalBesselJ_def`.

## Main statements

* `sphericalBesselJ_zero`: `j_0 = sinc`, and `sphericalBesselJ_one` gives the closed
  form `j_1(x) = sin x / x ^ 2 - cos x / x`.
* `analyticAt_sphericalBesselJ`: each `j_l` is real analytic on the whole line.
* `sphericalBesselJ_apply_zero`: `j_0(0) = 1` and `j_l(0) = 0` for `l ≠ 0`.
* `tendsto_sphericalBesselJ_div_pow`: the leading behaviour `j_l(x) / x ^ l → 1 / (2 l + 1)‼` at
  the origin.
* `sphericalBesselJ_neg`: the parity `j_l(-x) = (-1) ^ l j_l(x)`.
* `sphericalBesselJ_add_two`: the three-term recurrence in the order.
* `hasDerivAt_sphericalBesselJ` and `hasDerivAt_sphericalBesselJ_succ'`: the two derivative
  relations, which lower and raise the order. They form a ladder pair, arranged after the ladder
  relations of TauCeti's Hermite functions (`TauCeti.hasDerivAt_hermiteFunction`).
* `hasDerivAt_sphericalBesselJ_apply_zero`: the derivative at the origin, `j_1'(0) = 1 / 3` and
  `j_l'(0) = 0` for `l ≠ 1`.
* `sphericalBesselJ_equation`: `j_l` solves the spherical Bessel equation
  `x ^ 2 y'' + 2 x y' + (x ^ 2 - l (l + 1)) y = 0` on the whole line.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, §10.1.
* NIST Digital Library of Mathematical Functions, §10.47 (the equation), §10.49(ii) (Rayleigh's
  formula), §10.51 (recurrence and derivatives) and §10.52 (limiting forms).
-/

public section

open Filter Topology Real
open scoped Nat

open EpsilonEridani

namespace EpsilonEridani.Real

/-- The reduced spherical Bessel function `(-(1 / x) d/dx) ^ l (sin x / x)`; it is even, analytic,
and equals `j_l(x) / x ^ l` away from the origin. -/
private noncomputable def reducedSphericalBesselJ (l : ℕ) : ℝ → ℝ :=
  (fun f : ℝ → ℝ => -dslope (deriv f) 0)^[l] sinc

local notation "G" => reducedSphericalBesselJ

/-- The spherical Bessel function of the first kind of order `l`, given by the Rayleigh formula
`j_l(x) = x ^ l * (-(1 / x) d/dx) ^ l (sin x / x)` (`sphericalBesselJ_def`). The operator
`-(1 / x) d/dx` is `f ↦ -dslope (deriv f) 0`, which agrees with `-f' x / x` for `x ≠ 0` on the even
functions it is applied to and takes the limiting value at `x = 0`. The resulting function is
analytic on the whole line (`analyticAt_sphericalBesselJ`). -/
noncomputable def sphericalBesselJ (l : ℕ) (x : ℝ) : ℝ := x ^ l * G l x

/-- The Rayleigh formula `j_l(x) = x ^ l * (-(1 / x) d/dx) ^ l (sin x / x)` defining
`sphericalBesselJ`, with `-(1 / x) d/dx` taken as `f ↦ -dslope (deriv f) 0`. -/
theorem sphericalBesselJ_def (l : ℕ) (x : ℝ) :
    sphericalBesselJ l x = x ^ l * (fun f : ℝ → ℝ => -dslope (deriv f) 0)^[l] sinc x :=
  (rfl)

private lemma reduced_succ (l : ℕ) : G (l + 1) = -dslope (deriv (G l)) 0 := by
  rw [reducedSphericalBesselJ, Function.iterate_succ_apply']
  rfl

private lemma analyticOnNhd_reduced (l : ℕ) : AnalyticOnNhd ℝ (G l) Set.univ := by
  induction l with
  | zero =>
    rw [reducedSphericalBesselJ, Function.iterate_zero_apply, sinc_eq_dslope]
    exact (analyticOnNhd_dslope (s := Set.univ)).mpr fun x _ => analyticAt_sin
  | succ l ih =>
    rw [reduced_succ]
    exact ((analyticOnNhd_dslope (s := Set.univ)).mpr ih.deriv).neg

@[fun_prop]
private lemma differentiable_reduced (l : ℕ) : Differentiable ℝ (G l) :=
  fun x => (analyticOnNhd_reduced l x (Set.mem_univ x)).differentiableAt

@[fun_prop]
private lemma continuous_reduced (l : ℕ) : Continuous (G l) :=
  (differentiable_reduced l).continuous

/-- Each reduced function is even. -/
private lemma reduced_neg (l : ℕ) (x : ℝ) : G l (-x) = G l x := by
  induction l generalizing x with
  | zero => exact sinc_neg x
  | succ l ih =>
    -- the derivative of the even function `G l` is odd
    have hodd : ∀ y, deriv (G l) (-y) = -deriv (G l) y := odd_deriv_of_even ih
    have h0 : deriv (G l) 0 = 0 := (odd_deriv_of_even ih).map_zero
    rw [reduced_succ]
    rcases eq_or_ne x 0 with rfl | hx
    · rw [neg_zero]
    · simp only [Pi.neg_apply, dslope_of_ne _ hx, dslope_of_ne _ (neg_ne_zero.mpr hx),
        slope_def_field, hodd, h0]
      ring

/-- The derivative of `G l` vanishes at the origin, since `G l` is even. -/
private lemma deriv_reduced_zero (l : ℕ) : deriv (G l) 0 = 0 :=
  (odd_deriv_of_even (reduced_neg l)).map_zero

/-- The Rayleigh step everywhere: `(G l)' = -x * G (l + 1)`. -/
private lemma hasDerivAt_reduced (l : ℕ) (x : ℝ) :
    HasDerivAt (G l) (-x * G (l + 1) x) x := by
  have h := sub_smul_dslope (deriv (G l)) 0 x
  rw [deriv_reduced_zero, sub_zero, sub_zero, smul_eq_mul] at h
  rw [reduced_succ, Pi.neg_apply, mul_neg, neg_mul, neg_neg, h]
  exact (differentiable_reduced l x).hasDerivAt

/-- The base case of the recurrence: `x ^ 2 G 2 - 3 G 1 + G 0 = 0`. It follows by differentiating
`x * sinc x = sin x` twice. -/
private lemma reduced_recurrence_zero (x : ℝ) :
    x ^ 2 * G 2 x - 3 * G 1 x + G 0 x = 0 := by
  have hsin : ∀ y, y * G 0 y = sin y := by
    intro y
    rw [reducedSphericalBesselJ, Function.iterate_zero_apply]
    rcases eq_or_ne y 0 with rfl | hy
    · simp
    · rw [sinc_of_ne_zero hy, mul_div_cancel₀ _ hy]
  -- first derivative: `G 0 - x ^ 2 G 1 = cos x`
  have h1 : ∀ y, G 0 y - y ^ 2 * G 1 y - cos y = 0 := by
    intro y
    have hd := ((hasDerivAt_id' y).mul (hasDerivAt_reduced 0 y)).sub (hasDerivAt_sin y)
    have := hd.unique ((hasDerivAt_const y 0).congr_of_eventuallyEq
      (Eventually.of_forall fun z => sub_eq_zero.mpr (hsin z)))
    linear_combination this
  -- second derivative: `x (x ^ 2 G 2 - 3 G 1 + G 0) = 0`
  have h2 : ∀ y, y * (y ^ 2 * G 2 y - 3 * G 1 y + G 0 y) = 0 := by
    intro y
    have hd := ((hasDerivAt_reduced 0 y).sub ((hasDerivAt_pow 2 y).mul
      (hasDerivAt_reduced 1 y))).sub (hasDerivAt_cos y)
    have := hd.unique ((hasDerivAt_const y 0).congr_of_eventuallyEq (Eventually.of_forall h1))
    linear_combination this + hsin y
  -- `x * f x = 0` everywhere and `f` continuous force `f = 0`, also at the origin
  exact congrFun (eq_zero_of_forall_smul_eq_zero (by fun_prop) h2) x

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
      have hd := (((hasDerivAt_pow 2 y).mul (hasDerivAt_reduced (l + 2) y)).sub
        ((hasDerivAt_reduced (l + 1) y).const_mul (2 * (l : ℝ) + 3))).add
        (hasDerivAt_reduced l y)
      have := hd.unique ((hasDerivAt_const y 0).congr_of_eventuallyEq (Eventually.of_forall ih))
      push_cast at this ⊢
      norm_num at this
      linear_combination -this
    exact congrFun (eq_zero_of_forall_smul_eq_zero (by fun_prop) h) x

/-- The value of the reduced functions at the origin, `G l 0 = 1 / (2 l + 1)‼`. -/
private lemma reduced_apply_zero (l : ℕ) : G l 0 = (((2 * l + 1)‼ : ℕ) : ℝ)⁻¹ := by
  induction l with
  | zero => simp [reducedSphericalBesselJ]
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
  rw [sphericalBesselJ, pow_zero, one_mul, reducedSphericalBesselJ, Function.iterate_zero_apply]

/-- Every spherical Bessel function `j_l` is real analytic on the whole line. -/
@[fun_prop]
theorem analyticAt_sphericalBesselJ (l : ℕ) (x : ℝ) : AnalyticAt ℝ (sphericalBesselJ l) x :=
  (analyticAt_id.pow l).mul (analyticOnNhd_reduced l x (Set.mem_univ x))

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
  rw [← reduced_apply_zero]
  refine (((continuous_reduced l).tendsto 0).mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [sphericalBesselJ, mul_div_cancel_left₀ _ (pow_ne_zero l hx)]

/-- The parity of the spherical Bessel functions: `j_l(-x) = (-1) ^ l j_l(x)`. -/
theorem sphericalBesselJ_neg (l : ℕ) (x : ℝ) :
    sphericalBesselJ l (-x) = (-1) ^ l * sphericalBesselJ l x := by
  rw [sphericalBesselJ, sphericalBesselJ, reduced_neg, neg_pow, mul_assoc]

/-- The three-term recurrence in the order:
`j_{l + 2}(x) = (2 l + 3) / x * j_{l + 1}(x) - j_l(x)` for `x ≠ 0`. -/
theorem sphericalBesselJ_add_two (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    sphericalBesselJ (l + 2) x =
      (2 * l + 3) / x * sphericalBesselJ (l + 1) x - sphericalBesselJ l x := by
  have h := reduced_recurrence l x
  simp only [sphericalBesselJ]
  field_simp
  linear_combination x ^ (l + 1) * h

/-- The derivative relation lowering the order, `j_l' = l / x * j_l - j_{l + 1}` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselJ (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (sphericalBesselJ l)
      (l / x * sphericalBesselJ l x - sphericalBesselJ (l + 1) x) x := by
  have h : HasDerivAt (sphericalBesselJ l)
      (l * x ^ (l - 1) * G l x + x ^ l * (-x * G (l + 1) x)) x :=
    (hasDerivAt_pow l x).mul (hasDerivAt_reduced l x)
  convert h using 1
  simp only [sphericalBesselJ]
  rcases l with _ | l
  · ring
  · rw [Nat.add_sub_cancel]
    field_simp
    ring

/-- The derivative relation raising the order,
`j_{l + 1}' = j_l - (l + 2) / x * j_{l + 1}` for `x ≠ 0`. -/
theorem hasDerivAt_sphericalBesselJ_succ' (l : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (sphericalBesselJ (l + 1))
      (sphericalBesselJ l x - (l + 2) / x * sphericalBesselJ (l + 1) x) x := by
  convert hasDerivAt_sphericalBesselJ (l + 1) hx using 1
  rw [sphericalBesselJ_add_two l hx]
  push_cast
  field_simp
  ring

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
  have h : HasDerivAt (sphericalBesselJ l)
      (l * 0 ^ (l - 1) * G l 0 + 0 ^ l * (-0 * G (l + 1) 0)) 0 :=
    (hasDerivAt_pow l 0).mul (hasDerivAt_reduced l 0)
  convert h using 1
  rcases l with _ | _ | l
  · simp
  · simp [reduced_apply_zero]
  · simp

/-- The derivative at the origin: `j_1'(0) = 1 / 3`, and `j_l'(0) = 0` for every `l ≠ 1`. -/
theorem deriv_sphericalBesselJ_apply_zero (l : ℕ) :
    deriv (sphericalBesselJ l) 0 = if l = 1 then 3⁻¹ else 0 :=
  (hasDerivAt_sphericalBesselJ_apply_zero l).deriv

/-- The order-one spherical Bessel function, `j_1(x) = sin x / x ^ 2 - cos x / x`. -/
theorem sphericalBesselJ_one (x : ℝ) : sphericalBesselJ 1 x = sin x / x ^ 2 - cos x / x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hsinc : HasDerivAt sinc ((cos x * x - sin x * 1) / x ^ 2) x := by
      refine ((hasDerivAt_sin x).div (hasDerivAt_id x) hx).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ne.mem_nhds hx] with y hy
      exact sinc_of_ne_zero hy
    have h := hasDerivAt_sphericalBesselJ 0 hx
    rw [sphericalBesselJ_zero] at h
    have := h.unique hsinc
    field_simp at this ⊢
    linear_combination -this

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
  have hd := (((hasDerivAt_inv hx).const_mul (l : ℝ)).mul
    (hasDerivAt_sphericalBesselJ l hx)).sub (hasDerivAt_sphericalBesselJ_succ' l hx)
  have hd' : deriv (fun y => l * y⁻¹ * sphericalBesselJ l y - sphericalBesselJ (l + 1) y) x = _ :=
    hd.deriv
  rw [hev.deriv_eq, hd', deriv_sphericalBesselJ l hx]
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
