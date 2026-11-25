/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Analysis.Asymptotics.Cocompact
public import EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic
public import EpsilonEridani.Mathematics.SpecialFunctions.Trigonometric.Bounds

/-!
# Large-argument asymptotics of the spherical Bessel functions

The spherical Bessel function of the first kind of order `l` behaves for large `|x|` like a
sine wave shifted by `l` right angles and damped by `1 / x`:

  `j_l(x) = sin (x - l π / 2) / x + O(1 / x ^ 2)`.

This is the asymptotic form that defines a phase shift in partial-wave scattering: a free radial
solution of angular momentum `l` is a sine wave whose phase lags that of the `s`-wave by `l π / 2`.

The estimates are stated along `cocompact ℝ`, that is as `x → +∞` and as `x → -∞` together; the
statements as `x → +∞` follow by `Asymptotics.IsBigO.mono` with `atTop_le_cocompact`. The same
shifted sine describes both ends of the line because `j_l(-x) = (-1) ^ l j_l(x)`
(`sphericalBesselJ_neg`) and `sin (-x - l π / 2) / (-x) = (-1) ^ l sin (x - l π / 2) / x`.

The proof works with the Riccati-Bessel form `x j_l(x)`, in which the three-term recurrence
`x j_{l + 2}(x) = (2 l + 3) j_{l + 1}(x) - x j_l(x)` (`mul_sphericalBesselJ_add_two`) holds on
the whole line with no division. The shifted sines satisfy
`sin (x - (l + 2) π / 2) = -sin (x - l π / 2)`, so the remainders
`x j_l(x) - sin (x - l π / 2)` satisfy the same recurrence up to the term
`(2 l + 3) j_{l + 1}(x)`, which is `O(1 / x)`. A two-step induction from `j_0(x) = sin x / x` and
`j_1(x) = sin x / x ^ 2 - cos x / x` then bounds every remainder.

## Main statements

* `isBigO_mul_sphericalBesselJ_sub_sin_inv_cocompact`: the Riccati-Bessel form,
  `x j_l(x) - sin (x - l π / 2) = O(1 / x)`.
* `isBigO_sphericalBesselJ_sub_sin_div_inv_sq_cocompact`:
  `j_l(x) - sin (x - l π / 2) / x = O(1 / x ^ 2)`, and
  `isLittleO_sphericalBesselJ_sub_sin_div_inv_cocompact`: its weaker form, the difference decays
  faster than `1 / x`.
* `isBigO_sphericalBesselJ_inv_cocompact`: `j_l(x) = O(1 / x)`, and
  `tendsto_sphericalBesselJ_cocompact`: `j_l(x) → 0` as `|x| → ∞`.
* `isBigO_deriv_sphericalBesselJ_sub_cos_div_inv_sq_cocompact`: the derivative,
  `j_l'(x) - cos (x - l π / 2) / x = O(1 / x ^ 2)`, and
  `isLittleO_deriv_sphericalBesselJ_sub_cos_div_inv_cocompact`: its weaker form, the difference
  decays faster than `1 / x`.
* `isBigO_deriv_sphericalBesselJ_inv_cocompact`: `j_l'(x) = O(1 / x)`.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, 10.1.16.
* NIST Digital Library of Mathematical Functions, §10.52(ii) (limiting forms for large argument).
-/

public section

open Filter Topology Real Asymptotics

namespace EpsilonEridani

/-- **The Riccati-Bessel form of the large-argument asymptotics**: along `cocompact ℝ`,
`x j_l(x) = sin (x - l π / 2) + O(1 / x)`. -/
theorem isBigO_mul_sphericalBesselJ_sub_sin_inv_cocompact (l : ℕ) :
    (fun x => x * sphericalBesselJ l x - sin (x - l * (π / 2))) =O[cocompact ℝ]
      fun x => x⁻¹ := by
  -- A two-step induction: the statement for `l` and `l + 1` gives it for `l + 2`.
  suffices H : ∀ l : ℕ,
      ((fun x => x * sphericalBesselJ l x - sin (x - l * (π / 2))) =O[cocompact ℝ]
        fun x => x⁻¹) ∧
      ((fun x => x * sphericalBesselJ (l + 1) x - sin (x - ((l + 1 : ℕ) : ℝ) * (π / 2)))
        =O[cocompact ℝ] fun x => x⁻¹) from (H l).1
  intro l
  induction l with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- `x j_0(x) = x sinc x = sin x`
      exact (isBigO_zero _ _).congr_left fun x => by simp
    · -- `x j_1(x) - sin (x - π / 2) = sin x / x` for `x ≠ 0`
      refine ((isBigO_sin_comp_one _ fun x => x).mul (isBigO_refl (fun x : ℝ => x⁻¹) _)).congr' ?_
        (.of_forall fun x => one_mul _)
      filter_upwards [eventually_ne_cocompact 0] with x hx
      rw [zero_add, Nat.cast_one, one_mul, sin_sub_pi_div_two, sphericalBesselJ_one]
      field_simp
      ring
  | succ l ih =>
    refine ⟨ih.2, ?_⟩
    -- `x j_{l + 1}(x)` is bounded, so `(2 l + 3) j_{l + 1}(x) = O(1 / x)`
    have hj : sphericalBesselJ (l + 1) =O[cocompact ℝ] fun x => x⁻¹ :=
      ih.2.isBigO_inv (isBigO_sin_comp_one _ _) (eventually_ne_cocompact 0)
        (tendsto_inv₀_cocompact.isBigO_one ℝ)
    refine ((hj.const_mul_left (2 * l + 3)).sub ih.1).congr_left fun x => ?_
    -- the remainders obey the recurrence up to `(2 l + 3) j_{l + 1}(x)`, since two right angles
    -- more in the phase flip the sign of the shifted sine; the index `l + 1 + 1` is restated as
    -- `l + 2`, the form `mul_sphericalBesselJ_add_two` expects
    rw [show l + 1 + 1 = l + 2 by rfl, mul_sphericalBesselJ_add_two,
      show x - ((l + 2 : ℕ) : ℝ) * (π / 2) = x - l * (π / 2) - π by push_cast; ring, sin_sub_pi]
    ring

/-- **The spherical Bessel functions decay like `1 / x`**: along `cocompact ℝ`,
`j_l(x) = O(1 / x)`. -/
theorem isBigO_sphericalBesselJ_inv_cocompact (l : ℕ) :
    sphericalBesselJ l =O[cocompact ℝ] fun x => x⁻¹ :=
  (isBigO_mul_sphericalBesselJ_sub_sin_inv_cocompact l).isBigO_inv (isBigO_sin_comp_one _ _)
    (eventually_ne_cocompact 0) (tendsto_inv₀_cocompact.isBigO_one ℝ)

/-- Every spherical Bessel function tends to zero as `|x| → ∞`. -/
theorem tendsto_sphericalBesselJ_cocompact (l : ℕ) :
    Tendsto (sphericalBesselJ l) (cocompact ℝ) (𝓝 0) :=
  (isBigO_sphericalBesselJ_inv_cocompact l).trans_tendsto tendsto_inv₀_cocompact

/-- **The large-argument asymptotics of the spherical Bessel functions**: along `cocompact ℝ`,
`j_l(x) = sin (x - l π / 2) / x + O(1 / x ^ 2)`. -/
theorem isBigO_sphericalBesselJ_sub_sin_div_inv_sq_cocompact (l : ℕ) :
    (fun x => sphericalBesselJ l x - sin (x - l * (π / 2)) / x) =O[cocompact ℝ]
      fun x => (x ^ 2)⁻¹ := by
  refine (isBigO_mul_sphericalBesselJ_sub_sin_inv_cocompact l).inv_mul_inv_sq.congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_cocompact 0] with x hx
  field_simp

/-- **The large-argument asymptotics of the spherical Bessel functions**, in the form
`j_l(x) - sin (x - l π / 2) / x = o(1 / x)` along `cocompact ℝ`: the difference decays faster
than `1 / x`. -/
theorem isLittleO_sphericalBesselJ_sub_sin_div_inv_cocompact (l : ℕ) :
    (fun x => sphericalBesselJ l x - sin (x - l * (π / 2)) / x) =o[cocompact ℝ]
      fun x => x⁻¹ :=
  (isBigO_sphericalBesselJ_sub_sin_div_inv_sq_cocompact l).trans_isLittleO
    (isLittleO_inv_sq_inv tendsto_inv₀_cocompact)

/-- **The large-argument asymptotics of the derivative**: along `cocompact ℝ`,
`j_l'(x) = cos (x - l π / 2) / x + O(1 / x ^ 2)`. -/
theorem isBigO_deriv_sphericalBesselJ_sub_cos_div_inv_sq_cocompact (l : ℕ) :
    (fun x => deriv (sphericalBesselJ l) x - cos (x - l * (π / 2)) / x) =O[cocompact ℝ]
      fun x => (x ^ 2)⁻¹ := by
  -- `j_l' = (l / x) j_l - j_{l + 1}` and `sin (x - (l + 1) π / 2) = -cos (x - l π / 2)`
  have h₁ : (fun x => (l : ℝ) * x⁻¹ * sphericalBesselJ l x) =O[cocompact ℝ]
      fun x => (x ^ 2)⁻¹ := by
    refine ((isBigO_sphericalBesselJ_inv_cocompact l).inv_mul_inv_sq.const_mul_left
      (l : ℝ)).congr_left fun x => by ring
  refine (h₁.sub (isBigO_sphericalBesselJ_sub_sin_div_inv_sq_cocompact (l + 1))).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_cocompact 0] with x hx
  rw [deriv_sphericalBesselJ_of_ne_zero l hx,
    show x - ((l + 1 : ℕ) : ℝ) * (π / 2) = x - l * (π / 2) - π / 2 by push_cast; ring,
    sin_sub_pi_div_two]
  ring

/-- **The large-argument asymptotics of the derivative**, in the form
`j_l'(x) - cos (x - l π / 2) / x = o(1 / x)` along `cocompact ℝ`: the difference decays faster
than `1 / x`. -/
theorem isLittleO_deriv_sphericalBesselJ_sub_cos_div_inv_cocompact (l : ℕ) :
    (fun x => deriv (sphericalBesselJ l) x - cos (x - l * (π / 2)) / x) =o[cocompact ℝ]
      fun x => x⁻¹ :=
  (isBigO_deriv_sphericalBesselJ_sub_cos_div_inv_sq_cocompact l).trans_isLittleO
    (isLittleO_inv_sq_inv tendsto_inv₀_cocompact)

/-- **The derivatives of the spherical Bessel functions decay like `1 / x`**: along
`cocompact ℝ`, `j_l'(x) = O(1 / x)`. -/
theorem isBigO_deriv_sphericalBesselJ_inv_cocompact (l : ℕ) :
    deriv (sphericalBesselJ l) =O[cocompact ℝ] fun x => x⁻¹ := by
  -- `j_l'(x)` is `cos (x - l π / 2) / x = O(1 / x)` up to an `o(1 / x)` remainder
  have hcos : (fun x => cos (x - l * (π / 2)) / x) =O[cocompact ℝ] fun x => x⁻¹ :=
    ((isBigO_cos_comp_one _ _).mul (isBigO_refl (fun x : ℝ => x⁻¹) _)).congr
      (fun _ => (div_eq_mul_inv _ _).symm) fun _ => one_mul _
  exact ((isLittleO_deriv_sphericalBesselJ_sub_cos_div_inv_cocompact l).isBigO.add
    hcos).congr_left fun _ => sub_add_cancel _ _

end EpsilonEridani
