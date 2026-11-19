/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded

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
  `j_l'(x) - cos (x - l π / 2) / x = O(1 / x ^ 2)`.

## References

* M. Abramowitz and I. A. Stegun, *Handbook of Mathematical Functions*, 10.1.16.
* NIST Digital Library of Mathematical Functions, §10.52(ii) (limiting forms for large argument).
-/

public section

open Filter Topology Real Asymptotics

namespace EpsilonEridani

/-- Two right angles more in the phase flip the sign of the shifted sine:
`sin (x - (l + 2) π / 2) = -sin (x - l π / 2)`. -/
private theorem sin_sub_add_two_mul_pi_div_two (l : ℕ) (x : ℝ) :
    sin (x - ((l + 2 : ℕ) : ℝ) * (π / 2)) = -sin (x - l * (π / 2)) := by
  rw [← sin_sub_pi]
  congr 1
  push_cast
  ring

/-- Away from a compact neighbourhood of the origin, `x ≠ 0`. -/
private theorem eventually_ne_zero_cocompact : ∀ᶠ x : ℝ in cocompact ℝ, x ≠ 0 := by
  filter_upwards [(isCompact_singleton (x := (0 : ℝ))).compl_mem_cocompact] with x hx
  exact Set.mem_compl_singleton_iff.mp hx

/-- `x⁻¹ → 0` as `|x| → ∞`. -/
private theorem tendsto_inv_cocompact : Tendsto (fun x : ℝ => x⁻¹) (cocompact ℝ) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_inv₀_cobounded

/-- A shifted sine is bounded. -/
private theorem isBigO_sin_sub_one (c : ℝ) :
    (fun x : ℝ => sin (x - c)) =O[cocompact ℝ] fun _ => (1 : ℝ) :=
  .of_bound 1 (.of_forall fun x => by simpa using abs_sin_le_one (x - c))

/-- If `x f(x)` is bounded along `cocompact ℝ`, then `f(x) = O(1 / x)`, since
`f(x) = x⁻¹ (x f(x))` for `x ≠ 0`. -/
private theorem isBigO_inv_of_isBigO_mul_one {f : ℝ → ℝ}
    (h : (fun x => x * f x) =O[cocompact ℝ] fun _ => (1 : ℝ)) :
    f =O[cocompact ℝ] fun x => x⁻¹ := by
  refine ((isBigO_refl (fun x : ℝ => x⁻¹) _).mul h).congr' ?_ (.of_forall fun x => mul_one _)
  filter_upwards [eventually_ne_zero_cocompact] with x hx
  rw [inv_mul_cancel_left₀ hx]

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
      have hsin : sin =O[cocompact ℝ] fun _ => (1 : ℝ) :=
        (isBigO_sin_sub_one 0).congr_left fun x => by rw [sub_zero]
      refine (hsin.mul (isBigO_refl (fun x : ℝ => x⁻¹) _)).congr' ?_ (.of_forall fun x => one_mul _)
      filter_upwards [eventually_ne_zero_cocompact] with x hx
      rw [zero_add, Nat.cast_one, one_mul, sin_sub_pi_div_two, sphericalBesselJ_one]
      field_simp
      ring
  | succ l ih =>
    refine ⟨ih.2, ?_⟩
    -- `x j_{l + 1}(x)` is bounded, so `(2 l + 3) j_{l + 1}(x) = O(1 / x)`
    have hj : sphericalBesselJ (l + 1) =O[cocompact ℝ] fun x => x⁻¹ :=
      isBigO_inv_of_isBigO_mul_one <| ((ih.2.trans (tendsto_inv_cocompact.isBigO_one ℝ)).add
        (isBigO_sin_sub_one _)).congr_left fun _ => sub_add_cancel _ _
    refine ((hj.const_mul_left (2 * l + 3)).sub ih.1).congr_left fun x => ?_
    -- the remainders obey the recurrence up to `(2 l + 3) j_{l + 1}(x)`
    have h := mul_sphericalBesselJ_add_two l x
    -- restate the index `l + 1 + 1` as `l + 2`, the form the two rewriting lemmas expect
    rw [show l + 1 + 1 = l + 2 by rfl, sin_sub_add_two_mul_pi_div_two, h]
    ring

/-- **The spherical Bessel functions decay like `1 / x`**: along `cocompact ℝ`,
`j_l(x) = O(1 / x)`. -/
theorem isBigO_sphericalBesselJ_inv_cocompact (l : ℕ) :
    sphericalBesselJ l =O[cocompact ℝ] fun x => x⁻¹ :=
  isBigO_inv_of_isBigO_mul_one <| (((isBigO_mul_sphericalBesselJ_sub_sin_inv_cocompact l).trans
    (tendsto_inv_cocompact.isBigO_one ℝ)).add (isBigO_sin_sub_one _)).congr_left
      fun _ => sub_add_cancel _ _

/-- Every spherical Bessel function tends to zero as `|x| → ∞`. -/
theorem tendsto_sphericalBesselJ_cocompact (l : ℕ) :
    Tendsto (sphericalBesselJ l) (cocompact ℝ) (𝓝 0) :=
  (isBigO_sphericalBesselJ_inv_cocompact l).trans_tendsto tendsto_inv_cocompact

/-- **The large-argument asymptotics of the spherical Bessel functions**: along `cocompact ℝ`,
`j_l(x) = sin (x - l π / 2) / x + O(1 / x ^ 2)`. -/
theorem isBigO_sphericalBesselJ_sub_sin_div_inv_sq_cocompact (l : ℕ) :
    (fun x => sphericalBesselJ l x - sin (x - l * (π / 2)) / x) =O[cocompact ℝ]
      fun x => (x ^ 2)⁻¹ := by
  refine ((isBigO_refl (fun x : ℝ => x⁻¹) _).mul
    (isBigO_mul_sphericalBesselJ_sub_sin_inv_cocompact l)).congr' ?_ ?_
  · filter_upwards [eventually_ne_zero_cocompact] with x hx
    field_simp
  · exact Eventually.of_forall fun x => by simp only [sq, mul_inv]

/-- **The large-argument asymptotics of the spherical Bessel functions**, in the form
`j_l(x) - sin (x - l π / 2) / x = o(1 / x)` along `cocompact ℝ`: the difference decays faster
than `1 / x`. -/
theorem isLittleO_sphericalBesselJ_sub_sin_div_inv_cocompact (l : ℕ) :
    (fun x => sphericalBesselJ l x - sin (x - l * (π / 2)) / x) =o[cocompact ℝ]
      fun x => x⁻¹ := by
  refine (isBigO_sphericalBesselJ_sub_sin_div_inv_sq_cocompact l).trans_isLittleO ?_
  have h : (fun x : ℝ => x⁻¹) =o[cocompact ℝ] fun _ => (1 : ℝ) :=
    isLittleO_one_iff ℝ |>.2 tendsto_inv_cocompact
  refine ((isBigO_refl (fun x : ℝ => x⁻¹) _).mul_isLittleO h).congr' ?_ ?_
  · exact Eventually.of_forall fun x => by simp only [sq, mul_inv]
  · exact Eventually.of_forall fun x => mul_one _

/-- **The large-argument asymptotics of the derivative**: along `cocompact ℝ`,
`j_l'(x) = cos (x - l π / 2) / x + O(1 / x ^ 2)`. -/
theorem isBigO_deriv_sphericalBesselJ_sub_cos_div_inv_sq_cocompact (l : ℕ) :
    (fun x => deriv (sphericalBesselJ l) x - cos (x - l * (π / 2)) / x) =O[cocompact ℝ]
      fun x => (x ^ 2)⁻¹ := by
  -- `j_l' = (l / x) j_l - j_{l + 1}` and `sin (x - (l + 1) π / 2) = -cos (x - l π / 2)`
  have h₁ : (fun x => (l : ℝ) * x⁻¹ * sphericalBesselJ l x) =O[cocompact ℝ]
      fun x => (x ^ 2)⁻¹ := by
    refine (((isBigO_refl (fun x : ℝ => x⁻¹) _).mul
      (isBigO_sphericalBesselJ_inv_cocompact l)).const_mul_left (l : ℝ)).congr ?_ ?_
    · exact fun x => by ring
    · exact fun x => by simp only [sq, mul_inv]
  refine (h₁.sub (isBigO_sphericalBesselJ_sub_sin_div_inv_sq_cocompact (l + 1))).congr' ?_
    (EventuallyEq.refl _ _)
  filter_upwards [eventually_ne_zero_cocompact] with x hx
  rw [deriv_sphericalBesselJ_of_ne_zero l hx,
    show x - ((l + 1 : ℕ) : ℝ) * (π / 2) = x - l * (π / 2) - π / 2 by push_cast; ring,
    sin_sub_pi_div_two]
  ring

end EpsilonEridani
