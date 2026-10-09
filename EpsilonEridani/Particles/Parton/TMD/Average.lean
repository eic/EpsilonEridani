/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.TMD.Basic
public import EpsilonEridani.Particles.Parton.TMD.Reduction
/-!

# TMD Azimuthal Average

This module defines the azimuthal average — the circle average that maps a
vector-argument function on `TransversePlane` to a scalar-magnitude `Tmd`.

## Motivation

The transverse-momentum-dependent correlator (Layer 0.4 of the
`TransverseMomentumDistributions` roadmap) is a function on the two-dimensional
transverse plane `TransversePlane = EuclideanSpace ℝ (Fin 2)`.  Reducing it to a
`Tmd` requires summing over the circle of radius `|kT|`.  The azimuthal average
performs this sum and produces a function of the scalar magnitude `kT` alone.

## Key results

* `azimuthalAverage_areaForm_eq_zero`: the average annihilates the area form
  `ω(v,w) = v₁·w₂ − v₂·w₁`.  This is the mathematical statement that the
  `F₁₄` amplitude integrates to zero over circles — acceptance example 6 of
  the `TransverseMomentumDistributions` roadmap Layer 2.4.
* `azimuthalAverage_nonneg`: the average preserves the nonnegativity
  condition of `TMD.IsTmdDensity`.
* `azimuthalTmd_isTmdDensity`: the average of a vector-argument density
  yields a `Tmd` satisfying `IsTmdDensity`.
-/

@[expose] public section

noncomputable section

open Real
open Set
open MeasureTheory

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace TMD

variable {Flavor : Type}

/-! ## Transverse plane geometry -/

/-- The two-dimensional transverse plane in momentum space. -/
abbrev TransversePlane : Type := EuclideanSpace ℝ (Fin 2)

/-- Standard basis vector `e₁ = (1, 0)`. -/
noncomputable def e1 : TransversePlane := !₂[1, 0]

/-- Standard basis vector `e₂ = (0, 1)`. -/
noncomputable def e2 : TransversePlane := !₂[0, 1]

/-- The unit vector pointing at polar angle `θ` in the transverse plane. -/
noncomputable def unitVector (θ : ℝ) : TransversePlane :=
  !₂[cos θ, sin θ]

/-- The radial vector of radius `kT` at polar angle `θ`. -/
noncomputable def radialVector (kT : ℝ) (θ : ℝ) : TransversePlane :=
  kT • unitVector θ

/-! ## Core definitions -/

/-- The azimuthal average of a function `f : TransversePlane → ℝ → ℝ → ℝ → ℝ`
    (with arguments `(vector, x, Q2, ζ)`) at fixed `(x, kT, Q2, ζ)`.  This is
    `(1 / 2π)` times the integral over the polar angle `θ ∈ [0, 2π)` of `f` on the
    circle of radius `kT`. -/
noncomputable def azimuthalAverage
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ)
    (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f (radialVector kT θ) x Q2 ζ

/-- Plain azimuthal average without the `x, Q2, ζ` arguments (for pure transverse-plane
    functions). -/
noncomputable def azimuthalAveragePure (f : TransversePlane → ℝ) (kT : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f (radialVector kT θ)

/-! ## Area form and its annihilation -/

/-- The area form (symplectic form) on `TransversePlane`:
    `ω(v, w) = v₁·w₂ − v₂·w₁`. -/
noncomputable def areaForm (v w : TransversePlane) : ℝ :=
  v 0 * w 1 - v 1 * w 0

/-- The area form is alternating: `ω(v, v) = 0`. -/
lemma areaForm_self (v : TransversePlane) : areaForm v v = 0 := by
  dsimp [areaForm]
  ring

/-- Integrating `areaForm (radialVector kT θ) v` over `θ ∈ [0, 2π)` gives zero.  The
    integrand is explicitly `kT·(v₂ cos θ − v₁ sin θ)`, which is a sinusoid and
    integrates to zero over a full period. -/
lemma integral_areaForm_radial_over_circle (kT : ℝ) (v : TransversePlane) :
    ∫ θ in (0 : ℝ)..(2 * π), areaForm (radialVector kT θ) v = 0 := by
  have h : ∀ θ, areaForm (radialVector kT θ) v = kT * v 1 * cos θ - kT * v 0 * sin θ := by
    intro θ
    simp [areaForm, radialVector, unitVector]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_sub (continuous_cos.intervalIntegrable _ _ |>.const_mul _)
      (continuous_sin.intervalIntegrable _ _ |>.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos, integral_sin]
  simp

/-- The azimuthal average of `areaForm(·, v)` is zero for any fixed vector `v`.

    This is the cancellation that makes `F₁₄` vanish in semi-inclusive DIS:
    the area form carries a single power of the transverse momentum, so its
    angular integral over any circle is zero. -/
lemma azimuthalAverage_areaForm_eq_zero (v : TransversePlane) (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) :
    azimuthalAverage (fun w _ _ _ => areaForm w v) x kT Q2 ζ = 0 := by
  rw [azimuthalAverage, integral_areaForm_radial_over_circle kT v, mul_zero]

/-! ## Density preservation -/

/-- The azimuthal average preserves the positive-density condition: if the vector-
    argument function is everywhere nonnegative, so is its scalar average. -/
theorem azimuthalAverage_nonneg
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ v x Q2 ζ, 0 ≤ f v x Q2 ζ)
    (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) :
    0 ≤ azimuthalAverage f x kT Q2 ζ :=
  mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg (by positivity) fun _ _ => hf _ x Q2 ζ)

/-- `azimuthalAveragePure` preserves nonnegativity. -/
lemma azimuthalAveragePure_nonneg (f : TransversePlane → ℝ)
    (hf : ∀ v, 0 ≤ f v) (kT : ℝ) : 0 ≤ azimuthalAveragePure f kT :=
  mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by positivity) fun _ _ => hf _)

/-! ## Mapping to `Tmd` -/

/-- Given a vector-argument TMD `Φ : TransversePlane → Flavor → ℝ → ℝ → ℝ → ℝ`
    (with arguments `(vector, i, x, Q2, ζ)`), produce the scalar-magnitude `Tmd`.

    The azimuthal average is taken per flavor.  Since a `Tmd` is a function of the
    magnitude `kT`, it is set to zero at unphysical `kT < 0`. -/
noncomputable def azimuthalTmd
    (Φ : TransversePlane → Flavor → ℝ → ℝ → ℝ → ℝ) : Tmd Flavor :=
  fun i x kT Q2 ζ =>
    if kT < 0 then 0 else azimuthalAverage (fun v x Q2 ζ => Φ v i x Q2 ζ) x kT Q2 ζ

/-- The azimuthal TMD satisfies the `IsTmdDensity` condition whenever the vector-
    argument function is nonnegative and supported in `x ∈ [0, 1]`. -/
lemma azimuthalTmd_isTmdDensity
    (Φ : TransversePlane → Flavor → ℝ → ℝ → ℝ → ℝ)
    (hΦ : ∀ v i x Q2 ζ, 0 ≤ Φ v i x Q2 ζ)
    (h_supportX : ∀ v i x Q2 ζ, x < 0 ∨ 1 < x → Φ v i x Q2 ζ = 0) :
    IsTmdDensity (azimuthalTmd Φ) where
  supportX i x kT Q2 ζ hx := by
    simp [azimuthalTmd, azimuthalAverage, h_supportX _ i x Q2 ζ hx]
  supportKT i x kT Q2 ζ hkT := by
    simp [azimuthalTmd, hkT]
  nonneg i x kT Q2 ζ _ _ hkT := by
    simp only [azimuthalTmd, not_lt.mpr hkT, ite_false]
    exact azimuthalAverage_nonneg _ (fun v x Q2 ζ => hΦ v i x Q2 ζ) x kT Q2 ζ

/-! ## Support lemmas for the radial vector -/

/-- The unit vector has norm 1. -/
lemma unitVector_norm (θ : ℝ) : ‖unitVector θ‖ = 1 := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [unitVector, Real.cos_sq_add_sin_sq]

/-- The radial vector has norm `|kT|`. -/
lemma radialVector_norm (kT : ℝ) (θ : ℝ) : ‖radialVector kT θ‖ = |kT| := by
  rw [radialVector, norm_smul, unitVector_norm, mul_one, Real.norm_eq_abs]

/-- For nonnegative `kT`, the radial vector has norm `kT`. -/
lemma radialVector_norm_of_nonneg (kT : ℝ) (hkT : 0 ≤ kT) (θ : ℝ) :
    ‖radialVector kT θ‖ = kT := by
  rw [radialVector_norm, abs_of_nonneg hkT]

end TMD
end Parton
end Particles
end EpsilonEridani
