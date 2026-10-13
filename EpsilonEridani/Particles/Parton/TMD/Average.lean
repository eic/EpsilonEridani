/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.TMD.Basic
public import EpsilonEridani.Particles.Parton.TMD.Reduction
public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import Mathlib.MeasureTheory.Integral.CircleAverage
/-!

# TMD Azimuthal Average

This module defines the azimuthal average — the circle average that maps a
vector-argument function on `TransversePlane` to a scalar-magnitude `Tmd`.

## Motivation

Layer 2.4 of the `WignerDistributions` roadmap asks for the azimuthal average of a
vector-argument TMD, a function on the two-dimensional transverse plane
`TransversePlane = EuclideanSpace ℝ (Fin 2)`, landing in the magnitude-valued `Tmd`.
The average is Mathlib's `Real.circleAverage`, transported to `TransversePlane` along
`Complex.orthonormalBasisOneI.repr`.

## Key results

* `azimuthalAverage_eq_zero_of_odd`: the average annihilates every function odd in the
  transverse vector.
* `azimuthalAverage_areaForm_eq_zero`: in particular it annihilates the area form
  `w ↦ ω(w, v)` of any orientation of the transverse plane.  This is the area-form
  ingredient of the `F₁₄` annihilation in Layer 2.4 of the `WignerDistributions` roadmap;
  the `F₁₄` amplitude itself is not defined here.
* `azimuthalAverage_nonneg`: the average preserves the nonnegativity
  condition of `TMD.IsTmdDensity`.
* `azimuthalTmd_isTmdDensity`: the average of a vector-argument density
  yields a `Tmd` satisfying `IsTmdDensity`.
-/

@[expose] public section

noncomputable section

open Real
open scoped EuclideanSpace

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace TMD

variable {Flavor : Type}

/-! ## Transverse plane geometry -/

/-- The two-dimensional transverse plane in momentum space. -/
abbrev TransversePlane : Type := EuclideanSpace ℝ (Fin 2)

/-- The radial vector of radius `kT` at polar angle `θ` in the transverse plane:
    `circleMap 0 kT θ` read in the coordinates `Complex.orthonormalBasisOneI`. -/
noncomputable def radialVector (kT : ℝ) (θ : ℝ) : TransversePlane :=
  Complex.orthonormalBasisOneI.repr (circleMap 0 kT θ)

/-- The radial vector has norm `|kT|`. -/
lemma radialVector_norm (kT : ℝ) (θ : ℝ) : ‖radialVector kT θ‖ = |kT| := by
  rw [radialVector, LinearIsometryEquiv.norm_map, norm_circleMap_zero]

/-- For nonnegative `kT`, the radial vector has norm `kT`. -/
lemma radialVector_norm_of_nonneg (kT : ℝ) (hkT : 0 ≤ kT) (θ : ℝ) :
    ‖radialVector kT θ‖ = kT := by
  rw [radialVector_norm, abs_of_nonneg hkT]

/-! ## Core definitions -/

/-- The azimuthal average of a function `f : TransversePlane → ℝ → ℝ → ℝ → ℝ`
    (with arguments `(vector, x, Q2, ζ)`) at fixed `(x, kT, Q2, ζ)`: the circle average
    of `f` over the circle of radius `kT` centred at the origin. -/
noncomputable def azimuthalAverage
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ)
    (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) : ℝ :=
  Real.circleAverage (fun z => f (Complex.orthonormalBasisOneI.repr z) x Q2 ζ) 0 kT

/-- The azimuthal average is `(1 / 2π)` times the integral of `f` along the radial vector
    over the polar angle `θ ∈ [0, 2π]`. -/
lemma azimuthalAverage_eq_integral
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ) (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) :
    azimuthalAverage f x kT Q2 ζ =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), f (radialVector kT θ) x Q2 ζ :=
  Real.circleAverage_def

/-! ## Annihilation of odd functions and of the area form -/

/-- The azimuthal average of a function odd in the transverse vector vanishes. -/
lemma azimuthalAverage_eq_zero_of_odd
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ) (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ)
    (hf : ∀ w, f (-w) x Q2 ζ = -f w x Q2 ζ) :
    azimuthalAverage f x kT Q2 ζ = 0 := by
  have h : azimuthalAverage f x kT Q2 ζ = -azimuthalAverage f x kT Q2 ζ := by
    conv_lhs => rw [azimuthalAverage, ← Real.circleAverage_neg_radius]
    have hneg : ∀ θ, circleMap 0 (-kT) θ = -circleMap 0 kT θ := fun θ => by
      simp [circleMap]
    simp_rw [azimuthalAverage, Real.circleAverage_def, hneg, map_neg, hf,
      intervalIntegral.integral_neg, smul_neg]
  linarith

/-- The azimuthal average of `w ↦ ω(w, v)` is zero, for the area form `ω` of any
    orientation of the transverse plane and any fixed vector `v`. -/
lemma azimuthalAverage_areaForm_eq_zero
    (o : Orientation ℝ TransversePlane (Fin 2))
    (v : TransversePlane) (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) :
    azimuthalAverage (fun w _ _ _ => o.areaForm w v) x kT Q2 ζ = 0 :=
  azimuthalAverage_eq_zero_of_odd _ x kT Q2 ζ fun w => by simp

/-! ## Density preservation -/

/-- The azimuthal average preserves the positive-density condition: if the vector-
    argument function is everywhere nonnegative, so is its scalar average. -/
theorem azimuthalAverage_nonneg
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ v x Q2 ζ, 0 ≤ f v x Q2 ζ)
    (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) :
    0 ≤ azimuthalAverage f x kT Q2 ζ :=
  Real.circleAverage_nonneg_of_nonneg fun _ _ => hf _ _ _ _

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
    simp [azimuthalTmd, azimuthalAverage, h_supportX _ i x Q2 ζ hx, Real.circleAverage_def]
  supportKT i x kT Q2 ζ hkT := by
    simp [azimuthalTmd, hkT]
  nonneg i x kT Q2 ζ _ _ hkT := by
    simp only [azimuthalTmd, not_lt.mpr hkT, ite_false]
    exact azimuthalAverage_nonneg _ (fun v x Q2 ζ => hΦ v i x Q2 ζ) x kT Q2 ζ

end TMD
end Parton
end Particles
end EpsilonEridani
