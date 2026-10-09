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

* `azimuthalAverage_eq_zero_of_areaForm`: the average annihilates the area form
  `ω(v,w) = v₁·w₂ − v₂·w₁`.  This is the mathematical statement that the
  `F₁₄` amplitude integrates to zero over circles — acceptance example 6 of
  the `TransverseMomentumDistributions` roadmap Layer 2.4.
* `azimuthalAverage_preserves_nonneg`: the average preserves the nonnegativity
  condition of `TMD.IsTmdDensity`.
* `azimuthalAverage_maps_to_Tmd`: the average of a vector-argument function
  yields a genuine `Tmd`.
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

/-! ## Transverse plane geometry -/

/-- The two-dimensional transverse plane in momentum space. -/
abbrev TransversePlane : Type := EuclideanSpace ℝ (Fin 2)

/-- Standard basis vector `e₁ = (1, 0)`. -/
noncomputable def e1 : TransversePlane := ![1, 0]

/-- Standard basis vector `e₂ = (0, 1)`. -/
noncomputable def e2 : TransversePlane := ![0, 1]

/-- The unit vector pointing at polar angle `θ` in the transverse plane. -/
noncomputable def unitVector (θ : ℝ) : TransversePlane :=
  ![cos θ, sin θ]

/-- The radial vector of radius `kT` at polar angle `θ`. -/
noncomputable def radialVector (kT : ℝ) (θ : ℝ) : TransversePlane :=
  kT • unitVector θ

/-! ## Area form and its annihilation -/

/-- The area form (symplectic form) on `TransversePlane`:
    `ω(v, w) = v₁·w₂ − v₂·w₁`. -/
noncomputable def areaForm (v w : TransversePlane) : ℝ :=
  v 0 * w 1 - v 1 * w 0

/-- The area form is alternating: `ω(v, v) = 0`. -/
lemma areaForm_self (v : TransversePlane) : areaForm v v = 0 := by
  dsimp [areaForm]
  ring

/-- The `θ`-derivative sign lemma: integrating `areaForm(radialVector kT θ, fixedVector)`
    over `θ ∈ [0, 2π)` gives zero.  The integrand is explicitly
    `(kT cos θ)·v₂ − (kT sin θ)·v₁ = kT·(v₂ cos θ − v₁ sin θ)`, which is a
    sinusoid and integrates to zero over a full period. -/
lemma integral_areaForm_radial_over_circle (kT : ℝ) (v : TransversePlane) :
    ∫ θ in (0 : ℝ)..(2 * π), areaForm (radialVector kT θ) v = 0 := by
  dsimp [areaForm, radialVector, unitVector]
  have hcos : ∫ θ in (0 : ℝ)..(2 * π), cos θ = 0 := by
    rw [integral_cos]
    ring
  have hsin : ∫ θ in (0 : ℝ)..(2 * π), sin θ = 0 := by
    rw [integral_sin]
    ring
  calc
    ∫ θ in (0 : ℝ)..(2 * π), (kT * cos θ) * (v 1) - (kT * sin θ) * (v 0) = 
      ∫ θ in (0 : ℝ)..(2 * π), (kT * (v 1) * cos θ - kT * (v 0) * sin θ) := by
      refine integral_congr fun θ _ => ?_
      ring
    _ = (∫ θ in (0 : ℝ)..(2 * π), kT * (v 1) * cos θ) -
        (∫ θ in (0 : ℝ)..(2 * π), kT * (v 0) * sin θ) := by
      rw [integral_sub]
      · exact IntervalIntegrable.const_mul (IntervalIntegrable.cos (a:=0) (b:=2*π)) _
      · exact IntervalIntegrable.const_mul (IntervalIntegrable.sin (a:=0) (b:=2*π)) _
    _ = kT * (v 1) * (∫ θ in (0 : ℝ)..(2 * π), cos θ) -
        kT * (v 0) * (∫ θ in (0 : ℝ)..(2 * π), sin θ) := by
      simp [integral_mul_const, integral_const_mul, mul_assoc]
    _ = kT * (v 1) * 0 - kT * (v 0) * 0 := by rw [hcos, hsin]
    _ = 0 := by ring

/-- The azimuthal average of `areaForm(·, v)` is zero for any fixed vector `v`.

    This is the cancellation that makes `F₁₄` vanish in semi-inclusive DIS:
    the area form carries a single power of the transverse momentum, so its
    angular integral over any circle is zero. -/
lemma azimuthalAverage_areaForm_eq_zero (v : TransversePlane) (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) :
    azimuthalAverage (fun w _ _ _ _ => areaForm w v) x kT Q2 ζ = 0 := by
  dsimp [azimuthalAverage]
  rw [integral_areaForm_radial_over_circle kT v]
  simp

/-! ## Core definitions -/

/-- The azimuthal average of a function `f : TransversePlane → ℝ → ℝ → ℝ → ℝ`
    at fixed `(x, kT, Q2, ζ)`.  This is `(1 / 2π)` times the integral over
    the polar angle `θ ∈ [0, 2π)`. -/
noncomputable def azimuthalAverage
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ)
    (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f (radialVector kT θ) x Q2 ζ

/-- Plain azimuthal average without the `x, Q2, ζ` arguments (for pure transverse-plane
    functions). -/
noncomputable def azimuthalAveragePure (f : TransversePlane → ℝ) (kT : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ θ in (0 : ℝ)..(2 * π), f (radialVector kT θ)

/-! ## Density preservation -/

/-- The azimuthal average preserves the positive-density condition: if the vector-
    argument function is everywhere nonnegative, so is its scalar average. -/
theorem azimuthalAverage_nonneg
    (f : TransversePlane → ℝ → ℝ → ℝ → ℝ)
    (hf : ∀ v x kT Q2 ζ, 0 ≤ f v x kT Q2 ζ)
    (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) :
    0 ≤ azimuthalAverage f x kT Q2 ζ := by
  dsimp [azimuthalAverage]
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg (fun θ _ => hf _ x kT Q2 ζ)

/-- `azimuthalAveragePure` preserves nonnegativity. -/
lemma azimuthalAveragePure_nonneg (f : TransversePlane → ℝ)
    (hf : ∀ v, 0 ≤ f v) (kT : ℝ) : 0 ≤ azimuthalAveragePure f kT := by
  dsimp [azimuthalAveragePure]
  refine mul_nonneg (by positivity) ?_
  refine integral_nonneg (fun θ _ => hf _)

/-! ## Mapping to `Tmd` -/

/-- Given a vector-argument TMD `Φ : TransversePlane → Flavor → ℝ → ℝ → ℝ → ℝ`
    (with arguments `(vector, i, x, Q2, ζ)`), produce the scalar-magnitude `Tmd`.

    The azimuthal average is defined per flavor; we apply it componentwise. -/
noncomputable def azimuthalTmd
    (Φ : TransversePlane → Flavor → ℝ → ℝ → ℝ → ℝ)
    (i : Flavor) (x : ℝ) (kT : ℝ) (Q2 ζ : ℝ) : ℝ :=
  azimuthalAverage (fun v _ _ _ _ => Φ v i x Q2 ζ) x kT Q2 ζ

/-- The azimuthal TMD satisfies the `IsTmdDensity` condition whenever the vector-
    argument function satisfies the density condition per slice. -/
lemma azimuthalTmd_isTmdDensity
    (Φ : TransversePlane → Flavor → ℝ → ℝ → ℝ → ℝ)
    (hΦ : ∀ v i x Q2 ζ, 0 ≤ Φ v i x Q2 ζ)
    (h_supportX : ∀ v i x kT Q2 ζ, x < 0 ∨ 1 < x → Φ v i x kT Q2 ζ = 0)
    (h_supportKT : ∀ v i x kT Q2 ζ, kT < 0 → Φ v i x kT Q2 ζ = 0) :
    IsTmdDensity (azimuthalTmd Φ) := by
  refine
    { supportX := ?_
      supportKT := ?_
      nonneg := ?_ }
  · intro i x kT Q2 ζ hx
    dsimp [azimuthalTmd, azimuthalAverage]
    have hzero : (fun (θ : ℝ) => Φ (radialVector kT θ) i x Q2 ζ) = fun _ => 0 := by
      ext θ
      apply h_supportX (radialVector kT θ) i x Q2 ζ hx
    simp [hzero]
  · intro i x kT Q2 ζ hkT
    dsimp [azimuthalTmd, azimuthalAverage]
    have hzero : (fun (θ : ℝ) => Φ (radialVector kT θ) i x Q2 ζ) = fun _ => 0 := by
      ext θ
      apply h_supportKT (radialVector kT θ) i x kT Q2 ζ hkT
    simp [hzero]
  · intro i x kT Q2 ζ hx0 hx1 hkT0
    apply azimuthalAverage_nonneg (fun v _ _ _ _ => Φ v i x Q2 ζ) ?_ x kT Q2 ζ
    intro v
    apply hΦ v i x kT Q2 ζ

/-! ## Support lemmas for the radial vector -/

/-- The unit vector has norm 1. -/
lemma unitVector_norm (θ : ℝ) : ‖unitVector θ‖ = 1 := by
  dsimp [unitVector]
  simp [PiLp.norm_eq, norm_euclideanSpace]

/-- The radial vector has norm `|kT|`. -/
lemma radialVector_norm (kT : ℝ) (θ : ℝ) : ‖radialVector kT θ‖ = |kT| := by
  dsimp [radialVector]
  rw [norm_smul, unitVector_norm, mul_one]

/-- For nonnegative `kT`, the radial vector has norm `kT`. -/
lemma radialVector_norm_of_nonneg (kT : ℝ) (hkT : 0 ≤ kT) (θ : ℝ) :
    ‖radialVector kT θ‖ = kT := by
  rw [radialVector_norm, abs_of_nonneg hkT]

end TMD
end Parton
end Particles
end EpsilonEridani
