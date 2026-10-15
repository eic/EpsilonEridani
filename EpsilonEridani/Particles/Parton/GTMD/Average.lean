/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.GTMD.Transverse
public import EpsilonEridani.Particles.Parton.TMD.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
/-!

# The azimuthal average

A `TMD.Tmd` is a function of the transverse-momentum *magnitude* `kT`, so it cannot express
any dependence on the direction of the transverse-momentum vector. A transverse-momentum
dependent distribution whose argument is a genuine vector in `Transverse` reaches `TMD.Tmd`
by averaging over the polar angle at fixed radius. This module makes that average explicit.

## Main definitions

* `circleAverageTransverse g kT`: the mean of `g : Transverse → ℝ` over the circle of radius
  `kT` about the origin, i.e. Mathlib's `Real.circleAverage` transported to `Transverse`
  along `Complex.orthonormalBasisOneI.repr`.
* `VectorTmd`: a transverse-momentum dependent distribution whose transverse-momentum
  argument is a vector in `Transverse`.
* `IsVectorTmdDensity`: the vector-argument analogue of `TMD.IsTmdDensity`.
* `azimuthalAverage`: the per-flavour circle average of a `VectorTmd`, a `TMD.Tmd`.

## Main results

* `circleAverageTransverse_eq_integral`: the average is `(2π)⁻¹ ∫₀^{2π} g (radialVector kT θ) dθ`.
* `circleAverageTransverse_eq_zero_of_odd`: the average annihilates every function that is odd
  on the circle, in particular every linear functional.
* `isTmdDensity_azimuthalAverage`: the azimuthal average of a vector-argument density is a
  density in the sense of `TMD.IsTmdDensity`.

## References

* S. Meissner, A. Metz and M. Schlegel, *Generalized parton correlation functions for a spin-1/2
  hadron*, JHEP **08** (2009) 056, arXiv:0906.5323.
* C. Lorcé, B. Pasquini and M. Vanderhaeghen, *Unified framework for generalized and
  transverse-momentum dependent parton distributions within a 3Q light-cone picture of the
  nucleon*, JHEP **05** (2011) 041, arXiv:1102.4704.
-/

@[expose] public section

noncomputable section

open Real

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

variable {Flavor : Type}

/-! ## The circle average on the transverse plane -/

/-- The mean of `g` over the circle of radius `kT` about the origin of the transverse plane:
    Mathlib's `Real.circleAverage` transported along `Complex.orthonormalBasisOneI.repr`. -/
def circleAverageTransverse (g : Transverse → ℝ) (kT : ℝ) : ℝ :=
  Real.circleAverage (fun z => g (Complex.orthonormalBasisOneI.repr z)) 0 kT

/-- The circle average is `(2π)⁻¹` times the integral of `g` along the radial vector over the
    polar angle `θ ∈ [0, 2π]`. -/
lemma circleAverageTransverse_eq_integral (g : Transverse → ℝ) (kT : ℝ) :
    circleAverageTransverse g kT =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), g (radialVector kT θ) := by
  rw [circleAverageTransverse, Real.circleAverage_def, smul_eq_mul]
  simp only [radialVector]

/-- The circle average does not change when the radius is replaced by its negative. -/
@[simp]
lemma circleAverageTransverse_neg_radius (g : Transverse → ℝ) (kT : ℝ) :
    circleAverageTransverse g (-kT) = circleAverageTransverse g kT :=
  Real.circleAverage_neg_radius

/-- The circle average of the zero function vanishes. -/
@[simp]
lemma circleAverageTransverse_zero (kT : ℝ) : circleAverageTransverse 0 kT = 0 := by
  simp [circleAverageTransverse, Real.circleAverage_const]

/-- The circle average of a function odd on the circle `‖w‖ = |kT|` vanishes. -/
lemma circleAverageTransverse_eq_zero_of_odd {g : Transverse → ℝ} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → g (-w) = -g w) :
    circleAverageTransverse g kT = 0 := by
  have hodd : ∀ θ, g (radialVector (-kT) θ) = -g (radialVector kT θ) := fun θ => by
    rw [radialVector_neg, hg _ (norm_radialVector kT θ)]
  have h := circleAverageTransverse_neg_radius g kT
  rw [circleAverageTransverse_eq_integral, circleAverageTransverse_eq_integral] at h
  simp_rw [hodd, intervalIntegral.integral_neg] at h
  rw [circleAverageTransverse_eq_integral]
  linarith

/-! ## Vector-argument TMDs and their azimuthal average -/

/-- A transverse-momentum dependent distribution `f i x kT Q2 ζ` whose transverse-momentum
    argument `kT` is a vector in the transverse plane rather than a magnitude. -/
abbrev VectorTmd (Flavor : Type) : Type := Flavor → ℝ → Transverse → ℝ → ℝ → ℝ

/-- The vector-argument analogue of `TMD.IsTmdDensity`: support in `x ∈ [0, 1]` and
    nonnegativity there. -/
structure IsVectorTmdDensity (f : VectorTmd Flavor) : Prop where
  /-- The density vanishes outside the physical range `[0, 1]` of the momentum fraction. -/
  supportX : ∀ i x kT Q2 ζ, x < 0 ∨ 1 < x → f i x kT Q2 ζ = 0
  /-- The density is nonnegative on the physical range of the momentum fraction. -/
  nonneg : ∀ i x kT Q2 ζ, 0 ≤ x → x ≤ 1 → 0 ≤ f i x kT Q2 ζ

/-- The azimuthal average of a vector-argument TMD: per flavour, the circle average of
    `f i x · Q2 ζ` over the circle of radius `kT`. Since a `TMD.Tmd` is a function of the
    magnitude `kT`, it is set to zero at unphysical `kT < 0`. -/
def azimuthalAverage (f : VectorTmd Flavor) : TMD.Tmd Flavor :=
  fun i x kT Q2 ζ => if kT < 0 then 0 else circleAverageTransverse (f i x · Q2 ζ) kT

/-- The azimuthal average vanishes at negative transverse-momentum magnitude. -/
@[simp]
lemma azimuthalAverage_of_neg (f : VectorTmd Flavor) (i : Flavor) {x kT Q2 ζ : ℝ}
    (hkT : kT < 0) : azimuthalAverage f i x kT Q2 ζ = 0 := by
  simp [azimuthalAverage, hkT]

/-- At nonnegative transverse-momentum magnitude, the azimuthal average is the circle average. -/
lemma azimuthalAverage_of_nonneg (f : VectorTmd Flavor) (i : Flavor) {x kT Q2 ζ : ℝ}
    (hkT : 0 ≤ kT) :
    azimuthalAverage f i x kT Q2 ζ = circleAverageTransverse (f i x · Q2 ζ) kT := by
  simp [azimuthalAverage, not_lt.mpr hkT]

/-- The azimuthal average of a vector-argument density is a density in the sense of
    `TMD.IsTmdDensity`. -/
theorem isTmdDensity_azimuthalAverage {f : VectorTmd Flavor} (hf : IsVectorTmdDensity f) :
    TMD.IsTmdDensity (azimuthalAverage f) where
  supportX i x kT Q2 ζ hx := by
    rcases lt_or_ge kT 0 with hkT | hkT
    · exact azimuthalAverage_of_neg f i hkT
    · have h0 : (f i x · Q2 ζ) = 0 := funext fun v => hf.supportX i x v Q2 ζ hx
      rw [azimuthalAverage_of_nonneg f i hkT, h0, circleAverageTransverse_zero]
  supportKT i x kT Q2 ζ hkT := azimuthalAverage_of_neg f i hkT
  nonneg i x kT Q2 ζ hx0 hx1 hkT := by
    rw [azimuthalAverage_of_nonneg f i hkT]
    exact Real.circleAverage_nonneg_of_nonneg fun _ _ => hf.nonneg i x _ Q2 ζ hx0 hx1

end GTMD
end Parton
end Particles
end EpsilonEridani
