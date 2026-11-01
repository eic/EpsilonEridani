/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Mathematics.Normed.Operator.LinearIsometry
public import EpsilonEridani.Particles.Parton.GTMD.Transverse
public import EpsilonEridani.Particles.Parton.GTMD.Basic
public import EpsilonEridani.Particles.Parton.TMD.Basic
public import Mathlib.MeasureTheory.Integral.CircleAverage
/-!

# The azimuthal average

A `TMD.Tmd` is a function of the transverse-momentum *magnitude* `kT`, so it cannot express
any dependence on the direction of the transverse-momentum vector. A transverse-momentum
dependent distribution whose argument is a genuine vector in `Transverse` — a `VectorTmd`,
introduced in `EpsilonEridani.Particles.Parton.GTMD.Basic` — reaches `TMD.Tmd` by averaging
over the polar angle at fixed radius. This module makes that average explicit.

## Main definitions

* `circleAverageTransverse g kT`: the mean of `g : Transverse → E` over the circle of radius
  `kT` about the origin, i.e. Mathlib's `Real.circleAverage` transported to `Transverse`
  along `Complex.orthonormalBasisOneI.repr`. Following Mathlib's convention, it is `0` when
  `g` is not circle integrable.
* `azimuthalAverage`: the per-flavour circle average of a `VectorTmd`, a `TMD.Tmd`. The value
  is set to `0` at unphysical `kT < 0`, which is the only reason the average satisfies
  `TMD.IsTmdDensity.supportKT`; since the circle average is even in `kT`, this cutoff is a
  deliberate break of that symmetry, and `azimuthalAverage_of_neg`/`azimuthalAverage_of_nonneg`
  are the interface for it. The average also inherits the junk value `0` of
  `circleAverageTransverse` on non-integrable slices, which is why `IsVectorTmdDensity` needs
  no measurability or integrability condition.

## Main results

* `circleAverageTransverse_eq_integral`: the average is
  `(2π)⁻¹ • ∫₀^{2π} g (circleMapTransverse kT θ) dθ`.
* `circleAverageTransverse_const_on_circle`: the average of a function that is constant on
  the circle `‖w‖ = |kT|` is that constant.
* `Continuous.circleAverageTransverse`: the average of a continuous function is continuous in
  the radius.
* `circleAverageTransverse_eq_zero_of_odd`, `azimuthalAverage_eq_zero_of_odd`: the averages
  annihilate every function that is odd on the circle, in particular every linear map.
* `azimuthalAverage_of_neg`, `azimuthalAverage_of_nonneg`: the azimuthal average vanishes at
  negative transverse-momentum magnitude and is the circle average at nonnegative magnitude —
  the interface to the `kT < 0` cutoff of `azimuthalAverage`.
* `azimuthalAverage_comp_norm`: averaging a function of the magnitude alone returns that
  function at nonnegative transverse-momentum magnitude, so the average retracts the radial
  inclusion on TMDs vanishing at negative magnitude, `TMD.IsTmdDensity` in particular.
* `isTmdDensity_azimuthalAverage`, `regularity_azimuthalAverage`,
  `assumptions_azimuthalAverage`: the azimuthal average of a vector-argument density is a
  density in the sense of `TMD.IsTmdDensity`, is regular in the sense of `TMD.Regularity`, and
  satisfies the full `TMD.Assumptions` bundle, so it can be used with every consumer that
  takes one.

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

variable {Flavor : Type} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The circle average on the transverse plane -/

/-- The mean of `g` over the circle of radius `kT` about the origin of the transverse plane:
    Mathlib's `Real.circleAverage` transported along `Complex.orthonormalBasisOneI.repr`.
    Following Mathlib's convention, the value is `0` when
    `fun z => g (Complex.orthonormalBasisOneI.repr z)` is not circle integrable, so the
    identification with the mean requires circle integrability. -/
def circleAverageTransverse (g : Transverse → E) (kT : ℝ) : E :=
  Real.circleAverage (fun z => g (Complex.orthonormalBasisOneI.repr z)) 0 kT

/-- The circle average on the transverse plane is Mathlib's `Real.circleAverage` of the
    function read in the coordinates `Complex.orthonormalBasisOneI`. -/
lemma circleAverageTransverse_def (g : Transverse → E) (kT : ℝ) :
    circleAverageTransverse g kT =
      Real.circleAverage (fun z => g (Complex.orthonormalBasisOneI.repr z)) 0 kT :=
  (rfl)
  -- `(rfl)`, not `rfl`: a syntactic `rfl` proof would implicitly tag the lemma `@[defeq]`,
  -- which would let `dsimp` unfold `circleAverageTransverse` downstream.

/-- The circle average is `(2π)⁻¹` times the integral of `g` along `circleMapTransverse kT`
    over the polar angle `θ ∈ [0, 2π]`. -/
lemma circleAverageTransverse_eq_integral (g : Transverse → E) (kT : ℝ) :
    circleAverageTransverse g kT =
      (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), g (circleMapTransverse kT θ) := by
  rw [circleAverageTransverse_def, Real.circleAverage_def]
  simp only [circleMapTransverse]

/-- The circle average does not change when the radius is replaced by its negative. -/
@[simp]
lemma circleAverageTransverse_neg_radius (g : Transverse → E) (kT : ℝ) :
    circleAverageTransverse g (-kT) = circleAverageTransverse g kT := by
  simp only [circleAverageTransverse_def]
  exact Real.circleAverage_neg_radius

/-- The circle average does not change when the radius is replaced by its absolute value. -/
@[simp]
lemma circleAverageTransverse_abs_radius (g : Transverse → E) (kT : ℝ) :
    circleAverageTransverse g |kT| = circleAverageTransverse g kT := by
  simp only [circleAverageTransverse_def]
  exact Real.circleAverage_abs_radius

/-- The circle average at zero radius is the value at the origin. -/
@[simp]
lemma circleAverageTransverse_zero_radius [CompleteSpace E] (g : Transverse → E) :
    circleAverageTransverse g 0 = g 0 := by
  rw [circleAverageTransverse_def, Real.circleAverage_zero, map_zero]

/-- The circle average of a function that is constant on the circle `‖w‖ = |kT|` is that
    constant. -/
lemma circleAverageTransverse_const_on_circle [CompleteSpace E] {g : Transverse → E} {c : E}
    {kT : ℝ} (h : ∀ w, ‖w‖ = |kT| → g w = c) :
    circleAverageTransverse g kT = c := by
  rw [circleAverageTransverse_def]
  exact Real.circleAverage_const_on_circle fun z hz =>
    h _ (SemilinearIsometryClass.norm_map_of_mem_sphere_zero
      Complex.orthonormalBasisOneI.repr hz)

/-- The circle average of a function nonnegative on the circle `‖w‖ = |kT|` is nonnegative. -/
lemma circleAverageTransverse_nonneg_of_nonneg {g : Transverse → ℝ} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → 0 ≤ g w) : 0 ≤ circleAverageTransverse g kT := by
  rw [circleAverageTransverse_def]
  exact Real.circleAverage_nonneg_of_nonneg fun z hz =>
    hg _ (SemilinearIsometryClass.norm_map_of_mem_sphere_zero
      Complex.orthonormalBasisOneI.repr hz)

/-- The circle average of a function odd on the circle `‖w‖ = |kT|` vanishes. -/
lemma circleAverageTransverse_eq_zero_of_odd {g : Transverse → E} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → g (-w) = -g w) :
    circleAverageTransverse g kT = 0 := by
  have hodd : ∀ θ, g (circleMapTransverse (-kT) θ) = -g (circleMapTransverse kT θ) := fun θ => by
    rw [circleMapTransverse_neg_radius, hg _ (norm_circleMapTransverse kT θ)]
  have h := circleAverageTransverse_neg_radius g kT
  rw [circleAverageTransverse_eq_integral, circleAverageTransverse_eq_integral] at h
  simp_rw [hodd, intervalIntegral.integral_neg, smul_neg] at h
  rw [circleAverageTransverse_eq_integral]
  linear_combination (norm := module) (-2⁻¹ : ℝ) • h

end GTMD
end Parton
end Particles
end EpsilonEridani

open EpsilonEridani.Particles.Parton.GTMD in
/-- The circle average of a continuous function is continuous in the radius: the transverse
    transport of Mathlib's `Continuous.circleAverage`, which is what carries continuity of the
    transverse-momentum slices of a `VectorTmd` to regularity of their azimuthal average. -/
lemma Continuous.circleAverageTransverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Transverse → E} (hg : Continuous g) : Continuous (circleAverageTransverse g) :=
  (((hg.comp Complex.orthonormalBasisOneI.repr.continuous).circleAverage (c := 0)).congr
    fun kT => (circleAverageTransverse_def g kT).symm)

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

variable {Flavor : Type} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The azimuthal average of a vector-argument TMD -/

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

/-- The azimuthal average annihilates every vector-argument TMD that is odd in its
    transverse-momentum argument on the circle `‖w‖ = |kT|`. -/
lemma azimuthalAverage_eq_zero_of_odd (f : VectorTmd Flavor) (i : Flavor) {x kT Q2 ζ : ℝ}
    (hf : ∀ w, ‖w‖ = |kT| → f i x (-w) Q2 ζ = -f i x w Q2 ζ) :
    azimuthalAverage f i x kT Q2 ζ = 0 := by
  rcases lt_or_ge kT 0 with hkT | hkT
  · exact azimuthalAverage_of_neg f i hkT
  · rw [azimuthalAverage_of_nonneg f i hkT]
    exact circleAverageTransverse_eq_zero_of_odd hf

/-- The azimuthal average at zero transverse momentum is the value at the origin. -/
@[simp]
lemma azimuthalAverage_zero_radius (f : VectorTmd Flavor) (i : Flavor) (x Q2 ζ : ℝ) :
    azimuthalAverage f i x 0 Q2 ζ = f i x 0 Q2 ζ := by
  rw [azimuthalAverage_of_nonneg f i (kT := 0) le_rfl, circleAverageTransverse_zero_radius]

/-- Averaging a function of the magnitude alone returns that function at nonnegative
    transverse-momentum magnitude. Together with vanishing at negative magnitude — which every
    `TMD.IsTmdDensity` guarantees — this says that the azimuthal average retracts the radial
    inclusion `g ↦ fun i x w Q2 ζ => g i x ‖w‖ Q2 ζ` of `TMD.Tmd` into `VectorTmd`. -/
lemma azimuthalAverage_comp_norm (g : TMD.Tmd Flavor) (i : Flavor) {x kT Q2 ζ : ℝ}
    (hkT : 0 ≤ kT) :
    azimuthalAverage (fun i x w Q2 ζ => g i x ‖w‖ Q2 ζ) i x kT Q2 ζ = g i x kT Q2 ζ := by
  rw [azimuthalAverage_of_nonneg _ i hkT]
  exact circleAverageTransverse_const_on_circle fun w hw => by rw [hw, abs_of_nonneg hkT]

/-- The azimuthal average of a vector-argument density is a density in the sense of
    `TMD.IsTmdDensity`. -/
theorem isTmdDensity_azimuthalAverage {f : VectorTmd Flavor} (hf : IsVectorTmdDensity f) :
    TMD.IsTmdDensity (azimuthalAverage f) where
  supportX i x kT Q2 ζ hx := by
    rcases lt_or_ge kT 0 with hkT | hkT
    · exact azimuthalAverage_of_neg f i hkT
    · rw [azimuthalAverage_of_nonneg f i hkT]
      exact circleAverageTransverse_const_on_circle fun w _ => hf.supportX i x w Q2 ζ hx
  supportKT i x kT Q2 ζ hkT := azimuthalAverage_of_neg f i hkT
  nonneg i x kT Q2 ζ hx0 hx1 hkT := by
    rw [azimuthalAverage_of_nonneg f i hkT]
    exact circleAverageTransverse_nonneg_of_nonneg fun w _ => hf.nonneg i x w Q2 ζ hx0 hx1

/-- The azimuthal average of a regular vector-argument TMD is regular in the sense of
    `TMD.Regularity`: continuity of every transverse-momentum slice gives measurability of
    the averaged function in the transverse-momentum magnitude. -/
theorem regularity_azimuthalAverage {f : VectorTmd Flavor} (hf : VectorTmd.Regularity f) :
    TMD.Regularity (azimuthalAverage f) where
  measurableKT i x Q2 ζ := by
    have hc : Continuous (circleAverageTransverse (f i x · Q2 ζ)) :=
      (hf.continuousKT i x Q2 ζ).circleAverageTransverse
    have hite : MeasureTheory.AEStronglyMeasurable (fun kT : ℝ =>
        if kT < 0 then (0 : ℝ) else circleAverageTransverse (f i x · Q2 ζ) kT) :=
      (Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const hc.measurable).aestronglyMeasurable
    simpa only [azimuthalAverage] using hite

/-- The azimuthal average of a vector-argument TMD satisfying the full assumption bundle
    satisfies the full `TMD.Assumptions` bundle, so it can be used with every consumer that
    takes one. -/
theorem assumptions_azimuthalAverage {f : VectorTmd Flavor} (hf : VectorTmd.Assumptions f) :
    TMD.Assumptions (azimuthalAverage f) :=
  TMD.assumptions_iff.mpr ⟨isTmdDensity_azimuthalAverage hf.toIsVectorTmdDensity,
    regularity_azimuthalAverage hf.toRegularity⟩

end GTMD
end Parton
end Particles
end EpsilonEridani
