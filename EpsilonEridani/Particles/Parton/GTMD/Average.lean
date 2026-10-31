/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.LinearIsometry.Sphere
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

* `circleAverageTransverse g kT`: the mean of `g : Transverse → E` over the circle of radius
  `kT` about the origin, i.e. Mathlib's `Real.circleAverage` transported to `Transverse`
  along `Complex.orthonormalBasisOneI.repr`. Following Mathlib's convention, it is `0` when
  `g` is not circle integrable.
* `VectorTmd`: a transverse-momentum dependent distribution whose transverse-momentum
  argument is a vector in `Transverse`.
* `IsVectorTmdDensity`: the vector-argument analogue of `TMD.IsTmdDensity`.
* `Regularity`: the vector-argument analogue of `TMD.Regularity`, the analytic half of the
  assumption bundle: continuity of every transverse-momentum slice.
* `Assumptions`: the full vector-argument assumption bundle, the physical conditions of
  `IsVectorTmdDensity` together with the analytic condition of `Regularity`.
* `azimuthalAverage`: the per-flavour circle average of a `VectorTmd`, a `TMD.Tmd`. It inherits
  the junk value `0` of `circleAverageTransverse` on non-integrable slices, which is why
  `IsVectorTmdDensity` needs no measurability or integrability condition.

## Main results

* `circleAverageTransverse_eq_integral`: the average is
  `(2π)⁻¹ • ∫₀^{2π} g (circleMapTransverse kT θ) dθ`.
* `circleAverageTransverse_const_on_circle`: the average of a function that is constant on
  the circle `‖w‖ = |kT|` is that constant.
* `circleAverageTransverse_eq_zero_of_odd`, `azimuthalAverage_eq_zero_of_odd`: the averages
  annihilate every function that is odd on the circle, in particular every linear map.
* `azimuthalAverage_comp_norm`: averaging a function of the magnitude alone returns that
  function.
* `isTmdDensity_azimuthalAverage`, `regularity_azimuthalAverage`,
  `assumptions_azimuthalAverage`: the azimuthal average of a vector-argument density is a
  density in the sense of `TMD.IsTmdDensity`, is regular in the sense of `TMD.Regularity`, and
  satisfies the full `TMD.Assumptions` bundle, so it can be used with every consumer that
  takes one.
* `assumptions_iff`: the split of the vector-argument assumption bundle into its physical and
  analytic halves is exact.

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
    circleAverageTransverse g (-kT) = circleAverageTransverse g kT :=
  Real.circleAverage_neg_radius

/-- The circle average does not change when the radius is replaced by its absolute value. -/
@[simp]
lemma circleAverageTransverse_abs_radius (g : Transverse → E) (kT : ℝ) :
    circleAverageTransverse g |kT| = circleAverageTransverse g kT :=
  Real.circleAverage_abs_radius

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
    h _ (Complex.orthonormalBasisOneI.repr.norm_map_of_mem_sphere_zero hz)

/-- The circle average of a function nonnegative on the circle `‖w‖ = |kT|` is nonnegative. -/
lemma circleAverageTransverse_nonneg_of_nonneg {g : Transverse → ℝ} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → 0 ≤ g w) : 0 ≤ circleAverageTransverse g kT := by
  rw [circleAverageTransverse_def]
  exact Real.circleAverage_nonneg_of_nonneg fun z hz =>
    hg _ (Complex.orthonormalBasisOneI.repr.norm_map_of_mem_sphere_zero hz)

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

/-! ### The analytic/physical split of `Assumptions`

As in the transverse-magnitude case (`EpsilonEridani.Particles.Parton.TMD.Assumptions`) the
bundle mixes a definition with an obligation. `IsVectorTmdDensity` is the physical half —
support in `x` and nonnegativity on the physical region — and is what "vector-argument
transverse-momentum-dependent parton density" means. `Regularity` is the analytic half,
continuity of the transverse-momentum slices; it is what transports to measurability of the
azimuthal average in the transverse-momentum magnitude (`regularity_azimuthalAverage` below).
`assumptions_iff` records that the split is exact.
-/

/-- **The analytic half of the vector-argument assumption bundle**: continuity of every
    transverse-momentum slice. -/
structure Regularity (f : VectorTmd Flavor) : Prop where
  /-- `f i x · Q2 ζ` is continuous as a function of the transverse-momentum vector. -/
  continuousKT : ∀ i x Q2 ζ, Continuous (fun w : Transverse => f i x w Q2 ζ)

/-- Structural assumptions for vector-argument TMD objects: the physical conditions of
    `IsVectorTmdDensity` together with the analytic condition of `Regularity`. -/
structure Assumptions (f : VectorTmd Flavor) : Prop where
  /-- The density vanishes outside the physical range `[0, 1]` of the momentum fraction. -/
  supportX : ∀ i x kT Q2 ζ, x < 0 ∨ 1 < x → f i x kT Q2 ζ = 0
  /-- The density is nonnegative on the physical range of the momentum fraction. -/
  nonneg : ∀ i x kT Q2 ζ, 0 ≤ x → x ≤ 1 → 0 ≤ f i x kT Q2 ζ
  /-- `f i x · Q2 ζ` is continuous as a function of the transverse-momentum vector. -/
  continuousKT : ∀ i x Q2 ζ, Continuous (fun w : Transverse => f i x w Q2 ζ)

/-- The physical half of a full vector-argument assumption bundle. -/
lemma Assumptions.isVectorTmdDensity {f : VectorTmd Flavor} (h : Assumptions f) :
    IsVectorTmdDensity f :=
  { supportX := h.supportX, nonneg := h.nonneg }

/-- The analytic half of a full vector-argument assumption bundle. -/
lemma Assumptions.regularity {f : VectorTmd Flavor} (h : Assumptions f) :
    Regularity f :=
  { continuousKT := h.continuousKT }

/-- The split is exact: `Assumptions` is the conjunction of the physical and the analytic
    half, with no residue. -/
lemma assumptions_iff {f : VectorTmd Flavor} :
    Assumptions f ↔ IsVectorTmdDensity f ∧ Regularity f :=
  ⟨fun h => ⟨h.isVectorTmdDensity, h.regularity⟩, fun h =>
    { supportX := h.1.supportX
      nonneg := h.1.nonneg
      continuousKT := h.2.continuousKT }⟩

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

/-- Averaging a function of the magnitude alone returns that function: the azimuthal average
    is a retraction of the radial inclusion `g ↦ fun i x w Q2 ζ => g i x ‖w‖ Q2 ζ` of
    `TMD.Tmd` into `VectorTmd`. -/
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
theorem regularity_azimuthalAverage {f : VectorTmd Flavor} (hf : Regularity f) :
    TMD.Regularity (azimuthalAverage f) where
  measurableKT i x Q2 ζ := by
    have hslice : Continuous (fun z : ℂ =>
        f i x (Complex.orthonormalBasisOneI.repr z) Q2 ζ) :=
      (hf.continuousKT i x Q2 ζ).comp Complex.orthonormalBasisOneI.repr.continuous
    have hc : Continuous (fun kT : ℝ => circleAverageTransverse (f i x · Q2 ζ) kT) :=
      (hslice.circleAverage (c := 0)).congr fun kT =>
        (circleAverageTransverse_def (f i x · Q2 ζ) kT).symm
    have hite : MeasureTheory.AEStronglyMeasurable (fun kT : ℝ =>
        if kT < 0 then (0 : ℝ) else circleAverageTransverse (f i x · Q2 ζ) kT) :=
      (Measurable.ite (measurableSet_lt measurable_id measurable_const)
        measurable_const hc.measurable).aestronglyMeasurable
    simpa only [azimuthalAverage] using hite

/-- The azimuthal average of a vector-argument TMD satisfying the full assumption bundle
    satisfies the full `TMD.Assumptions` bundle, so it can be used with every consumer that
    takes one. -/
theorem assumptions_azimuthalAverage {f : VectorTmd Flavor} (hf : Assumptions f) :
    TMD.Assumptions (azimuthalAverage f) :=
  TMD.assumptions_iff.mpr ⟨isTmdDensity_azimuthalAverage hf.isVectorTmdDensity,
    regularity_azimuthalAverage hf.regularity⟩

end GTMD
end Parton
end Particles
end EpsilonEridani
