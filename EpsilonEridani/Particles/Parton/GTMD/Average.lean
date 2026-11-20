/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.GTMD.CircleAverage
public import EpsilonEridani.Particles.Parton.GTMD.Basic
public import EpsilonEridani.Particles.Parton.TMD.Basic
/-!

# The azimuthal average

A `TMD.Tmd` is a function of the transverse-momentum *magnitude* `kT`, so it cannot express
any dependence on the direction of the transverse-momentum vector. A transverse-momentum
dependent distribution whose argument is a genuine vector in `Transverse` — a `VectorTmd`,
introduced in `EpsilonEridani.Particles.Parton.GTMD.Basic` — reaches `TMD.Tmd` by averaging
over the polar angle at fixed radius. This module makes that average explicit, using the
transverse circle average `circleAverageTransverse` of
`EpsilonEridani.Particles.Parton.GTMD.CircleAverage`.

## Main definitions

* `azimuthalAverage`: the per-flavour circle average of a `VectorTmd`, a `TMD.Tmd`. The value
  is set to `0` at unphysical `kT < 0`, which is the only reason the average satisfies
  `TMD.IsTmdDensity.supportKT`; since the circle average is even in the radius
  (`Real.circleAverage_neg_radius`), this cutoff is a deliberate break of that symmetry, and
  `azimuthalAverage_eq_zero_of_kT_neg`/`azimuthalAverage_of_kT_nonneg` are the interface for
  it. The average also inherits the junk value `0` of `circleAverageTransverse` on
  non-integrable slices, which is why `VectorTmd.IsDensity` needs no measurability or
  integrability condition.

## Main results

* `azimuthalAverage_eq_zero_of_kT_neg`, `azimuthalAverage_of_kT_nonneg`: the azimuthal average
  vanishes at negative transverse-momentum magnitude and is the circle average at nonnegative
  magnitude — the interface to the `kT < 0` cutoff of `azimuthalAverage`.
* `azimuthalAverage_zero_radius`: the azimuthal average at zero transverse momentum is the
  value at the origin.
* `azimuthalAverage_eq_zero_of_odd_on_circle`: the azimuthal average annihilates every
  vector-argument TMD that is odd in its transverse-momentum argument on the circle.
* `azimuthalAverage_comp_norm_of_kT_nonneg`: averaging a function of the magnitude alone returns
  that function at nonnegative transverse-momentum magnitude; the TMD form of
  `circleAverageTransverse_comp_norm`.
* `azimuthalAverage_comp_norm`: the azimuthal average retracts the radial inclusion
  `g ↦ fun i x w Q2 ζ => g i x ‖w‖ Q2 ζ` on TMDs vanishing at negative magnitude,
  `TMD.IsTmdDensity` in particular.
* `isTmdDensity_azimuthalAverage`: the azimuthal average of a `VectorTmd.IsDensity` is a
  `TMD.IsTmdDensity`.
* `tmdRegularity_azimuthalAverage`: the azimuthal average of a `VectorTmd.Regularity` TMD is
  `TMD.Regularity`.
* `tmdAssumptions_azimuthalAverage`: the azimuthal average of a `VectorTmd.Assumptions` TMD
  satisfies `TMD.Assumptions`, so it can be used with every consumer that takes one.

## References

* S. Meissner, A. Metz and M. Schlegel, *Generalized parton correlation functions for a spin-1/2
  hadron*, JHEP **08** (2009) 056, arXiv:0906.5323.
* C. Lorcé, B. Pasquini and M. Vanderhaeghen, *Unified framework for generalized and
  transverse-momentum dependent parton distributions within a 3Q light-cone picture of the
  nucleon*, JHEP **05** (2011) 041, arXiv:1102.4704.
-/

@[expose] public section

noncomputable section


namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

variable {Flavor : Type}

/-! ## The azimuthal average of a vector-argument TMD -/

/-- The azimuthal average of a vector-argument TMD: per flavour, the circle average of
    `f i x · Q2 ζ` over the circle of radius `kT`. Since a `TMD.Tmd` is a function of the
    magnitude `kT`, it is set to zero at unphysical `kT < 0`. -/
def azimuthalAverage (f : VectorTmd Flavor) : TMD.Tmd Flavor :=
  fun i x kT Q2 ζ => if kT < 0 then 0 else circleAverageTransverse (f i x · Q2 ζ) kT

/-- The azimuthal average is the `kT < 0` cutoff applied to the transverse circle average;
    `azimuthalAverage_eq_zero_of_kT_neg` and `azimuthalAverage_of_kT_nonneg` are its two
    branches. -/
lemma azimuthalAverage_def (f : VectorTmd Flavor) (i : Flavor) (x kT Q2 ζ : ℝ) :
    azimuthalAverage f i x kT Q2 ζ =
      if kT < 0 then 0 else circleAverageTransverse (f i x · Q2 ζ) kT := (rfl)
  -- `(rfl)`, not `rfl`: a syntactic `rfl` proof would implicitly tag the lemma `@[defeq]`,
  -- which would let `dsimp` unfold `azimuthalAverage` downstream.

/-- The azimuthal average vanishes at negative transverse-momentum magnitude. -/
@[simp]
lemma azimuthalAverage_eq_zero_of_kT_neg (f : VectorTmd Flavor) (i : Flavor) {x kT Q2 ζ : ℝ}
    (hkT : kT < 0) : azimuthalAverage f i x kT Q2 ζ = 0 := by
  simp [azimuthalAverage, hkT]

/-- At nonnegative transverse-momentum magnitude, the azimuthal average is the circle average. -/
lemma azimuthalAverage_of_kT_nonneg (f : VectorTmd Flavor) (i : Flavor) {x kT Q2 ζ : ℝ}
    (hkT : 0 ≤ kT) :
    azimuthalAverage f i x kT Q2 ζ = circleAverageTransverse (f i x · Q2 ζ) kT := by
  simp [azimuthalAverage, not_lt.mpr hkT]

/-- The azimuthal average annihilates every vector-argument TMD that is odd in its
    transverse-momentum argument on the circle `‖w‖ = |kT|`. -/
lemma azimuthalAverage_eq_zero_of_odd_on_circle (f : VectorTmd Flavor) (i : Flavor)
    {x kT Q2 ζ : ℝ}
    (hf : ∀ w, ‖w‖ = |kT| → f i x (-w) Q2 ζ = -f i x w Q2 ζ) :
    azimuthalAverage f i x kT Q2 ζ = 0 := by
  rcases lt_or_ge kT 0 with hkT | hkT
  · exact azimuthalAverage_eq_zero_of_kT_neg f i hkT
  · rw [azimuthalAverage_of_kT_nonneg f i hkT]
    exact circleAverageTransverse_eq_zero_of_odd_on_circle hf

/-- The azimuthal average at zero transverse momentum is the value at the origin. -/
@[simp]
lemma azimuthalAverage_zero_radius (f : VectorTmd Flavor) (i : Flavor) (x Q2 ζ : ℝ) :
    azimuthalAverage f i x 0 Q2 ζ = f i x 0 Q2 ζ := by
  rw [azimuthalAverage_of_kT_nonneg f i (kT := 0) le_rfl, circleAverageTransverse_zero_radius]

/-- Averaging a function of the magnitude alone returns that function at nonnegative
    transverse-momentum magnitude: the pointwise half of the retraction
    `azimuthalAverage_comp_norm`. -/
lemma azimuthalAverage_comp_norm_of_kT_nonneg (g : TMD.Tmd Flavor) (i : Flavor) {x kT Q2 ζ : ℝ}
    (hkT : 0 ≤ kT) :
    azimuthalAverage (fun i x w Q2 ζ => g i x ‖w‖ Q2 ζ) i x kT Q2 ζ = g i x kT Q2 ζ := by
  rw [azimuthalAverage_of_kT_nonneg _ i hkT,
    circleAverageTransverse_comp_norm (fun r => g i x r Q2 ζ), abs_of_nonneg hkT]

/-- The azimuthal average retracts the radial inclusion `g ↦ fun i x w Q2 ζ => g i x ‖w‖ Q2 ζ`
    of `TMD.Tmd` into `VectorTmd` on every TMD vanishing at negative transverse-momentum
    magnitude; the hypothesis is the field `TMD.IsTmdDensity.supportKT`, so every
    `TMD.IsTmdDensity` qualifies. -/
lemma azimuthalAverage_comp_norm {g : TMD.Tmd Flavor}
    (hg : ∀ i x kT Q2 ζ, kT < 0 → g i x kT Q2 ζ = 0) :
    azimuthalAverage (fun i x w Q2 ζ => g i x ‖w‖ Q2 ζ) = g := by
  funext i x kT Q2 ζ
  rcases lt_or_ge kT 0 with hkT | hkT
  · rw [azimuthalAverage_eq_zero_of_kT_neg _ i hkT, hg i x kT Q2 ζ hkT]
  · exact azimuthalAverage_comp_norm_of_kT_nonneg g i hkT

/-- The azimuthal average of a vector-argument density is a density in the sense of
    `TMD.IsTmdDensity`. -/
theorem isTmdDensity_azimuthalAverage {f : VectorTmd Flavor} (hf : VectorTmd.IsDensity f) :
    TMD.IsTmdDensity (azimuthalAverage f) where
  supportX i x kT Q2 ζ hx := by
    rcases lt_or_ge kT 0 with hkT | hkT
    · exact azimuthalAverage_eq_zero_of_kT_neg f i hkT
    · rw [azimuthalAverage_of_kT_nonneg f i hkT]
      exact circleAverageTransverse_const_on_circle fun w _ => hf.supportX i x w Q2 ζ hx
  supportKT i x kT Q2 ζ hkT := azimuthalAverage_eq_zero_of_kT_neg f i hkT
  nonneg i x kT Q2 ζ hx0 hx1 hkT := by
    rw [azimuthalAverage_of_kT_nonneg f i hkT]
    exact circleAverageTransverse_nonneg_of_nonneg fun w _ => hf.nonneg i x w Q2 ζ hx0 hx1

/-- The azimuthal average of a regular vector-argument TMD is regular in the sense of
    `TMD.Regularity`: measurability of every transverse-momentum slice gives measurability of
    the averaged function in the transverse-momentum magnitude. -/
theorem tmdRegularity_azimuthalAverage {f : VectorTmd Flavor} (hf : VectorTmd.Regularity f) :
    TMD.Regularity (azimuthalAverage f) where
  measurableKT i x Q2 ζ := by
    have hc : MeasureTheory.StronglyMeasurable (circleAverageTransverse (f i x · Q2 ζ)) :=
      (hf.measurableKT i x Q2 ζ).stronglyMeasurable.circleAverageTransverse
    simp only [azimuthalAverage_def]
    exact (Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const hc.measurable).aestronglyMeasurable

/-- The azimuthal average of a vector-argument TMD satisfying the full assumption bundle
    satisfies the full `TMD.Assumptions` bundle, so it can be used with every consumer that
    takes one. -/
theorem tmdAssumptions_azimuthalAverage {f : VectorTmd Flavor} (hf : VectorTmd.Assumptions f) :
    TMD.Assumptions (azimuthalAverage f) :=
  let h := VectorTmd.assumptions_iff.mp hf
  TMD.assumptions_iff.mpr ⟨isTmdDensity_azimuthalAverage h.1, tmdRegularity_azimuthalAverage h.2⟩

end GTMD
end Parton
end Particles
end EpsilonEridani
