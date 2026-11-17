/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Mathematics.MeasureTheory.Integral.CircleAverage
public import EpsilonEridani.Particles.Parton.GTMD.Transverse
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
/-!

# The circle average on the transverse plane

This module transports Mathlib's `Real.circleAverage` about the origin of `ℂ` to the transverse
plane `Transverse` along the coordinates `Complex.orthonormalBasisOneI`, a linear isometry, so the
circle of radius `r` in `ℂ` is carried onto the circle `‖w‖ = r` of the transverse plane. It is the
averaging operation behind the azimuthal average of a vector-argument TMD
(`EpsilonEridani.Particles.Parton.GTMD.Average`); it depends only on the transverse plane and
Mathlib's circle average, with no parton-physics content.

## Main definitions

* `circleAverageTransverse g R`: the mean of `g : Transverse → E` over the circle of radius
  `R` about the origin, i.e. Mathlib's `Real.circleAverage` transported to `Transverse`
  along `Complex.orthonormalBasisOneI.repr`. Following Mathlib's convention, it is `0` when
  `g` is not circle integrable.

## Main results

* `circleAverageTransverse_zero_radius`: the average at zero radius is the value at the origin.
* `circleAverageTransverse_congr_sphere`: the average depends only on the values on the circle
  `‖w‖ = |R|`.
* `circleAverageTransverse_const_on_circle`: the average of a function that is constant on
  the circle `‖w‖ = |R|` is that constant.
* `circleAverageTransverse_comp_norm`: the average of a radial function `w ↦ g ‖w‖` is
  `g |R|`.
* `circleAverageTransverse_nonneg_of_nonneg`: the average of a function nonnegative on the
  circle is nonnegative.
* `circleAverageTransverse_eq_zero_of_odd_on_circle`: the average of a function that is odd on the
  circle `‖w‖ = |R|` vanishes; the transport of `Real.circleAverage_eq_zero_of_odd_on_circle`.
* `MeasureTheory.StronglyMeasurable.circleAverageTransverse`: the average of a strongly
  measurable function is strongly measurable in the radius; the transport of
  `MeasureTheory.StronglyMeasurable.circleAverage`.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The mean of `g` over the circle of radius `R` about the origin of the transverse plane:
    Mathlib's `Real.circleAverage` transported along `Complex.orthonormalBasisOneI.repr`.
    Following Mathlib's convention, the value is `0` when
    `fun z => g (Complex.orthonormalBasisOneI.repr z)` is not circle integrable, so the
    identification with the mean requires circle integrability. -/
def circleAverageTransverse (g : Transverse → E) (R : ℝ) : E :=
  Real.circleAverage (fun z => g (Complex.orthonormalBasisOneI.repr z)) 0 R

/-- The circle average on the transverse plane is Mathlib's `Real.circleAverage` of the
    function read in the coordinates `Complex.orthonormalBasisOneI`. -/
lemma circleAverageTransverse_def (g : Transverse → E) (R : ℝ) :
    circleAverageTransverse g R =
      Real.circleAverage (fun z => g (Complex.orthonormalBasisOneI.repr z)) 0 R :=
  (rfl)
  -- `(rfl)`, not `rfl`: a syntactic `rfl` proof would implicitly tag the lemma `@[defeq]`,
  -- which would let `dsimp` unfold `circleAverageTransverse` downstream.

/-- The coordinates `Complex.orthonormalBasisOneI` carry the circle of radius `|R|` in `ℂ` onto
    the circle `‖w‖ = |R|` of the transverse plane. -/
private lemma norm_repr_of_mem_sphere {R : ℝ} {z : ℂ} (hz : z ∈ Metric.sphere (0 : ℂ) |R|) :
    ‖Complex.orthonormalBasisOneI.repr z‖ = |R| :=
  (LinearIsometryEquiv.norm_map _ z).trans (mem_sphere_zero_iff_norm.mp hz)

/-- The circle average at zero radius is the value at the origin. -/
@[simp]
lemma circleAverageTransverse_zero_radius [CompleteSpace E] (g : Transverse → E) :
    circleAverageTransverse g 0 = g 0 := by
  rw [circleAverageTransverse_def, Real.circleAverage_zero, map_zero]

/-- The circle average depends only on the values on the circle `‖w‖ = |R|`. -/
lemma circleAverageTransverse_congr_sphere {g₁ g₂ : Transverse → E} {R : ℝ}
    (h : ∀ w, ‖w‖ = |R| → g₁ w = g₂ w) :
    circleAverageTransverse g₁ R = circleAverageTransverse g₂ R := by
  rw [circleAverageTransverse_def, circleAverageTransverse_def]
  exact Real.circleAverage_congr_sphere fun z hz => h _ (norm_repr_of_mem_sphere hz)

/-- The circle average of a function that is constant on the circle `‖w‖ = |R|` is that
    constant. -/
lemma circleAverageTransverse_const_on_circle [CompleteSpace E] {g : Transverse → E} {c : E}
    {R : ℝ} (h : ∀ w, ‖w‖ = |R| → g w = c) :
    circleAverageTransverse g R = c := by
  rw [circleAverageTransverse_congr_sphere (g₂ := fun _ => c) h, circleAverageTransverse_def]
  exact Real.circleAverage_const c 0 R

/-- The circle average of a radial function `w ↦ g ‖w‖` over the circle of radius `R` is
    `g |R|`. -/
lemma circleAverageTransverse_comp_norm [CompleteSpace E] (g : ℝ → E) (R : ℝ) :
    circleAverageTransverse (fun w => g ‖w‖) R = g |R| :=
  circleAverageTransverse_const_on_circle fun w hw => by rw [hw]

/-- The circle average of a function nonnegative on the circle `‖w‖ = |R|` is nonnegative. -/
lemma circleAverageTransverse_nonneg_of_nonneg {g : Transverse → ℝ} {R : ℝ}
    (hg : ∀ w, ‖w‖ = |R| → 0 ≤ g w) : 0 ≤ circleAverageTransverse g R := by
  rw [circleAverageTransverse_def]
  exact Real.circleAverage_nonneg_of_nonneg fun z hz => hg _ (norm_repr_of_mem_sphere hz)

/-- The circle average of a function odd on the circle `‖w‖ = |R|` vanishes: the transverse
    transport of `Real.circleAverage_eq_zero_of_odd_on_circle`. -/
lemma circleAverageTransverse_eq_zero_of_odd_on_circle {g : Transverse → E} {R : ℝ}
    (hg : ∀ w, ‖w‖ = |R| → g (-w) = -g w) :
    circleAverageTransverse g R = 0 := by
  rw [circleAverageTransverse_def]
  refine Real.circleAverage_eq_zero_of_odd_on_circle fun z hz => ?_
  rw [mul_zero, zero_sub, map_neg]
  exact hg _ (norm_repr_of_mem_sphere hz)


end GTMD
end Parton
end Particles
end EpsilonEridani

open EpsilonEridani.Particles.Parton.GTMD in
/-- The circle average of a strongly measurable function is strongly measurable in the radius:
    the transverse transport of `MeasureTheory.StronglyMeasurable.circleAverage`, which is what
    carries measurability of the transverse-momentum slices of a `VectorTmd` to regularity of
    their azimuthal average. -/
lemma MeasureTheory.StronglyMeasurable.circleAverageTransverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {g : Transverse → E} (hg : StronglyMeasurable g) :
    StronglyMeasurable (circleAverageTransverse g) := by
  -- `circleAverageTransverse_def` is pointwise; `funext` lifts it to the equation of functions
  -- of the radius that the measurability statement is about.
  rw [funext (circleAverageTransverse_def g)]
  exact (hg.comp_measurable Complex.orthonormalBasisOneI.repr.continuous.measurable).circleAverage 0
