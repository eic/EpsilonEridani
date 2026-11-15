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

* `circleAverageTransverse g kT`: the mean of `g : Transverse → E` over the circle of radius
  `kT` about the origin, i.e. Mathlib's `Real.circleAverage` transported to `Transverse`
  along `Complex.orthonormalBasisOneI.repr`. Following Mathlib's convention, it is `0` when
  `g` is not circle integrable.

## Main results

* `circleAverageTransverse_const_on_circle`: the average of a function that is constant on
  the circle `‖w‖ = |kT|` is that constant.
* `circleAverageTransverse_comp_norm`: the average of a radial function `w ↦ g ‖w‖` is
  `g |kT|`.
* `circleAverageTransverse_eq_zero_of_odd`: the average of a function that is odd on the
  circle `‖w‖ = |kT|` vanishes; the transport of `Real.circleAverage_eq_zero_of_odd`.
* `stronglyMeasurable_circleAverageTransverse`: the average of a strongly measurable function is
  strongly measurable in the radius; the transport of
  `MeasureTheory.StronglyMeasurable.circleAverage`.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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
    h _ ((LinearIsometryEquiv.norm_map _ z).trans (mem_sphere_zero_iff_norm.mp hz))

/-- The circle average of a radial function `w ↦ g ‖w‖` over the circle of radius `kT` is
    `g |kT|`. -/
lemma circleAverageTransverse_comp_norm [CompleteSpace E] (g : ℝ → E) (kT : ℝ) :
    circleAverageTransverse (fun w => g ‖w‖) kT = g |kT| :=
  circleAverageTransverse_const_on_circle fun w hw => by rw [hw]

/-- The circle average of a function nonnegative on the circle `‖w‖ = |kT|` is nonnegative. -/
lemma circleAverageTransverse_nonneg_of_nonneg {g : Transverse → ℝ} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → 0 ≤ g w) : 0 ≤ circleAverageTransverse g kT := by
  rw [circleAverageTransverse_def]
  exact Real.circleAverage_nonneg_of_nonneg fun z hz =>
    hg _ ((LinearIsometryEquiv.norm_map _ z).trans (mem_sphere_zero_iff_norm.mp hz))

/-- The circle average of a function odd on the circle `‖w‖ = |kT|` vanishes: the transverse
    transport of `Real.circleAverage_eq_zero_of_odd`. -/
lemma circleAverageTransverse_eq_zero_of_odd {g : Transverse → E} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → g (-w) = -g w) :
    circleAverageTransverse g kT = 0 := by
  rw [circleAverageTransverse_def]
  refine Real.circleAverage_eq_zero_of_odd fun z hz => ?_
  rw [mul_zero, zero_sub, map_neg]
  exact hg _ ((LinearIsometryEquiv.norm_map _ z).trans (mem_sphere_zero_iff_norm.mp hz))

/-- The circle average of a strongly measurable function is strongly measurable in the radius:
    the transverse transport of `MeasureTheory.StronglyMeasurable.circleAverage`, which is what
    carries measurability of the transverse-momentum slices of a `VectorTmd` to regularity of
    their azimuthal average. -/
lemma stronglyMeasurable_circleAverageTransverse {g : Transverse → E}
    (hg : MeasureTheory.StronglyMeasurable g) :
    MeasureTheory.StronglyMeasurable (circleAverageTransverse g) := by
  rw [show circleAverageTransverse g = Real.circleAverage
      (fun z => g (Complex.orthonormalBasisOneI.repr z)) 0 from
    funext (circleAverageTransverse_def g)]
  exact (hg.comp_measurable Complex.orthonormalBasisOneI.repr.continuous.measurable).circleAverage 0

end GTMD
end Parton
end Particles
end EpsilonEridani
