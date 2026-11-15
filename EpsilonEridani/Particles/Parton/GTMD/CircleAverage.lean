/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Mathematics.MeasureTheory.Integral.CircleAverage
public import EpsilonEridani.Particles.Parton.GTMD.Transverse
/-!

# The circle average on the transverse plane

This module transports Mathlib's `Real.circleAverage` about the origin of `ℂ` to the transverse
plane `Transverse` along the coordinates `Complex.orthonormalBasisOneI`. It is the averaging
operation behind the azimuthal average of a vector-argument TMD
(`EpsilonEridani.Particles.Parton.GTMD.Average`), and depends on nothing beyond the
transverse plane itself.

## Main definitions

* `circleAverageTransverse g kT`: the mean of `g : Transverse → E` over the circle of radius
  `kT` about the origin, i.e. Mathlib's `Real.circleAverage` transported to `Transverse`
  along `Complex.orthonormalBasisOneI.repr`. Following Mathlib's convention, it is `0` when
  `g` is not circle integrable.

## Main results

* `circleAverageTransverse_eq_integral`: the average is
  `(2π)⁻¹ • ∫₀^{2π} g (circleMapTransverse kT θ) dθ`.
* `circleAverageTransverse_const_on_circle`: the average of a function that is constant on
  the circle `‖w‖ = |kT|` is that constant.
* `circleAverageTransverse_eq_zero_of_odd`: the average of a function that is odd on the
  circle `‖w‖ = |kT|` vanishes; the transport of `Real.circleAverage_eq_zero_of_odd`.
* `Continuous.circleAverageTransverse`: the average of a continuous function is continuous in
  the radius.
-/

@[expose] public section

noncomputable section

open Real

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
    h _ (by simpa using hz)

/-- The circle average of a function nonnegative on the circle `‖w‖ = |kT|` is nonnegative. -/
lemma circleAverageTransverse_nonneg_of_nonneg {g : Transverse → ℝ} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → 0 ≤ g w) : 0 ≤ circleAverageTransverse g kT := by
  rw [circleAverageTransverse_def]
  exact Real.circleAverage_nonneg_of_nonneg fun z hz =>
    hg _ (by simpa using hz)

/-- The circle average of a function odd on the circle `‖w‖ = |kT|` vanishes: the transverse
    transport of `Real.circleAverage_eq_zero_of_odd`. -/
lemma circleAverageTransverse_eq_zero_of_odd {g : Transverse → E} {kT : ℝ}
    (hg : ∀ w, ‖w‖ = |kT| → g (-w) = -g w) :
    circleAverageTransverse g kT = 0 := by
  rw [circleAverageTransverse_def]
  exact Real.circleAverage_eq_zero_of_odd fun z hz => by
    simpa using hg _ (by simpa using hz)

end GTMD
end Parton
end Particles
end EpsilonEridani

open EpsilonEridani.Particles.Parton.GTMD in
/-- The circle average of a continuous function is continuous in the radius: the transverse
    transport of Mathlib's `Continuous.circleAverage`, which is what carries continuity of the
    transverse-momentum slices of a `VectorTmd` to regularity of their azimuthal average. -/
@[fun_prop]
lemma Continuous.circleAverageTransverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Transverse → E} (hg : Continuous g) : Continuous (circleAverageTransverse g) :=
  (((hg.comp' Complex.orthonormalBasisOneI.repr.continuous).circleAverage (c := 0)).congr
    fun kT => (circleAverageTransverse_def g kT).symm)
