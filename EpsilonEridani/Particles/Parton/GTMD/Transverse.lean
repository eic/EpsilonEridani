/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.CircleIntegral
/-!

# The transverse plane

This module defines the transverse plane `Transverse = EuclideanSpace ℝ (Fin 2)` of the
light-front frame, in which transverse momenta and transverse positions are genuine
two-vectors, together with its polar parametrisation `circleMapTransverse`.

## Main definitions

* `Transverse`: the two-dimensional transverse plane.
* `circleMapTransverse kT θ`: the vector of radius `kT` at polar angle `θ`, i.e. Mathlib's
  `circleMap 0 kT θ` read in the coordinates `Complex.orthonormalBasisOneI`.

## Main results

* `circleMapTransverse_apply_zero`, `circleMapTransverse_apply_one`: the Cartesian components
  `(kT cos θ, kT sin θ)`.
* `norm_circleMapTransverse`: the vector has norm `|kT|`.
* `circleMapTransverse_neg_radius`: reversing the radius reverses the vector.

The coordinates `Complex.orthonormalBasisOneI` carry the circle of radius `r` in `ℂ` onto the
circle `‖w‖ = r` of the transverse plane; that translation is
`LinearIsometryEquiv.norm_map_of_mem_sphere_zero`, in
`EpsilonEridani.Mathematics.LinearAlgebra.LinearIsometry.Sphere`.
-/
@[expose] public section

noncomputable section

open Real

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

/-- The two-dimensional transverse plane of the light-front frame. -/
abbrev Transverse : Type := EuclideanSpace ℝ (Fin 2)

/-- The vector of radius `kT` at polar angle `θ` in the transverse plane:
    `circleMap 0 kT θ` read in the coordinates `Complex.orthonormalBasisOneI`. -/
def circleMapTransverse (kT θ : ℝ) : Transverse :=
  Complex.orthonormalBasisOneI.repr (circleMap 0 kT θ)

/-- The first Cartesian component of `circleMapTransverse kT θ` is `kT cos θ`. -/
@[simp]
lemma circleMapTransverse_apply_zero (kT θ : ℝ) : circleMapTransverse kT θ 0 = kT * cos θ := by
  simp [circleMapTransverse, circleMap_zero]

/-- The second Cartesian component of `circleMapTransverse kT θ` is `kT sin θ`. -/
@[simp]
lemma circleMapTransverse_apply_one (kT θ : ℝ) : circleMapTransverse kT θ 1 = kT * sin θ := by
  simp [circleMapTransverse, circleMap_zero]

/-- The vector `circleMapTransverse kT θ` has norm `|kT|`. -/
@[simp]
lemma norm_circleMapTransverse (kT θ : ℝ) : ‖circleMapTransverse kT θ‖ = |kT| := by
  rw [circleMapTransverse, LinearIsometryEquiv.norm_map, norm_circleMap_zero]

/-- The vector of radius zero is the origin. -/
@[simp]
lemma circleMapTransverse_zero_radius (θ : ℝ) : circleMapTransverse 0 θ = 0 := by
  simp [circleMapTransverse, circleMap_zero_radius]

/-- Reversing the radius reverses the vector. -/
lemma circleMapTransverse_neg_radius (kT θ : ℝ) :
    circleMapTransverse (-kT) θ = -circleMapTransverse kT θ := by
  have hc : circleMap 0 (-kT) θ = -circleMap 0 kT θ := by simp [circleMap_zero]
  rw [circleMapTransverse, hc, map_neg, circleMapTransverse]

end GTMD
end Parton
end Particles
end EpsilonEridani
