/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
/-!

# The transverse plane

This module defines the transverse plane `Transverse = EuclideanSpace ℝ (Fin 2)` of the
light-front frame, in which transverse momenta and transverse positions are genuine
two-vectors, together with its polar parametrisation `radialVector`.

## Main definitions

* `Transverse`: the two-dimensional transverse plane.
* `radialVector kT θ`: the vector of radius `kT` at polar angle `θ`, i.e. Mathlib's
  `circleMap 0 kT θ` read in the coordinates `Complex.orthonormalBasisOneI`.

## Main results

* `radialVector_apply_zero`, `radialVector_apply_one`: the Cartesian components
  `(kT cos θ, kT sin θ)`.
* `norm_radialVector`: the radial vector has norm `|kT|`.
* `radialVector_neg_radius`: reversing the radius reverses the vector.
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

/-- The radial vector of radius `kT` at polar angle `θ` in the transverse plane:
    `circleMap 0 kT θ` read in the coordinates `Complex.orthonormalBasisOneI`. -/
def radialVector (kT θ : ℝ) : Transverse :=
  Complex.orthonormalBasisOneI.repr (circleMap 0 kT θ)

/-- The first Cartesian component of the radial vector is `kT cos θ`. -/
@[simp]
lemma radialVector_apply_zero (kT θ : ℝ) : radialVector kT θ 0 = kT * cos θ := by
  simp [radialVector, circleMap_zero]

/-- The second Cartesian component of the radial vector is `kT sin θ`. -/
@[simp]
lemma radialVector_apply_one (kT θ : ℝ) : radialVector kT θ 1 = kT * sin θ := by
  simp [radialVector, circleMap_zero]

/-- The radial vector has norm `|kT|`. -/
@[simp]
lemma norm_radialVector (kT θ : ℝ) : ‖radialVector kT θ‖ = |kT| := by
  rw [radialVector, LinearIsometryEquiv.norm_map, norm_circleMap_zero]

/-- The radial vector of radius zero is the origin. -/
@[simp]
lemma radialVector_zero_radius (θ : ℝ) : radialVector 0 θ = 0 := by
  simp [radialVector, circleMap_zero_radius]

/-- Reversing the radius reverses the radial vector. -/
lemma radialVector_neg_radius (kT θ : ℝ) : radialVector (-kT) θ = -radialVector kT θ := by
  rw [radialVector, radialVector, ← map_neg]
  congr 1
  simp [circleMap_zero]

end GTMD
end Parton
end Particles
end EpsilonEridani
