/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic

/-!
# Extensions of the basic API of Lorentz vectors

Additions to `Physlib`'s `Relativity/Tensors/RealTensor/Vector/Basic.lean`.

* The vector `ofTimeAndSpatial x s` has time component `x` and spatial part `s`
  (`timeComponent_ofTimeAndSpatial_eq`, `spatialPart_ofTimeAndSpatial_eq`). It is assembled from
  Physlib's `ofTemporalComponent` and `ofSpatialComponent`, and every vector arises this way from
  its own time component and spatial part (`ofTimeAndSpatial_timeComponent_spatialPart_eq`).
  Its Minkowski product is `minkowskiProduct_ofTimeAndSpatial_eq` in
  `EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions`. It gives
  explicit configurations, such as light-cone frames, in any spacetime with at least two spatial
  dimensions.
-/

public section

noncomputable section

namespace Lorentz
namespace Vector

/-- The vector with time component `x` and spatial part `s`, assembled from Physlib's
`ofTemporalComponent` and `ofSpatialComponent`. -/
def ofTimeAndSpatial {d : ℕ} (x : ℝ) (s : EuclideanSpace ℝ (Fin d)) : Vector d :=
  ofTemporalComponent x + ofSpatialComponent s

lemma ofTimeAndSpatial_def {d : ℕ} (x : ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    ofTimeAndSpatial x s = ofTemporalComponent x + ofSpatialComponent s := (rfl)

@[simp]
lemma timeComponent_ofTimeAndSpatial_eq {d : ℕ} (x : ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    (ofTimeAndSpatial x s).timeComponent = x := by
  simp [ofTimeAndSpatial_def, ofTemporalComponent, ofSpatialComponent, apply_sum, basis_apply]

@[simp]
lemma spatialPart_ofTimeAndSpatial_eq {d : ℕ} (x : ℝ) (s : EuclideanSpace ℝ (Fin d)) :
    (ofTimeAndSpatial x s).spatialPart = s := by
  ext i
  simp [ofTimeAndSpatial_def, ofTemporalComponent, ofSpatialComponent, apply_sum, basis_apply]

/-- Every vector is assembled from its time component and its spatial part. -/
@[simp]
lemma ofTimeAndSpatial_timeComponent_spatialPart_eq {d : ℕ} (v : Vector d) :
    ofTimeAndSpatial v.timeComponent v.spatialPart = v := by
  refine ext_of_apply fun μ => ?_
  rcases μ with μ | i
  · fin_cases μ
    -- `timeComponent` is an `abbrev` for evaluation at `Sum.inl 0`
    exact timeComponent_ofTimeAndSpatial_eq ..
  · rw [← spatialPart_apply_eq_toCoord (ofTimeAndSpatial _ _), ← spatialPart_apply_eq_toCoord v,
      spatialPart_ofTimeAndSpatial_eq]

end Vector
end Lorentz
