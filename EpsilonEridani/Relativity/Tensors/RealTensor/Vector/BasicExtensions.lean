/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic

/-!
# Extensions of the basic API of Lorentz vectors

* Component lemmas for `Physlib`'s constructor `Lorentz.Vector.ofTemporalComponent`: the time
  component and spatial part of a purely temporal vector `t e₀`, and the linearity of the
  spatial part (`spatialPart_sub`, `spatialPart_add`, `spatialPart_smul`). They describe the
  equal-time projection `v - ofTemporalComponent v.timeComponent` of a vector `v`, which has
  vanishing time component
  (`timeComponent_sub_ofTemporalComponent_timeComponent`) and the spatial part of `v`
  (`spatialPart_sub_ofTemporalComponent`).

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

/-- The purely temporal vector `ofTemporalComponent t = t e₀` has time component `t`. -/
@[simp]
lemma timeComponent_ofTemporalComponent {d : ℕ} (t : ℝ) :
    (ofTemporalComponent t : Vector d).timeComponent = t := by
  simp [ofTemporalComponent, basis_apply]

/-- The purely temporal vector `ofTemporalComponent t = t e₀` has vanishing spatial part. -/
@[simp]
lemma spatialPart_ofTemporalComponent {d : ℕ} (t : ℝ) :
    (ofTemporalComponent t : Vector d).spatialPart = 0 := by
  ext i
  simp [ofTemporalComponent, basis_apply]

/-- The spatial part of a difference is the difference of the spatial parts.

This is not a `@[simp]` lemma: the reducible `spatialPart` head unfolds to a componentwise
expression, which `apply_sub` already rewrites, so the simp-normal-form linter rejects it. -/
lemma spatialPart_sub {d : ℕ} (v w : Vector d) :
    (v - w).spatialPart = v.spatialPart - w.spatialPart := by
  ext i
  simp

/-- The spatial part of a sum is the sum of the spatial parts.

This is not a `@[simp]` lemma, for the same reason as `spatialPart_sub`. -/
lemma spatialPart_add {d : ℕ} (v w : Vector d) :
    (v + w).spatialPart = v.spatialPart + w.spatialPart :=
  map_add (spatialCLM d) v w

/-- The spatial part of a scalar multiple is the multiple of the spatial part.

This is not a `@[simp]` lemma, for the same reason as `spatialPart_sub`. -/
lemma spatialPart_smul {d : ℕ} (c : ℝ) (v : Vector d) :
    (c • v).spatialPart = c • v.spatialPart :=
  map_smul (spatialCLM d) c v

/-- The equal-time projection `v - v⁰ e₀` has vanishing time component.

This is not a `@[simp]` lemma: `simp` proves it from `apply_sub` and
`timeComponent_ofTemporalComponent`. -/
lemma timeComponent_sub_ofTemporalComponent_timeComponent {d : ℕ} (v : Vector d) :
    (v - ofTemporalComponent v.timeComponent).timeComponent = 0 := by
  simp

/-- Subtracting a purely temporal vector `t e₀` does not change the spatial part. -/
@[simp]
lemma spatialPart_sub_ofTemporalComponent {d : ℕ} (v : Vector d) (t : ℝ) :
    (v - ofTemporalComponent t).spatialPart = v.spatialPart := by
  simp [spatialPart_sub]

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
