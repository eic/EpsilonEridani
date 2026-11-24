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
  component and spatial part of a purely temporal vector `t e₀`, and the spatial part of a
  difference (`spatialPart_sub`). They describe the equal-time projection
  `v - ofTemporalComponent v.timeComponent` of a vector `v`, which has vanishing time component
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

* The standard basis of four-dimensional Minkowski space indexed by `Fin 4`,
  `EpsilonEridani.minkowskiBasisFin4 = basis.reindex finSumFinEquiv`, with `e₀` the time direction,
  and its vectors `minkowskiBasisFin4_apply_zero`, …, `minkowskiBasisFin4_apply_three`. It is the
  basis in which the volume form of
  `EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm` is a determinant.
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

namespace EpsilonEridani

open Lorentz Vector

/-- The standard basis of four-dimensional Minkowski space indexed by `Fin 4`, with `e₀` the
time direction and `e₁, e₂, e₃` the spatial directions. -/
noncomputable def minkowskiBasisFin4 : Module.Basis (Fin 4) ℝ (Vector 3) :=
  basis.reindex finSumFinEquiv

/-- The `i`-th vector of `minkowskiBasisFin4` is the standard basis vector with the Minkowski index
`finSumFinEquiv.symm i : Fin 1 ⊕ Fin 3`. -/
theorem minkowskiBasisFin4_apply (i : Fin 4) :
    minkowskiBasisFin4 i = basis (finSumFinEquiv.symm i) := by
  simp [minkowskiBasisFin4]

/-- The coordinates of `v` in `minkowskiBasisFin4` are its components, `v^{finSumFinEquiv.symm i}`.
-/
@[simp]
theorem minkowskiBasisFin4_repr_apply (v : Vector 3) (i : Fin 4) :
    minkowskiBasisFin4.repr v i = v (finSumFinEquiv.symm i) := by
  simp [minkowskiBasisFin4, basis_repr_apply]

/-- `e₀` is the time basis vector. -/
@[simp]
theorem minkowskiBasisFin4_apply_zero : minkowskiBasisFin4 0 = basis (Sum.inl 0) :=
  minkowskiBasisFin4_apply 0

/-- `e₁` is the first spatial basis vector. -/
@[simp]
theorem minkowskiBasisFin4_apply_one : minkowskiBasisFin4 1 = basis (Sum.inr 0) :=
  minkowskiBasisFin4_apply 1

/-- `e₂` is the second spatial basis vector. -/
@[simp]
theorem minkowskiBasisFin4_apply_two : minkowskiBasisFin4 2 = basis (Sum.inr 1) :=
  minkowskiBasisFin4_apply 2

/-- `e₃` is the third spatial basis vector. -/
@[simp]
theorem minkowskiBasisFin4_apply_three : minkowskiBasisFin4 3 = basis (Sum.inr 2) :=
  minkowskiBasisFin4_apply 3

/-- `e_{i+1}` is the `i`-th spatial basis vector. -/
@[simp]
theorem minkowskiBasisFin4_apply_succ (i : Fin 3) :
    minkowskiBasisFin4 i.succ = basis (Sum.inr i) := by
  rw [minkowskiBasisFin4_apply]
  fin_cases i <;> rfl

end EpsilonEridani
