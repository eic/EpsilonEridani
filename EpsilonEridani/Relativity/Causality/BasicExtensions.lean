/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Causality.Basic

/-!
# Extensions of the causal character of Lorentz vectors

Facts about `Physlib`'s causal character `Lorentz.Vector.causalCharacter` that go beyond
`Physlib`'s own API, together with the component lemmas for `ofTemporalComponent` and
`ofSpatialComponent` they rest on: the spatial part of a spacelike vector does not vanish
(`spatialPart_ne_zero_of_spaceLike`), a nonzero vector with vanishing time component is
spacelike (`causalCharacter_eq_spaceLike_of_timeComponent_eq_zero`), and the equal-time
projection `v - ofTemporalComponent v.timeComponent`, which equals
`ofSpatialComponent v.spatialPart`
(`sub_ofTemporalComponent_timeComponent_eq_ofSpatialComponent_spatialPart`), of a vector with
nonzero spatial part is again spacelike
(`causalCharacter_sub_ofTemporalComponent_eq_spaceLike_of_spatialPart_ne_zero`).
-/

public section

namespace Lorentz
namespace Vector

open scoped Lorentz.Vector

/-- The spatial part of a spacelike vector does not vanish: a spacelike vector is never purely
temporal. -/
lemma spatialPart_ne_zero_of_spaceLike {d : ℕ} (v : Vector d)
    (hv : causalCharacter v = CausalCharacter.spaceLike) : spatialPart v ≠ 0 := by
  intro h
  have h' : ⟪v, v⟫ₘ < 0 := (spaceLike_iff_norm_sq_neg v).mp hv
  rw [minkowskiProduct_self_eq_sq_sub, h, norm_zero] at h'
  nlinarith [sq_nonneg v.timeComponent]

/-- A nonzero Lorentz vector with vanishing time component is spacelike. -/
lemma causalCharacter_eq_spaceLike_of_timeComponent_eq_zero {d : ℕ} {v : Vector d}
    (h0 : v.timeComponent = 0) (hne : v ≠ 0) :
    causalCharacter v = CausalCharacter.spaceLike := by
  have hsp : spatialPart v ≠ 0 := fun h =>
    hne (eq_zero_of_timeComponent_of_spatialPart h0 h)
  refine (spaceLike_iff_norm_sq_neg v).mpr ?_
  rw [minkowskiProduct_self_eq_sq_sub, h0, zero_pow two_ne_zero, zero_sub, neg_lt_zero]
  exact pow_pos (norm_pos_iff.mpr hsp) 2

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

/-- The purely spatial vector `ofSpatialComponent x` has vanishing time component. -/
@[simp]
lemma timeComponent_ofSpatialComponent {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    (ofSpatialComponent x : Vector d).timeComponent = 0 := by
  simp [ofSpatialComponent, apply_sum, basis_apply]

/-- The purely spatial vector `ofSpatialComponent x` has spatial part `x`. -/
@[simp]
lemma spatialPart_ofSpatialComponent {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    (ofSpatialComponent x : Vector d).spatialPart = x := by
  ext i
  simp [ofSpatialComponent, apply_sum, basis_apply]

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
lemma timeComponent_sub_ofTemporalComponent {d : ℕ} (v : Vector d) :
    (v - ofTemporalComponent v.timeComponent).timeComponent = 0 := by
  simp

/-- Subtracting a purely temporal vector `t e₀` does not change the spatial part. -/
@[simp]
lemma spatialPart_sub_ofTemporalComponent {d : ℕ} (v : Vector d) (t : ℝ) :
    (v - ofTemporalComponent t).spatialPart = v.spatialPart := by
  simp [spatialPart_sub]

/-- The equal-time projection `v - v⁰ e₀` is the purely spatial vector with the spatial part
of `v`. -/
lemma sub_ofTemporalComponent_timeComponent_eq_ofSpatialComponent_spatialPart {d : ℕ}
    (v : Vector d) :
    v - ofTemporalComponent v.timeComponent = ofSpatialComponent v.spatialPart := by
  rw [← sub_eq_zero]
  refine eq_zero_of_timeComponent_of_spatialPart ?_ ?_
  · simp
  · simp [spatialPart_sub]

/-- The equal-time projection `v - v⁰ e₀` of a vector with nonzero spatial part is again
spacelike. -/
lemma causalCharacter_sub_ofTemporalComponent_eq_spaceLike_of_spatialPart_ne_zero {d : ℕ}
    (v : Vector d) (hv : spatialPart v ≠ 0) :
    causalCharacter (v - ofTemporalComponent v.timeComponent) = CausalCharacter.spaceLike :=
  causalCharacter_eq_spaceLike_of_timeComponent_eq_zero (timeComponent_sub_ofTemporalComponent v)
    (fun h => hv (by rw [← spatialPart_sub_ofTemporalComponent v v.timeComponent, h]; ext i; simp))

end Vector
end Lorentz
