/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Composing a bilinear form with a nondegenerate one

Mathlib's `LinearMap.BilinForm.symmCompOfNondegenerate B₁ B₂ hB₂` raises the second index of a
bilinear form `B₁` against a nondegenerate bilinear form `B₂`: the endomorphism `E` with
`B₂ (E u) v = B₁ u v` for all `u` and `v`, which exists and is unique because a nondegenerate
form identifies `V` with its dual. This is the combinator behind the raised forms built from
alternating maps: the raised transverse antisymmetric tensor of a light-cone basis
(`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`) and the contraction of
the Minkowski volume form with two vectors
(`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm`).

## Main statements

* `LinearMap.BilinForm.eq_symmCompOfNondegenerate_iff`:
  `B₁.symmCompOfNondegenerate B₂ hB₂ u` is the unique vector `w` with `B₂ w v = B₁ u v` for
  every `v`.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The characterisation of `B₁.symmCompOfNondegenerate B₂ hB₂ u`: it is the unique vector `w`
with `B₂ w v = B₁ u v` for every `v`. -/
theorem eq_symmCompOfNondegenerate_iff (B₁ : BilinForm K V) {B₂ : BilinForm K V}
    (hB₂ : B₂.Nondegenerate) {u w : V} :
    w = B₁.symmCompOfNondegenerate B₂ hB₂ u ↔ ∀ v, B₂ w v = B₁ u v := by
  constructor
  · rintro rfl v
    exact symmCompOfNondegenerate_left_apply _ hB₂ v u
  · intro h
    refine (B₂.toDual hB₂).injective (LinearMap.ext fun v => ?_)
    rw [toDual_def, toDual_def, h, symmCompOfNondegenerate_left_apply]

end LinearMap.BilinForm
