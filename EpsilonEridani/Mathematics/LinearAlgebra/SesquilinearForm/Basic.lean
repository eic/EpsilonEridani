/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

/-!
# Isometries of a bilinear form

The maps `f` preserving a bilinear form `B`, `LinearMap.IsOrthogonal B f`, contain the identity
(`LinearMap.isOrthogonal_id`) and are closed under composition (`LinearMap.IsOrthogonal.comp`).
-/

public section

namespace LinearMap

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- The identity is an isometry of every bilinear form. -/
lemma isOrthogonal_id (B : BilinForm R M) : B.IsOrthogonal _root_.id := fun _ _ ↦ by
  rw [_root_.id_eq, _root_.id_eq]

/-- A composite of isometries of `B` is an isometry of `B`. -/
lemma IsOrthogonal.comp {f f' : M → M} (hf : B.IsOrthogonal f) (hf' : B.IsOrthogonal f') :
    B.IsOrthogonal (f ∘ f') := fun x y ↦ by
  rw [Function.comp_apply, Function.comp_apply, hf, hf']

end LinearMap
