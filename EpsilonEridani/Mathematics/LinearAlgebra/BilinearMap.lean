/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Linear independence of two bilinear maps separated by probe arguments

Two bilinear maps `B₁`, `B₂` are linearly independent as soon as one pair of arguments sees `B₁`
but not `B₂`, and another pair sees `B₂` but not `B₁`. This is the non-degeneracy argument
behind the uniqueness of the structure-function coefficients of the hadronic tensors of
deep-inelastic scattering.

## Main results

- `LinearMap.linearIndependent_pair_of_probes`: two bilinear maps separated by two probe pairs
  are linearly independent.
-/

public section

namespace LinearMap

variable {R M N P : Type*} [CommRing R] [IsDomain R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommGroup P] [Module R P] [Module.IsTorsionFree R P]

/-- Two bilinear maps are linearly independent if the probe pair `(v₁, w₁)` sees `B₁` but not
`B₂`, and the probe pair `(v₂, w₂)` sees `B₂` but not `B₁`. -/
theorem linearIndependent_pair_of_probes {B₁ B₂ : M →ₗ[R] N →ₗ[R] P} {v₁ v₂ : M} {w₁ w₂ : N}
    (h₁ : B₁ v₁ w₁ ≠ 0) (h₂ : B₂ v₁ w₁ = 0) (h₃ : B₁ v₂ w₂ = 0) (h₄ : B₂ v₂ w₂ ≠ 0) :
    LinearIndependent R ![B₁, B₂] := by
  refine LinearIndependent.pair_iff.mpr fun s t hst => ⟨?_, ?_⟩
  · have h := congr_fun₂ hst v₁ w₁
    simp only [add_apply, smul_apply, h₂, smul_zero, add_zero, zero_apply] at h
    exact (smul_eq_zero.mp h).resolve_right h₁
  · have h := congr_fun₂ hst v₂ w₂
    simp only [add_apply, smul_apply, h₃, smul_zero, zero_add, zero_apply] at h
    exact (smul_eq_zero.mp h).resolve_right h₄

end LinearMap
