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

- `LinearMap.SeparatingProbes`: two probe pairs separating two bilinear maps.
- `LinearMap.linearIndependent_pair_of_probes`, `LinearMap.SeparatingProbes.linearIndependent`:
  two bilinear maps separated by two probe pairs are linearly independent.
-/

public section

namespace LinearMap

section SeparatingProbes

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [AddCommMonoid P] [Module R P]

/-- Two probe pairs separating the bilinear maps `B₁` and `B₂`: the pair `(v₁, w₁)` sees `B₁`
but not `B₂`, and the pair `(v₂, w₂)` sees `B₂` but not `B₁`. -/
structure SeparatingProbes (B₁ B₂ : M →ₗ[R] N →ₗ[R] P) : Type _ where
  /-- First slot of the probe pair isolating `B₁`. -/
  v₁ : M
  /-- Second slot of the probe pair isolating `B₁`. -/
  w₁ : N
  /-- The first probe pair sees `B₁`. -/
  apply₁_ne_zero : B₁ v₁ w₁ ≠ 0
  /-- The first probe pair does not see `B₂`. -/
  apply₂_eq_zero : B₂ v₁ w₁ = 0
  /-- First slot of the probe pair isolating `B₂`. -/
  v₂ : M
  /-- Second slot of the probe pair isolating `B₂`. -/
  w₂ : N
  /-- The second probe pair does not see `B₁`. -/
  apply₁_eq_zero : B₁ v₂ w₂ = 0
  /-- The second probe pair sees `B₂`. -/
  apply₂_ne_zero : B₂ v₂ w₂ ≠ 0

end SeparatingProbes

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

/-- Two bilinear maps separated by probe pairs are linearly independent. -/
theorem SeparatingProbes.linearIndependent {B₁ B₂ : M →ₗ[R] N →ₗ[R] P}
    (h : SeparatingProbes B₁ B₂) : LinearIndependent R ![B₁, B₂] :=
  linearIndependent_pair_of_probes h.apply₁_ne_zero h.apply₂_eq_zero h.apply₁_eq_zero
    h.apply₂_ne_zero

end LinearMap
