/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Matrices preserving a bilinear form

A square matrix `Λ` preserves the bilinear form with Gram matrix `g` when `Λᵀ * g * Λ = g`.
It then also preserves the inverse form, `Λ * g⁻¹ * Λᵀ = g⁻¹`; for invertible `g` this is the
statement that raising indices with `g⁻¹` commutes with the action of `Λ`, so that a full
contraction of tensors with lower indices is invariant.

The case `g = 1` is the orthogonal group. Rotating a family `x : ι → M` of vectors in a module by
an orthogonal matrix `A`, `x a ↦ ∑ b, A a b • x b`, leaves every sum `∑ a, B (x a) (y a)` of a
bilinear map `B` invariant.

## Main results

- `Matrix.mul_inv_mul_transpose_eq_inv`: `Λᵀ * g * Λ = g` implies `Λ * g⁻¹ * Λᵀ = g⁻¹`.
- `Matrix.sum_bilin_sum_smul_of_mem_orthogonalGroup`: invariance of `∑ a, B (x a) (y a)` under
  an orthogonal rotation of the families `x` and `y`.
-/

@[expose] public section

namespace Matrix

variable {n ι R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- A matrix preserving a form with Gram matrix `g`, `Λᵀ * g * Λ = g`, also preserves the
inverse form: `Λ * g⁻¹ * Λᵀ = g⁻¹`. (For singular `g` both sides vanish, since then `g⁻¹ = 0`.) -/
theorem mul_inv_mul_transpose_eq_inv {g Λ : Matrix n n R} (hΛ : Λᵀ * g * Λ = g) :
    Λ * g⁻¹ * Λᵀ = g⁻¹ := by
  by_cases hg : IsUnit g.det
  · have h1 : Λᵀ * g * (Λ * g⁻¹) = 1 := by
      rw [← Matrix.mul_assoc, hΛ, mul_nonsing_inv g hg]
    have h2 : Λ * g⁻¹ * (Λᵀ * g) = 1 := by
      rw [← Matrix.mul_assoc] at h1
      exact mul_eq_one_comm.mp (by simpa only [Matrix.mul_assoc] using h1)
    have h3 : Λ * g⁻¹ * Λᵀ * g = 1 := by simpa only [Matrix.mul_assoc] using h2
    exact (inv_eq_left_inv h3).symm
  · simp [nonsing_inv_apply_not_isUnit g hg]

/-- Rotating two families of vectors by the same orthogonal matrix leaves the sum of their
pairings under a bilinear map unchanged. -/
theorem sum_bilin_sum_smul_of_mem_orthogonalGroup [Fintype ι] [DecidableEq ι]
    {M N : Type*} [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (B : M →ₗ[R] M →ₗ[R] N) {A : Matrix ι ι R} (hA : A ∈ orthogonalGroup ι R) (x y : ι → M) :
    ∑ a, B (∑ b, A a b • x b) (∑ c, A a c • y c) = ∑ b, B (x b) (y b) := by
  have hδ (b c : ι) : ∑ a, A a b * A a c = if b = c then 1 else 0 := by
    simpa [Matrix.mul_apply, one_apply] using
      congrFun (congrFun ((mem_orthogonalGroup_iff' ι R).mp hA) b) c
  calc ∑ a, B (∑ b, A a b • x b) (∑ c, A a c • y c)
      = ∑ a, ∑ b, ∑ c, (A a b * A a c) • B (x b) (y c) := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum,
          smul_smul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by rw [mul_comm]
    _ = ∑ b, ∑ c, (∑ a, A a b * A a c) • B (x b) (y c) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.sum_smul]
    _ = ∑ b, B (x b) (y b) := by simp [hδ]

end Matrix
