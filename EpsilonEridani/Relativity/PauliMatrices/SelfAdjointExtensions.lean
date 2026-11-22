/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# The spatial Pauli matrices: completeness and the exchange identity

The Pauli matrices act on the Hilbert space `ℂ² = EuclideanSpace ℂ (Fin 2)` through
`Matrix.toEuclideanLin`. The three spatial Pauli matrices `σ1, σ2, σ3`, which are
`pauliMatrix (Sum.inr i)` for `i = 0, 1, 2`, satisfy `σ1 σ1 + σ2 σ2 + σ3 σ3 = 3`, and the
completeness relation

`Σᵢ (σᵢ)_{αβ} (σᵢ)_{α'β'} = 2 δ_{α'β} δ_{β'α} - δ_{αβ} δ_{α'β'}`,

which is the Fierz relation `PauliMatrix.sum_pauliLower_mul_pauliLower` of PhyslibAlpha with the
`σ0 ⊗ σ0` term split off; this module extends `PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint`,
where that Fierz relation is stated. For two spin-`1/2` systems, with spin spaces `ℂ²`, the
completeness relation expresses the scalar product of their Pauli vectors through the operator
exchanging them:

`σ(1) · σ(2) = Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1`,

where `σ(k)` is the Pauli vector of the `k`-th system and `P₁₂ = TensorProduct.comm` swaps the
two tensor factors. Physlib's tensor-tree formalism states the Lorentz-covariant form of the same
identity as `PauliMatrix.pauliCo_contr_pauliContr`.

## Main results

* `PauliMatrix.sum_pauliMatrix_inr_mul_self`: `σ1 σ1 + σ2 σ2 + σ3 σ3 = 3`.
* `PauliMatrix.sum_pauliMatrix_inr_apply_mul_pauliMatrix_inr_apply`: the completeness relation of
  the spatial Pauli matrices.
* `PauliMatrix.sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr`: `Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1` on
  `ℂ² ⊗ ℂ²`.

## References

* P. A. M. Dirac, *Quantum mechanics of many-electron systems*, Proc. R. Soc. Lond. A 123 (1929)
  714.
-/

@[expose] public section

open Matrix TensorProduct

namespace PauliMatrix

/-- The sum of the squares of the three spatial Pauli matrices: `σ1 σ1 + σ2 σ2 + σ3 σ3 = 3`. -/
theorem sum_pauliMatrix_inr_mul_self :
    ∑ i : Fin 3, pauliMatrix (Sum.inr i) * pauliMatrix (Sum.inr i) = (3 : ℂ) • 1 := by
  simp only [pauliMatrix_mul_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

/-- The completeness relation of the spatial Pauli matrices:
`Σᵢ (σᵢ)_{αβ} (σᵢ)_{α'β'} = 2 δ_{α'β} δ_{β'α} - δ_{αβ} δ_{α'β'}`. -/
theorem sum_pauliMatrix_inr_apply_mul_pauliMatrix_inr_apply (α α' β β' : Fin 2) :
    ∑ i : Fin 3, pauliMatrix (Sum.inr i) α β * pauliMatrix (Sum.inr i) α' β' =
      2 * ((if α' = β then 1 else 0) * (if β' = α then 1 else 0)) -
        (if α = β then 1 else 0) * (if α' = β' then 1 else 0) := by
  -- This is the Fierz relation `sum_pauliLower_mul_pauliLower α' β' β α`, whose summand is
  -- `(σ_μ)_{αβ} (σ_μ)_{α'β'}` up to the sign `η_μμ² = 1`, with the `μ = 0` term
  -- `(σ₀)_{αβ} (σ₀)_{α'β'} = δ_{αβ} δ_{α'β'}` split off.
  have hη : ∀ μ, pauliLower μ α β * pauliLower μ α' β' =
      pauliMatrix μ α β * pauliMatrix μ α' β' := by
    rintro (μ | μ) <;> fin_cases μ <;> simp [pauliLower_eq_smul, minkowskiMatrixZ]
  have h := sum_pauliLower_mul_pauliLower α' β' β α
  rw [Finset.sum_congr rfl fun μ _ ↦ hη μ, Fintype.sum_sum_type, Finset.univ_unique,
    Finset.sum_singleton, Fin.default_eq_zero, pauliMatrix_inl_zero_eq_one, Matrix.one_apply,
    Matrix.one_apply] at h
  linear_combination h

/-- The exchange identity of the spatial Pauli matrices: on `ℂ² ⊗ ℂ²`,
`Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1`, where `P₁₂` exchanges the two tensor factors. -/
theorem sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr :
    ∑ i : Fin 3, TensorProduct.map (toEuclideanLin (pauliMatrix (Sum.inr i)))
      (toEuclideanLin (pauliMatrix (Sum.inr i))) =
      (2 : ℂ) • (TensorProduct.comm ℂ (EuclideanSpace ℂ (Fin 2))
        (EuclideanSpace ℂ (Fin 2))).toLinearMap - 1 := by
  -- Compare the matrices of both sides in the product basis `eₐ ⊗ e_b`.
  let b := (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  apply (LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)).injective
  simp only [map_sum, map_sub, map_smul, LinearMap.toMatrix_one, TensorProduct.toMatrix_comm,
    TensorProduct.toMatrix_map, toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin, b]
  ext ⟨α, α'⟩ ⟨β, β'⟩
  simp only [Matrix.sum_apply, kroneckerMap_apply,
    sum_pauliMatrix_inr_apply_mul_pauliMatrix_inr_apply, Matrix.sub_apply, Matrix.smul_apply,
    submatrix_apply, Matrix.one_apply, Prod.swap_prod_mk, id, Prod.mk.injEq, smul_eq_mul]
  grind

end PauliMatrix
