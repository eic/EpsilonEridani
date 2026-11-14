/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.PauliMatrices.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# The Pauli matrices as operators on `ℂ²`, and their exchange identity

The Pauli matrices act on the Hilbert space `ℂ² = EuclideanSpace ℂ (Fin 2)` through
`Matrix.toEuclideanLin`. Each squares to the identity there, and the spin operators of a
spin-`1/2` particle are `Sᵢ = σᵢ / 2` (`PauliMatrix.spinGen`), with `Σᵢ Sᵢ Sᵢ = 3/4`.

For two spin-`1/2` systems, with spin spaces `ℂ²`, the scalar product of their Pauli vectors is
expressed through the operator exchanging them:

`σ(1) · σ(2) = Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1`,

where `σ(k)` is the Pauli vector of the `k`-th system and `P₁₂ = TensorProduct.comm` swaps the
two tensor factors. In components this is the completeness relation
`Σᵢ (σᵢ)_{αβ} (σᵢ)_{γδ} = 2 δ_{αδ} δ_{βγ} - δ_{αβ} δ_{γδ}` of the spatial Pauli matrices, which
is the Fierz relation `PauliMatrix.sum_pauliLower_mul_pauliLower` of PhyslibAlpha with the
`σ₀ ⊗ σ₀` term split off; the proof transports it to operators on `ℂ² ⊗ ℂ²` through the matrix of
an operator in the product basis. Physlib's tensor-tree formalism states the Lorentz-covariant
form of the same identity as `PauliMatrix.pauliCo_contr_pauliContr`.

## Main definitions

* `PauliMatrix.spinGen i`: the spin operator `Sᵢ = σᵢ / 2` on `ℂ²`.

## Main results

* `PauliMatrix.toEuclideanLin_pauliMatrix_mul_self`: each Pauli matrix is an involution on `ℂ²`.
* `PauliMatrix.sum_spinGen_mul_self`: `Σᵢ Sᵢ Sᵢ = 3/4` on `ℂ²`.
* `PauliMatrix.sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr`: `Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1` on
  `ℂ² ⊗ ℂ²`.

## References

* P. A. M. Dirac, *Quantum mechanics of many-electron systems*, Proc. R. Soc. Lond. A 123 (1929)
  714.
-/

@[expose] public section

open Matrix TensorProduct

namespace PauliMatrix

/-- Each Pauli matrix squares to the identity as an operator on `ℂ²`. -/
@[simp]
theorem toEuclideanLin_pauliMatrix_mul_self (μ : Fin 1 ⊕ Fin 3) :
    toEuclideanLin (pauliMatrix μ) * toEuclideanLin (pauliMatrix μ) = 1 := by
  rw [Module.End.mul_eq_comp, ← toLpLin_mul_same, pauliMatrix_mul_self, toLpLin_one,
    Module.End.one_eq_id]

/-- The spin operator `Sᵢ = σᵢ / 2` of a spin-`1/2` particle, acting on its spin space `ℂ²`. -/
noncomputable def spinGen (i : Fin 3) : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (2 : ℂ)⁻¹ • toEuclideanLin (pauliMatrix (Sum.inr i))

/-- The spin operator applied to a state: `Sᵢ v = σᵢ v / 2`. -/
@[simp]
theorem spinGen_apply (i : Fin 3) (v : EuclideanSpace ℂ (Fin 2)) :
    spinGen i v = (2 : ℂ)⁻¹ • toEuclideanLin (pauliMatrix (Sum.inr i)) v := by
  simp [spinGen]

/-- The spin Casimir of a single spin-`1/2` particle: `Σᵢ Sᵢ Sᵢ = s (s + 1) = 3/4`. -/
theorem sum_spinGen_mul_self : ∑ i : Fin 3, spinGen i * spinGen i = (3 / 4 : ℂ) • 1 := by
  simp only [spinGen, smul_mul_smul_comm, toEuclideanLin_pauliMatrix_mul_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  module

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
  -- The Fierz relation, with the `σ₀ ⊗ σ₀` term split off from the three spatial ones.
  have h := sum_pauliLower_mul_pauliLower α' β' β α
  simp only [Fintype.sum_sum_type, pauliLower_eq_smul, minkowskiMatrixZ] at h
  simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, diagonal_apply_eq,
    Sum.elim_inl, Pi.one_apply, Int.cast_one, Matrix.smul_apply, smul_eq_mul, one_mul,
    Finset.sum_singleton, Sum.elim_inr, Pi.neg_apply, Int.reduceNeg, Int.cast_neg, neg_mul,
    mul_neg, neg_neg, mul_ite, mul_one, mul_zero, Matrix.sum_apply, kroneckerMap_apply,
    Matrix.sub_apply, submatrix_apply] at h ⊢
  rw [eq_sub_of_add_eq' h, pauliMatrix_inl_zero_eq_one]
  simp only [Matrix.one_apply]
  grind

end PauliMatrix
