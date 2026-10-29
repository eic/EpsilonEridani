/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.PauliMatrices.Relations
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The exchange identity of the spatial Pauli matrices

For two spin-`1/2` systems, with spin spaces `ℂ²`, the scalar product of their Pauli vectors is
expressed through the operator exchanging them:

`σ(1) · σ(2) = Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1`,

where `σ(k)` is the Pauli vector of the `k`-th system and `P₁₂ = TensorProduct.comm` swaps the
two tensor factors. In components this is the
completeness relation `Σᵢ (σᵢ)_{αβ} (σᵢ)_{γδ} = 2 δ_{αδ} δ_{βγ} - δ_{αβ} δ_{γδ}` of the spatial
Pauli matrices. Its Lorentz-covariant form, contracting the four-vector of Pauli matrices with the
Minkowski metric, is `PauliMatrix.pauliCo_contr_pauliContr`, stated in Physlib's tensor-tree
formalism; the spatial form here is stated for linear maps on `ℂ² ⊗ ℂ²`, with `ℂ²` the
Hilbert space `EuclideanSpace ℂ (Fin 2)`, where it is used to
decompose the spin space of a pair of spin-`1/2` particles into its singlet and triplet parts.

## Main results

* `PauliMatrix.sum_map_toEuclideanLin_pauliMatrix_inr`: `Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1` on `ℂ² ⊗ ℂ²`.

## References

* P. A. M. Dirac, *Quantum mechanics of many-electron systems*, Proc. R. Soc. Lond. A 123 (1929)
  714.
-/

public section

open Matrix TensorProduct

namespace PauliMatrix

/-- The exchange identity of the spatial Pauli matrices: on `ℂ² ⊗ ℂ²`,
`Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1`, where `P₁₂` exchanges the two tensor factors. -/
theorem sum_map_toEuclideanLin_pauliMatrix_inr :
    ∑ i : Fin 3, TensorProduct.map (toEuclideanLin (pauliMatrix (Sum.inr i)))
      (toEuclideanLin (pauliMatrix (Sum.inr i))) =
      (2 : ℂ) • (TensorProduct.comm ℂ (EuclideanSpace ℂ (Fin 2))
        (EuclideanSpace ℂ (Fin 2))).toLinearMap - 1 := by
  -- The columns of the three Pauli matrices, as multiples of the standard basis vectors.
  have h00 : toEuclideanLin (pauliMatrix (Sum.inr 0)) (EuclideanSpace.single 0 1) =
      (EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2)) := by
    ext k; fin_cases k <;> simp [pauliMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  have h01 : toEuclideanLin (pauliMatrix (Sum.inr 0)) (EuclideanSpace.single 1 1) =
      (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2)) := by
    ext k; fin_cases k <;> simp [pauliMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  have h10 : toEuclideanLin (pauliMatrix (Sum.inr 1)) (EuclideanSpace.single 0 1) =
      Complex.I • (EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2)) := by
    ext k; fin_cases k <;> simp [pauliMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  have h11 : toEuclideanLin (pauliMatrix (Sum.inr 1)) (EuclideanSpace.single 1 1) =
      -Complex.I • (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2)) := by
    ext k; fin_cases k <;> simp [pauliMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  have h20 : toEuclideanLin (pauliMatrix (Sum.inr 2)) (EuclideanSpace.single 0 1) =
      (EuclideanSpace.single 0 1 : EuclideanSpace ℂ (Fin 2)) := by
    ext k; fin_cases k <;> simp [pauliMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  have h21 : toEuclideanLin (pauliMatrix (Sum.inr 2)) (EuclideanSpace.single 1 1) =
      -(EuclideanSpace.single 1 1 : EuclideanSpace ℂ (Fin 2)) := by
    ext k; fin_cases k <;> simp [pauliMatrix, mulVec, dotProduct, Fin.sum_univ_two]
  -- Both sides agree on each of the four product basis vectors `eₐ ⊗ e_b`.
  let b := (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  refine (b.tensorProduct b).ext fun ⟨i, j⟩ ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [b, Fin.sum_univ_three, h00, h01, h10, h11, h20, h21, smul_tmul, tmul_smul, tmul_neg,
      neg_tmul, two_smul, smul_smul] <;> abel

end PauliMatrix
