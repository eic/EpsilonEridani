/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint

/-!
# The spatial Pauli matrices: completeness

The three spatial Pauli matrices `σ1, σ2, σ3`, which are `pauliMatrix (Sum.inr i)` for
`i = 0, 1, 2`, satisfy the completeness relation

`Σᵢ (σᵢ)_{αβ} (σᵢ)_{α'β'} = 2 δ_{α'β} δ_{β'α} - δ_{αβ} δ_{α'β'}`,

which is the Fierz relation `PauliMatrix.sum_pauliLower_mul_pauliLower` of PhyslibAlpha, stated
in the module this file extends, with the `σ0 ⊗ σ0` term split off. For two spin-`1/2` systems it
gives the exchange identity `σ(1) · σ(2) = 2 P₁₂ - 1`
(`PauliMatrix.sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr`, in
`EpsilonEridani.QuantumMechanics.AngularMomentum.SpinHalf`). Physlib's tensor-tree formalism states
the Lorentz-covariant form of the same identity as `PauliMatrix.pauliCo_contr_pauliContr`.

## Main results

* `PauliMatrix.sum_pauliMatrix_inr_apply_mul_pauliMatrix_inr_apply`: the completeness relation of
  the spatial Pauli matrices.

## References

* P. A. M. Dirac, *Quantum mechanics of many-electron systems*, Proc. R. Soc. Lond. A 123 (1929)
  714.
-/

@[expose] public section

namespace PauliMatrix

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

end PauliMatrix
