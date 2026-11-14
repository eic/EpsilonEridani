/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.PauliMatrices.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SpinOrbit
import PhyslibAlpha.Relativity.PauliMatrices.SelfAdjoint
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# The Pauli matrices as operators on `ℂ²`, and their exchange identity

The Pauli matrices act on the Hilbert space `ℂ² = EuclideanSpace ℂ (Fin 2)` through
`Matrix.toEuclideanLin`. Each squares to the identity there, and the spin operators of a
spin-`1/2` particle are `Sᵢ = σᵢ / 2` (`PauliMatrix.spinGen`), with `Σᵢ Sᵢ Sᵢ = 3/4`. They
satisfy the su(2) commutation relations `[Sᵢ, Sⱼ] = i Sₖ`, and so form the angular momentum
representation `PauliMatrix.spinRep` of PhyslibAlpha, to which its general results on angular
momentum, such as `J² = J₁² + J₂² + 2 J₁ · J₂` on a tensor product
(`PhyslibAlpha.Sl2.AngularMomentumRepresentation.Jsq_tensor`), apply.

For two spin-`1/2` systems, with spin spaces `ℂ²`, the scalar product of their Pauli vectors is
expressed through the operator exchanging them:

`σ(1) · σ(2) = Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1`,

where `σ(k)` is the Pauli vector of the `k`-th system and `P₁₂ = TensorProduct.comm` swaps the
two tensor factors. In components this is the completeness relation
`Σᵢ (σᵢ)_{αβ} (σᵢ)_{γδ} = 2 δ_{αδ} δ_{βγ} - δ_{αβ} δ_{γδ}` of the spatial Pauli matrices, which
is the Fierz relation `PauliMatrix.sum_pauliLower_mul_pauliLower` of PhyslibAlpha with the
`σ₀ ⊗ σ₀` term split off. For the spin operators it reads `S(1) · S(2) = (2 P₁₂ - 1) / 4`.
Physlib's tensor-tree formalism states the Lorentz-covariant form of the same identity as
`PauliMatrix.pauliCo_contr_pauliContr`.

## Implementation notes

The commutation relations are stated for the commutator bracket of `LieRing.ofAssociativeRing` on
`Module.End ℂ ℂ²`, which Mathlib does not make a global instance; they are the bracket in which
PhyslibAlpha states the fields of `PhyslibAlpha.Sl2.AngularMomentumRepresentation`, and a file that
states or rewrites with them must enable it with
`attribute [local instance 100] LieRing.ofAssociativeRing`.

## Main definitions

* `PauliMatrix.spinGen i`: the spin operator `Sᵢ = σᵢ / 2` on `ℂ²`.
* `PauliMatrix.spinRep`: the spin-`1/2` angular momentum representation on `ℂ²`.

## Main results

* `PauliMatrix.toEuclideanLin_pauliMatrix_mul_self`: each Pauli matrix is an involution on `ℂ²`.
* `PauliMatrix.sum_spinGen_mul_self`: `Σᵢ Sᵢ Sᵢ = 3/4` on `ℂ²`.
* `PauliMatrix.lie_spinGen_zero_one`, `PauliMatrix.lie_spinGen_one_two`,
  `PauliMatrix.lie_spinGen_two_zero`: the su(2) commutation relations `[Sᵢ, Sⱼ] = i Sₖ`.
* `PauliMatrix.Jsq_spinRep`: `J² = 3/4` for spin `1/2`.
* `PauliMatrix.sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr`: `Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1` on
  `ℂ² ⊗ ℂ²`.
* `PauliMatrix.dot_spinRep_spinRep`: `S(1) · S(2) = (2 P₁₂ - 1) / 4` on `ℂ² ⊗ ℂ²`.

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

/-! ### The su(2) commutation relations -/

section Lie

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The commutator of two spin operators, from the commutator of the Pauli matrices:
`[σᵢ, σⱼ] = 2 i σₖ` gives `[Sᵢ, Sⱼ] = i Sₖ`. -/
private theorem lie_spinGen_of_commutator {i j k : Fin 3}
    (h : pauliMatrix (Sum.inr i) * pauliMatrix (Sum.inr j) -
      pauliMatrix (Sum.inr j) * pauliMatrix (Sum.inr i) =
        (2 * Complex.I) • pauliMatrix (Sum.inr k)) :
    ⁅spinGen i, spinGen j⁆ = Complex.I • spinGen k := by
  rw [LieRing.of_associative_ring_bracket, spinGen, spinGen, spinGen, smul_mul_smul_comm,
    smul_mul_smul_comm, ← smul_sub, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
    ← toLpLin_mul_same, ← toLpLin_mul_same, ← map_sub, h, map_smul, smul_smul, smul_smul]
  congr 1
  ring

/-- The spin operators satisfy `[S₁, S₂] = i S₃`. -/
theorem lie_spinGen_zero_one : ⁅spinGen 0, spinGen 1⁆ = Complex.I • spinGen 2 :=
  lie_spinGen_of_commutator σ1_σ2_commutator

/-- The spin operators satisfy `[S₂, S₃] = i S₁`. -/
theorem lie_spinGen_one_two : ⁅spinGen 1, spinGen 2⁆ = Complex.I • spinGen 0 :=
  lie_spinGen_of_commutator σ2_σ3_commutator

/-- The spin operators satisfy `[S₃, S₁] = i S₂`. -/
theorem lie_spinGen_two_zero : ⁅spinGen 2, spinGen 0⁆ = Complex.I • spinGen 1 :=
  lie_spinGen_of_commutator σ3_σ1_commutator

end Lie

/-- The spin-`1/2` angular momentum representation on `ℂ²`, with components `Jᵢ = Sᵢ = σᵢ / 2`. -/
noncomputable def spinRep :
    PhyslibAlpha.Sl2.AngularMomentumRepresentation (EuclideanSpace ℂ (Fin 2)) where
  Jx := spinGen 0
  Jy := spinGen 1
  Jz := spinGen 2
  comm_xy := lie_spinGen_zero_one
  comm_yz := lie_spinGen_one_two
  comm_zx := lie_spinGen_two_zero

/-- The `x`-component of the spin-`1/2` representation is `spinGen 0`. -/
@[simp] theorem spinRep_Jx : spinRep.Jx = spinGen 0 := (rfl)

/-- The `y`-component of the spin-`1/2` representation is `spinGen 1`. -/
@[simp] theorem spinRep_Jy : spinRep.Jy = spinGen 1 := (rfl)

/-- The `z`-component of the spin-`1/2` representation is `spinGen 2`. -/
@[simp] theorem spinRep_Jz : spinRep.Jz = spinGen 2 := (rfl)

/-- The angular momentum squared of spin `1/2`: `J² = s (s + 1) = 3/4`. -/
theorem Jsq_spinRep : spinRep.Jsq = (3 / 4 : ℂ) • 1 := by
  rw [PhyslibAlpha.Sl2.AngularMomentumRepresentation.Jsq, ← sum_spinGen_mul_self,
    Fin.sum_univ_three, spinRep_Jx, spinRep_Jy, spinRep_Jz]

/-- The exchange identity of the spatial Pauli matrices: on `ℂ² ⊗ ℂ²`,
`Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1`, where `P₁₂` exchanges the two tensor factors. -/
theorem sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr :
    ∑ i : Fin 3, TensorProduct.map (toEuclideanLin (pauliMatrix (Sum.inr i)))
      (toEuclideanLin (pauliMatrix (Sum.inr i))) =
      (2 : ℂ) • (TensorProduct.comm ℂ (EuclideanSpace ℂ (Fin 2))
        (EuclideanSpace ℂ (Fin 2))).toLinearMap - 1 := by
  -- The component form `Σᵢ (σᵢ)_{αβ} (σᵢ)_{α'β'} = 2 δ_{α'β} δ_{β'α} - δ_{αβ} δ_{α'β'}`. It is
  -- the Fierz relation `sum_pauliLower_mul_pauliLower α' β' β α`, whose summand is
  -- `(σ_μ)_{αβ} (σ_μ)_{α'β'}` up to the sign `η_μμ² = 1`, with the `μ = 0` term
  -- `(σ₀)_{αβ} (σ₀)_{α'β'} = δ_{αβ} δ_{α'β'}` split off.
  have key : ∀ α α' β β' : Fin 2,
      ∑ i : Fin 3, pauliMatrix (.inr i) α β * pauliMatrix (.inr i) α' β' =
        2 * ((if α' = β then 1 else 0) * (if β' = α then 1 else 0)) -
          (if α = β then 1 else 0) * (if α' = β' then 1 else 0) := by
    intro α α' β β'
    have hη : ∀ μ, pauliLower μ α β * pauliLower μ α' β' =
        pauliMatrix μ α β * pauliMatrix μ α' β' := by
      rintro (μ | μ) <;> fin_cases μ <;> simp [pauliLower_eq_smul, minkowskiMatrixZ]
    have h := sum_pauliLower_mul_pauliLower α' β' β α
    rw [Finset.sum_congr rfl fun μ _ ↦ hη μ, Fintype.sum_sum_type, Finset.univ_unique,
      Finset.sum_singleton, Fin.default_eq_zero, pauliMatrix_inl_zero_eq_one, Matrix.one_apply,
      Matrix.one_apply] at h
    linear_combination h
  -- Compare the matrices of both sides in the product basis `eₐ ⊗ e_b`.
  let b := (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
  apply (LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)).injective
  simp only [map_sum, map_sub, map_smul, LinearMap.toMatrix_one, TensorProduct.toMatrix_comm,
    TensorProduct.toMatrix_map, toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_toLin, b]
  ext ⟨α, α'⟩ ⟨β, β'⟩
  simp only [Matrix.sum_apply, kroneckerMap_apply, key, Matrix.sub_apply, Matrix.smul_apply,
    submatrix_apply, Matrix.one_apply, Prod.swap_prod_mk, id, Prod.mk.injEq, smul_eq_mul]
  grind

/-- The scalar product of the spins of two spin-`1/2` systems, through the exchange identity:
`S(1) · S(2) = (σ(1) · σ(2)) / 4 = (2 P₁₂ - 1) / 4`. -/
theorem dot_spinRep_spinRep :
    PhyslibAlpha.Sl2.AngularMomentumRepresentation.dot spinRep spinRep =
      (4 : ℂ)⁻¹ • ((2 : ℂ) • (TensorProduct.comm ℂ (EuclideanSpace ℂ (Fin 2))
        (EuclideanSpace ℂ (Fin 2))).toLinearMap - 1) := by
  rw [← sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr, Fin.sum_univ_three,
    PhyslibAlpha.Sl2.AngularMomentumRepresentation.dot, spinRep_Jx, spinRep_Jy, spinRep_Jz]
  simp only [spinGen, TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul]
  module

end PauliMatrix
