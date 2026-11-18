/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SpinOrbit
public import EpsilonEridani.Relativity.PauliMatrices.BasicExtensions
public import EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer
public import EpsilonEridani.QuantumMechanics.AngularMomentum.AdditionExtensions

/-!
# The spin-`1/2` angular momentum representation

The spin operators of a spin-`1/2` particle act on its spin space `ℂ² = EuclideanSpace ℂ (Fin 2)`
as half the spatial Pauli matrices: `S₁, S₂, S₃ = σ1 / 2, σ2 / 2, σ3 / 2`. In Lean the index is
`i : Fin 3`, and `PhyslibAlpha.Sl2.spinGen i = pauliMatrix (Sum.inr i) / 2`, so `spinGen 0 = σ1 / 2`
is `S₁`. They satisfy `S₁ S₁ + S₂ S₂ + S₃ S₃ = 3/4` and the su(2) commutation relations
`[S₁, S₂] = i S₃` (cyclically), and so form the angular momentum representation
`PhyslibAlpha.Sl2.spinHalfRep` of PhyslibAlpha, to which its general results on angular momentum,
such as `J² = J₁² + J₂² + 2 J₁ · J₂` on a tensor product
(`PhyslibAlpha.Sl2.AngularMomentumRepresentation.Jsq_tensor`), apply.

For two spin-`1/2` systems the exchange identity `σ(1) · σ(2) = 2 P₁₂ - 1` of the Pauli matrices
(`PauliMatrix.sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr`), where `P₁₂ =
TensorProduct.comm` swaps the two tensor factors, gives the scalar product of their spins:
`S(1) · S(2) = (2 P₁₂ - 1) / 4`. Their total spin squared is then
`S² = S(1)² + S(2)² + 2 S(1) · S(2) = 1 + P₁₂`, twice the symmetrizer `TensorProduct.symmetrizer`
of `ℂ² ⊗ ℂ²`. The total spin acts on `ℂ² ⊗ ℂ²` through the diagonal action
`diagEnd X X = X ⊗ 1 + 1 ⊗ X`, which commutes with the symmetrizer and the antisymmetrizer of the
tensor square of any module (`TensorProduct.commute_rTensor_add_lTensor_symmetrizer`,
`TensorProduct.commute_rTensor_add_lTensor_antisymmetrizer`), so the antisymmetric part, the
spin-singlet channel, and the symmetric part, the spin-triplet channel, are invariant under the
total spin. On them the total spin squared takes the values `S (S + 1) = 0` and `2`, and the
traces `1` and `3` of the two projectors are, over `ℂ`, the dimensions of the two channels.

## Implementation notes

The commutation relations are stated for the commutator bracket of `LieRing.ofAssociativeRing` on
`Module.End ℂ ℂ²`, which Mathlib does not make a global instance; they are the bracket in which
PhyslibAlpha states the fields of `PhyslibAlpha.Sl2.AngularMomentumRepresentation`, and a file that
states or rewrites with them must enable it with
`attribute [local instance 100] LieRing.ofAssociativeRing`.

## Main definitions

* `PhyslibAlpha.Sl2.spinGen i`: the spin operator `pauliMatrix (Sum.inr i) / 2` on `ℂ²`.
* `PhyslibAlpha.Sl2.spinHalfRep`: the spin-`1/2` angular momentum representation on `ℂ²`.

## Main results

* `PhyslibAlpha.Sl2.sum_spinGen_mul_self`: `S₁ S₁ + S₂ S₂ + S₃ S₃ = 3/4` on `ℂ²`.
* `PhyslibAlpha.Sl2.lie_spinGen_zero_one`, `PhyslibAlpha.Sl2.lie_spinGen_one_two`,
  `PhyslibAlpha.Sl2.lie_spinGen_two_zero`: the su(2) commutation relations.
* `PhyslibAlpha.Sl2.Jsq_spinHalfRep`: `J² = 3/4` for spin `1/2`.
* `PhyslibAlpha.Sl2.dot_spinHalfRep_spinHalfRep`: `S(1) · S(2) = (2 P₁₂ - 1) / 4` on `ℂ² ⊗ ℂ²`.
* `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep`: the total spin squared of two spin-`1/2` systems is
  twice the symmetrizer of `ℂ² ⊗ ℂ²`.
* `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_apply_of_mem_antisymmetricTensors`,
  `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_apply_of_mem_symmetricTensors`: the total spin squared
  is `0` on an antisymmetric state and `2` on a symmetric state of `ℂ² ⊗ ℂ²`.
* `PhyslibAlpha.Sl2.trace_antisymmetrizer_euclideanSpace_fin_two`,
  `PhyslibAlpha.Sl2.trace_symmetrizer_euclideanSpace_fin_two`: the traces `1` and `3` of the two
  projectors of `ℂ² ⊗ ℂ²`.
* `PhyslibAlpha.Sl2.commute_Jx_tensor_spinHalfRep_antisymmetrizer`,
  `PhyslibAlpha.Sl2.commute_Jx_tensor_spinHalfRep_symmetrizer` and their `Jy`, `Jz` analogues:
  both projectors commute with the total spin.
* `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_mul_antisymmetrizer`,
  `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_mul_symmetrizer` and their right-multiplied forms:
  the total spin squared is `0` on the antisymmetric and `2` on the symmetric part.
-/

@[expose] public section

open Matrix TensorProduct PauliMatrix

namespace PhyslibAlpha.Sl2

/-- The spin operator `pauliMatrix (Sum.inr i) / 2` of a spin-`1/2` particle, acting on its spin
space `ℂ²`; `spinGen 0`, `spinGen 1`, `spinGen 2` are `S₁ = σ1 / 2`, `S₂ = σ2 / 2`,
`S₃ = σ3 / 2`. -/
noncomputable def spinGen (i : Fin 3) : Module.End ℂ (EuclideanSpace ℂ (Fin 2)) :=
  (2 : ℂ)⁻¹ • toEuclideanLin (pauliMatrix (Sum.inr i))

/-- The defining formula of the spin operator: `spinGen i = pauliMatrix (Sum.inr i) / 2`. -/
theorem spinGen_def (i : Fin 3) :
    spinGen i = (2 : ℂ)⁻¹ • toEuclideanLin (pauliMatrix (Sum.inr i)) :=
  (rfl)

/-- The spin operator applied to a state: `spinGen i v = pauliMatrix (Sum.inr i) v / 2`. -/
@[simp]
theorem spinGen_apply (i : Fin 3) (v : EuclideanSpace ℂ (Fin 2)) :
    spinGen i v = (2 : ℂ)⁻¹ • toEuclideanLin (pauliMatrix (Sum.inr i)) v := by
  simp [spinGen_def]

/-- The spin Casimir of a single spin-`1/2` particle:
`S₁ S₁ + S₂ S₂ + S₃ S₃ = s (s + 1) = 3/4`. -/
theorem sum_spinGen_mul_self : ∑ i : Fin 3, spinGen i * spinGen i = (3 / 4 : ℂ) • 1 := by
  simp only [spinGen_def, smul_mul_smul_comm, Module.End.mul_eq_comp, ← toLpLin_mul_same,
    ← Finset.smul_sum, ← map_sum, sum_pauliMatrix_inr_mul_self, map_smul,
    toLpLin_one, ← Module.End.one_eq_id, smul_smul]
  norm_num

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
  simp only [LieRing.of_associative_ring_bracket, spinGen_def, smul_mul_smul_comm, ← smul_sub,
    Module.End.mul_eq_comp, ← toLpLin_mul_same, ← map_sub, h, map_smul, smul_smul]
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

/-- The spin-`1/2` angular momentum representation on `ℂ²`, with components
`Jx, Jy, Jz = spinGen 0, spinGen 1, spinGen 2`, that is `σ1 / 2, σ2 / 2, σ3 / 2`. -/
noncomputable def spinHalfRep :
    AngularMomentumRepresentation (EuclideanSpace ℂ (Fin 2)) where
  Jx := spinGen 0
  Jy := spinGen 1
  Jz := spinGen 2
  comm_xy := lie_spinGen_zero_one
  comm_yz := lie_spinGen_one_two
  comm_zx := lie_spinGen_two_zero

/-- The `x`-component of the spin-`1/2` representation is `spinGen 0`. -/
@[simp] theorem spinHalfRep_Jx : spinHalfRep.Jx = spinGen 0 := (rfl)

/-- The `y`-component of the spin-`1/2` representation is `spinGen 1`. -/
@[simp] theorem spinHalfRep_Jy : spinHalfRep.Jy = spinGen 1 := (rfl)

/-- The `z`-component of the spin-`1/2` representation is `spinGen 2`. -/
@[simp] theorem spinHalfRep_Jz : spinHalfRep.Jz = spinGen 2 := (rfl)

/-- The angular momentum squared of spin `1/2`: `J² = s (s + 1) = 3/4`. -/
theorem Jsq_spinHalfRep : spinHalfRep.Jsq = (3 / 4 : ℂ) • 1 := by
  rw [AngularMomentumRepresentation.Jsq, ← sum_spinGen_mul_self,
    Fin.sum_univ_three, spinHalfRep_Jx, spinHalfRep_Jy, spinHalfRep_Jz]

/-- The scalar product of the spins of two spin-`1/2` systems, through the exchange identity:
`S(1) · S(2) = (σ(1) · σ(2)) / 4 = (2 P₁₂ - 1) / 4`. -/
theorem dot_spinHalfRep_spinHalfRep :
    AngularMomentumRepresentation.dot spinHalfRep spinHalfRep =
      (4 : ℂ)⁻¹ • ((2 : ℂ) • (TensorProduct.comm ℂ (EuclideanSpace ℂ (Fin 2))
        (EuclideanSpace ℂ (Fin 2))).toLinearMap - 1) := by
  rw [← sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr]
  simp only [AngularMomentumRepresentation.dot, Fin.sum_univ_three, spinHalfRep_Jx, spinHalfRep_Jy,
    spinHalfRep_Jz, spinGen_def, TensorProduct.map_smul_left, TensorProduct.map_smul_right,
    smul_smul]
  module

/-! ### Two spin-`1/2` systems -/

/-- The total spin squared `S² = Σᵢ Sᵢ Sᵢ` of two spin-`1/2` systems is twice the symmetrizer of
`ℂ² ⊗ ℂ²`: `S² = 1 + P₁₂ = 2 • symmetrizer`, where `P₁₂` exchanges the two spins. -/
theorem Jsq_tensor_spinHalfRep :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq =
      (2 : ℂ) • TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2)) := by
  rw [AngularMomentumRepresentation.Jsq_tensor, Jsq_spinHalfRep, dot_spinHalfRep_spinHalfRep,
    TensorProduct.symmetrizer_def]
  simp only [LinearMap.rTensor_smul, LinearMap.lTensor_smul, Module.End.one_eq_id,
    LinearMap.rTensor_id, LinearMap.lTensor_id, invOf_eq_inv]
  module

/-- The total spin squared of two spin-`1/2` systems vanishes on an antisymmetric state, which lies
in the singlet channel: `S² x = 0`. -/
theorem Jsq_tensor_spinHalfRep_apply_of_mem_antisymmetricTensors
    {x : EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)}
    (hx : x ∈ TauCeti.antisymmetricTensors ℂ (EuclideanSpace ℂ (Fin 2))) :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq x = 0 := by
  rw [← (antisymmetrizer_apply_eq_self_iff x).mpr hx, ← Module.End.mul_apply,
    Jsq_tensor_spinHalfRep, smul_mul_assoc, symmetrizer_mul_antisymmetrizer, smul_zero,
    LinearMap.zero_apply]

/-- The total spin squared of two spin-`1/2` systems takes the value `2` on a symmetric state,
which lies in the triplet channel: `S² x = 2 x`. -/
theorem Jsq_tensor_spinHalfRep_apply_of_mem_symmetricTensors
    {x : EuclideanSpace ℂ (Fin 2) ⊗[ℂ] EuclideanSpace ℂ (Fin 2)}
    (hx : x ∈ TauCeti.symmetricTensors ℂ (EuclideanSpace ℂ (Fin 2))) :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq x = (2 : ℂ) • x := by
  rw [← (symmetrizer_apply_eq_self_iff x).mpr hx, ← Module.End.mul_apply,
    Jsq_tensor_spinHalfRep, smul_mul_assoc, symmetrizer_mul_self, LinearMap.smul_apply]

/-- The antisymmetrizer of `ℂ² ⊗ ℂ²` has trace `1`, which over `ℂ` is the dimension of the
spin-singlet channel; that rank statement is not formalised here. -/
@[simp]
theorem trace_antisymmetrizer_euclideanSpace_fin_two :
    LinearMap.trace ℂ _ (TensorProduct.antisymmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) = 1 := by
  rw [trace_antisymmetrizer, finrank_euclideanSpace_fin, invOf_eq_inv]
  norm_num

/-- The symmetrizer of `ℂ² ⊗ ℂ²` has trace `3`, which over `ℂ` is the dimension of the
spin-triplet channel; that rank statement is not formalised here. -/
@[simp]
theorem trace_symmetrizer_euclideanSpace_fin_two :
    LinearMap.trace ℂ _ (TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) = 3 := by
  rw [trace_symmetrizer, finrank_euclideanSpace_fin, invOf_eq_inv]
  norm_num

/-- The antisymmetric part of `ℂ² ⊗ ℂ²` is invariant under the `x`-component of the total spin. -/
theorem commute_Jx_tensor_spinHalfRep_antisymmetrizer :
    Commute (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jx
      (TensorProduct.antisymmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) := by
  rw [AngularMomentumRepresentation.tensor_Jx, diagEnd]
  exact commute_rTensor_add_lTensor_antisymmetrizer _

/-- The antisymmetric part of `ℂ² ⊗ ℂ²` is invariant under the `y`-component of the total spin. -/
theorem commute_Jy_tensor_spinHalfRep_antisymmetrizer :
    Commute (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jy
      (TensorProduct.antisymmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) := by
  rw [AngularMomentumRepresentation.tensor_Jy, diagEnd]
  exact commute_rTensor_add_lTensor_antisymmetrizer _

/-- The antisymmetric part of `ℂ² ⊗ ℂ²` is invariant under the `z`-component of the total spin. -/
theorem commute_Jz_tensor_spinHalfRep_antisymmetrizer :
    Commute (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jz
      (TensorProduct.antisymmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) := by
  rw [AngularMomentumRepresentation.tensor_Jz, diagEnd]
  exact commute_rTensor_add_lTensor_antisymmetrizer _

/-- The symmetric part of `ℂ² ⊗ ℂ²` is invariant under the `x`-component of the total spin. -/
theorem commute_Jx_tensor_spinHalfRep_symmetrizer :
    Commute (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jx
      (TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) := by
  rw [AngularMomentumRepresentation.tensor_Jx, diagEnd]
  exact commute_rTensor_add_lTensor_symmetrizer _

/-- The symmetric part of `ℂ² ⊗ ℂ²` is invariant under the `y`-component of the total spin. -/
theorem commute_Jy_tensor_spinHalfRep_symmetrizer :
    Commute (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jy
      (TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) := by
  rw [AngularMomentumRepresentation.tensor_Jy, diagEnd]
  exact commute_rTensor_add_lTensor_symmetrizer _

/-- The symmetric part of `ℂ² ⊗ ℂ²` is invariant under the `z`-component of the total spin. -/
theorem commute_Jz_tensor_spinHalfRep_symmetrizer :
    Commute (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jz
      (TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2))) := by
  rw [AngularMomentumRepresentation.tensor_Jz, diagEnd]
  exact commute_rTensor_add_lTensor_symmetrizer _

/-- The total spin squared of two spin-`1/2` systems vanishes on the antisymmetric part, the
singlet channel: `S (S + 1) = 0` for `S = 0`. -/
@[simp]
theorem Jsq_tensor_spinHalfRep_mul_antisymmetrizer :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq *
      TensorProduct.antisymmetrizer ℂ (EuclideanSpace ℂ (Fin 2)) = 0 := by
  rw [Jsq_tensor_spinHalfRep, smul_mul_assoc, symmetrizer_mul_antisymmetrizer, smul_zero]

/-- The total spin squared of two spin-`1/2` systems takes the value `2` on the symmetric part,
the triplet channel: `S (S + 1) = 2` for `S = 1`. -/
@[simp]
theorem Jsq_tensor_spinHalfRep_mul_symmetrizer :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq *
      TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2)) =
        (2 : ℂ) • TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2)) := by
  rw [Jsq_tensor_spinHalfRep, smul_mul_assoc, symmetrizer_mul_self]

/-- The total spin squared of two spin-`1/2` systems vanishes on the antisymmetric part,
multiplying from the right. -/
@[simp]
theorem antisymmetrizer_mul_Jsq_tensor_spinHalfRep :
    TensorProduct.antisymmetrizer ℂ (EuclideanSpace ℂ (Fin 2)) *
      (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq = 0 := by
  rw [Jsq_tensor_spinHalfRep, mul_smul_comm, antisymmetrizer_mul_symmetrizer, smul_zero]

/-- The total spin squared of two spin-`1/2` systems takes the value `2` on the symmetric part,
multiplying from the right. -/
@[simp]
theorem symmetrizer_mul_Jsq_tensor_spinHalfRep :
    TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2)) *
      (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq =
        (2 : ℂ) • TensorProduct.symmetrizer ℂ (EuclideanSpace ℂ (Fin 2)) := by
  rw [Jsq_tensor_spinHalfRep, mul_smul_comm, symmetrizer_mul_self]

end PhyslibAlpha.Sl2
