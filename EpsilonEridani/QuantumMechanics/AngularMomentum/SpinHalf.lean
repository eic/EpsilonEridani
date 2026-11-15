/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SpinOrbit
public import EpsilonEridani.Relativity.PauliMatrices.BasicExtensions

/-!
# The spin-`1/2` angular momentum representation

The spin operators of a spin-`1/2` particle act on its spin space `ℂ² = EuclideanSpace ℂ (Fin 2)`
as half the spatial Pauli matrices: `S₁, S₂, S₃ = σ1 / 2, σ2 / 2, σ3 / 2`. In Lean the index is
`i : Fin 3`, and `PauliMatrix.spinGen i = pauliMatrix (Sum.inr i) / 2`, so `spinGen 0 = σ1 / 2`
is `S₁`. They satisfy `S₁ S₁ + S₂ S₂ + S₃ S₃ = 3/4` and the su(2) commutation relations
`[S₁, S₂] = i S₃` (cyclically), and so form the angular momentum representation
`PauliMatrix.spinHalfRep` of PhyslibAlpha, to which its general results on angular momentum, such
as `J² = J₁² + J₂² + 2 J₁ · J₂` on a tensor product
(`PhyslibAlpha.Sl2.AngularMomentumRepresentation.Jsq_tensor`), apply.

For two spin-`1/2` systems the exchange identity `σ(1) · σ(2) = 2 P₁₂ - 1` of the Pauli matrices
(`PauliMatrix.sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr`), where `P₁₂ =
TensorProduct.comm` swaps the two tensor factors, gives the scalar product of their spins:
`S(1) · S(2) = (2 P₁₂ - 1) / 4`.

## Implementation notes

The commutation relations are stated for the commutator bracket of `LieRing.ofAssociativeRing` on
`Module.End ℂ ℂ²`, which Mathlib does not make a global instance; they are the bracket in which
PhyslibAlpha states the fields of `PhyslibAlpha.Sl2.AngularMomentumRepresentation`, and a file that
states or rewrites with them must enable it with
`attribute [local instance 100] LieRing.ofAssociativeRing`.

## Main definitions

* `PauliMatrix.spinGen i`: the spin operator `pauliMatrix (Sum.inr i) / 2` on `ℂ²`.
* `PauliMatrix.spinHalfRep`: the spin-`1/2` angular momentum representation on `ℂ²`.

## Main results

* `PauliMatrix.sum_spinGen_mul_self`: `S₁ S₁ + S₂ S₂ + S₃ S₃ = 3/4` on `ℂ²`.
* `PauliMatrix.lie_spinGen_zero_one`, `PauliMatrix.lie_spinGen_one_two`,
  `PauliMatrix.lie_spinGen_two_zero`: the su(2) commutation relations.
* `PauliMatrix.Jsq_spinHalfRep`: `J² = 3/4` for spin `1/2`.
* `PauliMatrix.dot_spinHalfRep_spinHalfRep`: `S(1) · S(2) = (2 P₁₂ - 1) / 4` on `ℂ² ⊗ ℂ²`.
-/

@[expose] public section

open Matrix TensorProduct

namespace PauliMatrix

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
    ← Finset.smul_sum, ← map_sum, sum_pauliMatrix_inr_mul_self, map_smul, toLpLin_one,
    Module.End.one_eq_id, smul_smul]
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
  rw [LieRing.of_associative_ring_bracket, spinGen_def, spinGen_def, spinGen_def,
    smul_mul_smul_comm, smul_mul_smul_comm, ← smul_sub, Module.End.mul_eq_comp,
    Module.End.mul_eq_comp, ← toLpLin_mul_same, ← toLpLin_mul_same, ← map_sub, h, map_smul,
    smul_smul, smul_smul]
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
    PhyslibAlpha.Sl2.AngularMomentumRepresentation (EuclideanSpace ℂ (Fin 2)) where
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
  rw [PhyslibAlpha.Sl2.AngularMomentumRepresentation.Jsq, ← sum_spinGen_mul_self,
    Fin.sum_univ_three, spinHalfRep_Jx, spinHalfRep_Jy, spinHalfRep_Jz]

/-- The scalar product of the spins of two spin-`1/2` systems, through the exchange identity:
`S(1) · S(2) = (σ(1) · σ(2)) / 4 = (2 P₁₂ - 1) / 4`. -/
theorem dot_spinHalfRep_spinHalfRep :
    PhyslibAlpha.Sl2.AngularMomentumRepresentation.dot spinHalfRep spinHalfRep =
      (4 : ℂ)⁻¹ • ((2 : ℂ) • (TensorProduct.comm ℂ (EuclideanSpace ℂ (Fin 2))
        (EuclideanSpace ℂ (Fin 2))).toLinearMap - 1) := by
  rw [← sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr, Fin.sum_univ_three,
    PhyslibAlpha.Sl2.AngularMomentumRepresentation.dot, spinHalfRep_Jx, spinHalfRep_Jy,
    spinHalfRep_Jz]
  simp only [spinGen_def, TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul]
  module

end PauliMatrix
