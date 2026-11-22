/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.Addition
public import EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer

/-!
# Components of the coupled angular momentum and the exchange symmetry

The coupled angular momentum `PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor ρ₁ ρ₂` on
`V ⊗ W` has Cartesian components `J₁ ⊗ 1 + 1 ⊗ J₂`, the diagonal action
`PhyslibAlpha.Sl2.diagEnd` of the two factors. Upstream states this for the ladder operators
(`tensor_Jp`, `tensor_Jm`); this module states it for the Cartesian components, so that results
about `diagEnd`, such as its commutation with an operator on `V ⊗ W`, apply to the total angular
momentum without unfolding `tensor`.

The diagonal action `diagEnd X X` of one endomorphism on the tensor square `M ⊗ M` commutes
with the exchange of the two factors, so it commutes with the symmetrizer and the antisymmetrizer
of `M ⊗ M` (`TensorProduct.symmetrizer`, `TensorProduct.antisymmetrizer`): the symmetric and
antisymmetric parts are invariant under the coupled angular momentum of two copies of one
representation.

## Main results

* `PhyslibAlpha.Sl2.diagEnd_eq_rTensor_add_lTensor`: `diagEnd A B = A ⊗ 1 + 1 ⊗ B`.
* `PhyslibAlpha.Sl2.commute_diagEnd_symmetrizer`,
  `PhyslibAlpha.Sl2.commute_diagEnd_antisymmetrizer`: the diagonal action of an endomorphism on a
  tensor square commutes with both projectors.
* `PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor_Jx`, `tensor_Jy`, `tensor_Jz`:
  `(tensor ρ₁ ρ₂).Jx = diagEnd ρ₁.Jx ρ₂.Jx`, and likewise for `Jy` and `Jz`.
-/

@[expose] public section

namespace PhyslibAlpha.Sl2

section Diagonal

variable {K M N : Type*} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- The defining formula of the diagonal action: `diagEnd A B = A ⊗ 1 + 1 ⊗ B`. -/
theorem diagEnd_eq_rTensor_add_lTensor (A : Module.End K M) (B : Module.End K N) :
    diagEnd A B = A.rTensor N + B.lTensor M :=
  (rfl)

variable [Invertible (2 : K)]

/-- The diagonal action `X ⊗ 1 + 1 ⊗ X` of an endomorphism `X` of `M` commutes with the
symmetrizer of `M ⊗ M`, so the symmetric part is invariant under it. -/
theorem commute_diagEnd_symmetrizer (X : Module.End K M) :
    Commute (diagEnd X X) (TensorProduct.symmetrizer K M) := by
  rw [diagEnd_eq_rTensor_add_lTensor]
  exact TensorProduct.commute_rTensor_add_lTensor_symmetrizer X

/-- The diagonal action `X ⊗ 1 + 1 ⊗ X` of an endomorphism `X` of `M` commutes with the
antisymmetrizer of `M ⊗ M`, so the antisymmetric part is invariant under it. -/
theorem commute_diagEnd_antisymmetrizer (X : Module.End K M) :
    Commute (diagEnd X X) (TensorProduct.antisymmetrizer K M) := by
  rw [diagEnd_eq_rTensor_add_lTensor]
  exact TensorProduct.commute_rTensor_add_lTensor_antisymmetrizer X

end Diagonal

namespace AngularMomentumRepresentation

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The `x`-component of the coupled angular momentum is `ρ₁.Jx ⊗ 1 + 1 ⊗ ρ₂.Jx`. -/
@[simp]
theorem tensor_Jx (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jx = diagEnd ρ₁.Jx ρ₂.Jx :=
  (rfl)

/-- The `y`-component of the coupled angular momentum is `ρ₁.Jy ⊗ 1 + 1 ⊗ ρ₂.Jy`. -/
@[simp]
theorem tensor_Jy (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jy = diagEnd ρ₁.Jy ρ₂.Jy :=
  (rfl)

/-- The `z`-component of the coupled angular momentum is `ρ₁.Jz ⊗ 1 + 1 ⊗ ρ₂.Jz`. -/
@[simp]
theorem tensor_Jz (ρ₁ : AngularMomentumRepresentation V) (ρ₂ : AngularMomentumRepresentation W) :
    (tensor ρ₁ ρ₂).Jz = diagEnd ρ₁.Jz ρ₂.Jz :=
  (rfl)

end AngularMomentumRepresentation

end PhyslibAlpha.Sl2
