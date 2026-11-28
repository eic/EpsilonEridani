/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import PhyslibAlpha.Mathematics.RepresentationTheory.Sl2.TensorHighestWeight
public import EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer

/-!
# The diagonal action and the projectors of a tensor square

The diagonal action `PhyslibAlpha.Sl2.diagEnd A B = A ⊗ 1 + 1 ⊗ B` of two endomorphisms on
`M ⊗ N` is the form in which a Lie algebra, such as the angular momentum of
`PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor`, acts on a tensor product. This module
states its defining formula as a lemma, so that consumers need not unfold `diagEnd`, and proves
that on a tensor square the diagonal action `diagEnd X X` of one endomorphism commutes with the
symmetrizer and the antisymmetrizer of `M ⊗ M` (`TensorProduct.symmetrizer`,
`TensorProduct.antisymmetrizer`): the symmetric and antisymmetric tensors are invariant under
every diagonal action.

## Main results

* `PhyslibAlpha.Sl2.diagEnd_eq_rTensor_add_lTensor`: `diagEnd A B = A ⊗ 1 + 1 ⊗ B`.
* `PhyslibAlpha.Sl2.commute_diagEnd_symmetrizer`,
  `PhyslibAlpha.Sl2.commute_diagEnd_antisymmetrizer`: `diagEnd X X` commutes with the two
  projectors of `M ⊗ M`.
-/

public section

namespace PhyslibAlpha.Sl2

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

end PhyslibAlpha.Sl2
