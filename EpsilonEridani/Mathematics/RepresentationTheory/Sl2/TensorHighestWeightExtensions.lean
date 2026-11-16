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

The diagonal action `PhyslibAlpha.Sl2.diagEnd f f = f ⊗ 1 + 1 ⊗ f` of an endomorphism `f` of `M`
on `M ⊗ M` is the form in which a Lie algebra, such as the angular momentum of
`PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor`, acts on a tensor square. This module
states that it commutes with the symmetrizer and the antisymmetrizer of `M ⊗ M`
(`TensorProduct.symmetrizer`, `TensorProduct.antisymmetrizer`), so the symmetric and the
antisymmetric tensors are invariant under every diagonal action.

## Main results

* `PhyslibAlpha.Sl2.commute_diagEnd_symmetrizer`,
  `PhyslibAlpha.Sl2.commute_diagEnd_antisymmetrizer`: `diagEnd f f` commutes with the two
  projectors of `M ⊗ M`.
-/

@[expose] public section

namespace PhyslibAlpha.Sl2

variable {K M : Type*} [Field K] [Invertible (2 : K)] [AddCommGroup M] [Module K M]

/-- The diagonal action `f ⊗ 1 + 1 ⊗ f` of an endomorphism `f` of `M` commutes with the
symmetrizer of `M ⊗ M`. -/
theorem commute_diagEnd_symmetrizer (f : Module.End K M) :
    Commute (diagEnd f f) (TensorProduct.symmetrizer K M) := by
  rw [diagEnd]
  exact TensorProduct.commute_rTensor_add_lTensor_symmetrizer f

/-- The diagonal action `f ⊗ 1 + 1 ⊗ f` of an endomorphism `f` of `M` commutes with the
antisymmetrizer of `M ⊗ M`. -/
theorem commute_diagEnd_antisymmetrizer (f : Module.End K M) :
    Commute (diagEnd f f) (TensorProduct.antisymmetrizer K M) := by
  rw [diagEnd]
  exact TensorProduct.commute_rTensor_add_lTensor_antisymmetrizer f

end PhyslibAlpha.Sl2
