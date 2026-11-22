/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.QuantumMechanics.AngularMomentum.SpinHalf
public import EpsilonEridani.QuantumMechanics.AngularMomentum.AdditionExtensions
public import EpsilonEridani.Mathematics.RepresentationTheory.Sl2.TensorHighestWeightExtensions

/-!
# The spin singlet and triplet channels of a heavy quark-antiquark pair

The heavy quark and the heavy antiquark each carry spin `1/2`, with spin space `ℂ²` on which the
spin operators are `pauliSpinGen i = pauliMatrix (Sum.inr i) / 2` (so `pauliSpinGen 0 = σ1 / 2`),
forming the angular momentum representation `pauliSpinHalf`. These two definitions, the
spin-`1/2` results on them and the traces below are in the namespace
`PhyslibAlpha.Sl2.AngularMomentumRepresentation` (module
`EpsilonEridani.QuantumMechanics.AngularMomentum.SpinHalf`). The spin space of the pair is
`ℂ² ⊗ ℂ²`, on which the total spin, with components `pauliSpinGen i ⊗ 1 + 1 ⊗ pauliSpinGen i`, is
the coupled representation `tensor pauliSpinHalf pauliSpinHalf`.

This module decomposes `2 ⊗ 2 = 1 ⊕ 3` into the spin-singlet and spin-triplet channels, by
symmetry under the operator `P₁₂ = TensorProduct.comm` exchanging the two spins. The singlet
projector is the antisymmetrizer `TensorProduct.antisymmetrizer ℂ ℂ² = (1 - P₁₂) / 2` and the
triplet projector the symmetrizer `TensorProduct.symmetrizer ℂ ℂ² = (1 + P₁₂) / 2` of `ℂ² ⊗ ℂ²`
(module `EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer`): they are complete
orthogonal idempotents onto the antisymmetric and symmetric tensors, and the exchange acts on them
by `-1` and `1`. Their traces are `1` and `3` (`trace_antisymmetrizer_euclideanSpace_fin_two`,
`trace_symmetrizer_euclideanSpace_fin_two`), which over `ℂ` are the dimensions of the two channels
(that rank statement is not formalised here). Moreover:

* both projectors commute with every component of the total spin, which by `tensor_Jx`,
  `tensor_Jy`, `tensor_Jz` (module
  `EpsilonEridani.QuantumMechanics.AngularMomentum.AdditionExtensions`) is a diagonal action
  `diagEnd X X` (`PhyslibAlpha.Sl2.commute_diagEnd_antisymmetrizer`,
  `PhyslibAlpha.Sl2.commute_diagEnd_symmetrizer`, module
  `EpsilonEridani.Mathematics.RepresentationTheory.Sl2.TensorHighestWeightExtensions`), so both
  channels are invariant under the total spin;
* the total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair is `1 + P₁₂`, that is twice the triplet
  projector (`Jsq_tensor_pauliSpinHalf`), so it takes the value `S (S + 1) = 0` on the singlet
  channel and `2` on the triplet channel (`Jsq_tensor_pauliSpinHalf_mul_antisymmetrizer`,
  `Jsq_tensor_pauliSpinHalf_mul_symmetrizer`, and on states
  `Jsq_tensor_pauliSpinHalf_apply_of_mem_antisymmetricTensors`,
  `Jsq_tensor_pauliSpinHalf_apply_of_mem_symmetricTensors`).

Consequently the exchange operator acts on the channel of total spin `S` by `(-1)^(S + 1)`: this
is the spin factor in the charge-conjugation eigenvalue of a quark-antiquark pair.

The abstract counterpart of this decomposition is the Clebsch-Gordan rule
`V(1) ⊗ V(1) ≅ V(2) ⊕ V(0)` for `sl₂` (`TauCeti.Sl2Std.isInternal_cgSummand`); the results above
give the two channels as explicit projectors in the Pauli convention, together with the exchange
symmetry that distinguishes them. Their colour counterpart is
`EpsilonEridani.QFT.Quarkonium.NRQCD.ColorDecomposition`, the singlet-octet decomposition
`N ⊗ N* = 1 ⊕ adj` of the colour of the pair.

This module gathers these results for the heavy quark-antiquark pair: it imports the modules
that state them and adds no declarations of its own.

## Implementation notes

The spin space is `EuclideanSpace ℂ (Fin 2)`, on which the Pauli matrices act through
`Matrix.toEuclideanLin`, rather than `Fin 2 → ℂ`: over `Fin 2 → ℂ` the `Pi.addCommMonoid` and
`Pi.addCommGroup` instances on the tensor square do not agree syntactically, which keeps
`Module.End ℂ ((Fin 2 → ℂ) ⊗[ℂ] (Fin 2 → ℂ))` from being recognised as a ring and blocks every
ring lemma on the projectors.

## References

* G. T. Bodwin, E. Braaten and G. P. Lepage, *Rigorous QCD analysis of inclusive annihilation and
  production of heavy quarkonium*, Phys. Rev. D 51 (1995) 1125, Section II.
* N. Brambilla et al., *Heavy quarkonium physics*, CERN-2005-005, hep-ph/0412158.
-/
