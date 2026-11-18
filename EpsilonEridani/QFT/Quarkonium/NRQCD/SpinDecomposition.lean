/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer
public import EpsilonEridani.QuantumMechanics.AngularMomentum.SpinHalf

/-!
# The spin singlet and triplet channels of a heavy quark-antiquark pair

The heavy quark and the heavy antiquark each carry spin `1/2`, with spin space `ℂ²` on which the
spin operators are `spinGen i = pauliMatrix (Sum.inr i) / 2` (`PhyslibAlpha.Sl2.spinGen`, so
`spinGen 0 = σ1 / 2`), forming the angular momentum representation `PhyslibAlpha.Sl2.spinHalfRep`.
The spin space of the pair is `ℂ² ⊗ ℂ²`, on which the total spin, with components
`spinGen i ⊗ 1 + 1 ⊗ spinGen i`, is the coupled representation
`PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep`.

This module decomposes `2 ⊗ 2 = 1 ⊕ 3` into the spin-singlet and spin-triplet channels, by
symmetry under the operator `P₁₂ = TensorProduct.comm` exchanging the two spins. The singlet
projector is the antisymmetrizer `(1 - P₁₂) / 2` and the triplet projector the symmetrizer
`(1 + P₁₂) / 2` of `ℂ² ⊗ ℂ²`, so the general results on `TensorProduct.antisymmetrizer` and
`TensorProduct.symmetrizer` apply to them: they are complete orthogonal idempotents onto the
antisymmetric and symmetric tensors, and the exchange acts on them by `-1` and `1`. Since the
projectors are reducible abbreviations, the results on the spin-`1/2` representation in
`EpsilonEridani.QuantumMechanics.AngularMomentum.SpinHalf` apply to them directly:

* their traces are `1` and `3` (`PhyslibAlpha.Sl2.trace_antisymmetrizer_euclideanSpace_fin_two`,
  `PhyslibAlpha.Sl2.trace_symmetrizer_euclideanSpace_fin_two`), which over `ℂ` are the dimensions
  of the two channels (that rank statement is not formalised here);
* both commute with every component of the total spin
  (`PhyslibAlpha.Sl2.commute_Jx_tensor_spinHalfRep_antisymmetrizer`,
  `PhyslibAlpha.Sl2.commute_Jx_tensor_spinHalfRep_symmetrizer` and their `Jy`, `Jz` analogues), so
  both channels are invariant under the total spin;
* the total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair is `1 + P₁₂`, that is twice the triplet
  projector (`PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep`), so it takes the value `S (S + 1) = 0` on
  the singlet channel and `2` on the triplet channel
  (`PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_mul_antisymmetrizer`,
  `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_mul_symmetrizer`, and on states
  `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_apply_of_mem_antisymmetricTensors`,
  `PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep_apply_of_mem_symmetricTensors`).

Consequently the exchange operator acts on the channel of total spin `S` by `(-1)^(S + 1)`: this
is the spin factor in the charge-conjugation eigenvalue of a quark-antiquark pair.

The abstract counterpart of this decomposition is the Clebsch-Gordan rule
`V(1) ⊗ V(1) ≅ V(2) ⊕ V(0)` for `sl₂` (`TauCeti.Sl2Std.isInternal_cgSummand`); this file gives
the two channels as explicit projectors in the Pauli convention, together with the exchange
symmetry that distinguishes them. Its colour counterpart, whose structure this file follows, is
`EpsilonEridani.QFT.Quarkonium.NRQCD.ColorDecomposition`, the singlet-octet decomposition
`N ⊗ N* = 1 ⊕ adj` of the colour of the pair.

## Main definitions

* `spinSingletProj`, `spinTripletProj`: the projectors onto the two spin channels of the pair.

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

public section

noncomputable section

namespace EpsilonEridani.QFT.Quarkonium

open TensorProduct

/-- The spin space `ℂ²` of a spin-`1/2` particle. -/
local notation "ℂ²" => EuclideanSpace ℂ (Fin 2)

/-- The projector `(1 - P₁₂) / 2` onto the spin-singlet channel of a pair of spin-`1/2`
particles, where `P₁₂` exchanges the two spins: the antisymmetrizer of `ℂ² ⊗ ℂ²`. -/
abbrev spinSingletProj : Module.End ℂ (ℂ² ⊗[ℂ] ℂ²) :=
  antisymmetrizer ℂ ℂ²

/-- The projector `(1 + P₁₂) / 2` onto the spin-triplet channel of a pair of spin-`1/2`
particles, where `P₁₂` exchanges the two spins: the symmetrizer of `ℂ² ⊗ ℂ²`. -/
abbrev spinTripletProj : Module.End ℂ (ℂ² ⊗[ℂ] ℂ²) :=
  symmetrizer ℂ ℂ²

end EpsilonEridani.QFT.Quarkonium
