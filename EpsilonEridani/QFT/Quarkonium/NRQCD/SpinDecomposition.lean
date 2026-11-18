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
spin operators are `spinGen i = pauliMatrix (Sum.inr i) / 2` (so `spinGen 0 = σ1 / 2`), forming the
angular momentum representation `spinHalf`; these and the results below are in the namespace
`PhyslibAlpha.Sl2.AngularMomentumRepresentation` (module
`EpsilonEridani.QuantumMechanics.AngularMomentum.SpinHalf`). The spin space of the pair is
`ℂ² ⊗ ℂ²`, on which the total spin, with components `spinGen i ⊗ 1 + 1 ⊗ spinGen i`, is the
coupled representation `tensor spinHalf spinHalf`.

This module decomposes `2 ⊗ 2 = 1 ⊕ 3` into the spin-singlet and spin-triplet channels, by
symmetry under the operator `P₁₂ = TensorProduct.comm` exchanging the two spins. The singlet
projector is the antisymmetrizer `(1 - P₁₂) / 2` and the triplet projector the symmetrizer
`(1 + P₁₂) / 2` of `ℂ² ⊗ ℂ²`, so the general results on `TensorProduct.antisymmetrizer` and
`TensorProduct.symmetrizer` apply to them: they are complete orthogonal idempotents onto the
antisymmetric and symmetric tensors, and the exchange acts on them by `-1` and `1`. Their traces
are `1` and `3` (`trace_spinSingletProj`, `trace_spinTripletProj`), which over `ℂ` are the
dimensions of the two channels (that rank statement is not formalised here). Since the projectors
are reducible abbreviations, the spin-`1/2` results apply to them directly:

* both commute with every component of the total spin
  (`commute_Jx_tensor_spinHalf_antisymmetrizer`, `commute_Jx_tensor_spinHalf_symmetrizer` and
  their `Jy`, `Jz` analogues), so both channels are invariant under the total spin;
* the total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair is `1 + P₁₂`, that is twice the triplet
  projector (`Jsq_tensor_spinHalf`), so it takes the value `S (S + 1) = 0` on the singlet channel
  and `2` on the triplet channel (`Jsq_tensor_spinHalf_mul_antisymmetrizer`,
  `Jsq_tensor_spinHalf_mul_symmetrizer`, and on states
  `Jsq_tensor_spinHalf_apply_of_mem_antisymmetricTensors`,
  `Jsq_tensor_spinHalf_apply_of_mem_symmetricTensors`).

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

## Main results

* `trace_spinSingletProj`, `trace_spinTripletProj`: the traces `1` and `3`.

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

/-- The singlet projector has trace `1`, which over `ℂ` is the dimension of the singlet channel;
that rank statement is not formalised here. -/
@[simp]
theorem trace_spinSingletProj :
    LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) spinSingletProj = 1 := by
  rw [spinSingletProj, trace_antisymmetrizer, finrank_euclideanSpace_fin, invOf_eq_inv]
  norm_num

/-- The triplet projector has trace `3`, which over `ℂ` is the dimension of the triplet channel;
that rank statement is not formalised here. -/
@[simp]
theorem trace_spinTripletProj :
    LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) spinTripletProj = 3 := by
  rw [spinTripletProj, trace_symmetrizer, finrank_euclideanSpace_fin, invOf_eq_inv]
  norm_num

end EpsilonEridani.QFT.Quarkonium
