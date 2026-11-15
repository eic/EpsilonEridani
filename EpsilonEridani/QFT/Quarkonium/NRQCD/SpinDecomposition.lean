/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer
public import EpsilonEridani.QuantumMechanics.AngularMomentum.SpinHalf
public import Mathlib.LinearAlgebra.Trace

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
antisymmetric and symmetric tensors, and the exchange acts on them by `-1` and `1`. Both commute
with the diagonal action `diagEnd X X = X ⊗ 1 + 1 ⊗ X` of every operator `X` on `ℂ²`
(`PhyslibAlpha.Sl2.commute_diagEnd_antisymmetrizer`, `PhyslibAlpha.Sl2.commute_diagEnd_symmetrizer`,
stated for the tensor square of any vector space). This is the form in
which the total spin acts: the component `(tensor spinHalfRep spinHalfRep).Jx` is by definition
`diagEnd spinHalfRep.Jx spinHalfRep.Jx`, and likewise for `Jy` and `Jz`. Specific to spin `1/2`
are

* the traces `1` and `3` of the two projectors, which over `ℂ` are the dimensions of the two
  channels (that rank statement is not formalised here);
* the total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair, which is `1 + P₁₂`, that is twice the
  triplet projector, so it takes the value `S (S + 1) = 0` on the singlet channel and `2` on the
  triplet channel.

The computation of `S²` is the decomposition `S² = S₁² + S₂² + 2 S(1) · S(2)`
(`PhyslibAlpha.Sl2.AngularMomentumRepresentation.Jsq_tensor`) with `S₁² = S₂² = 3/4`
(`PhyslibAlpha.Sl2.Jsq_spinHalfRep`) and the exchange identity `S(1) · S(2) = (2 P₁₂ - 1) / 4`
of the Pauli matrices (`PhyslibAlpha.Sl2.dot_spinHalfRep_spinHalfRep`), which give
`S² = 1 + P₁₂ = 2 • spinTripletProj` (`PhyslibAlpha.Sl2.Jsq_tensor_spinHalfRep`). Consequently the
exchange operator acts on the channel of total spin `S` by `(-1)^(S + 1)`: this is the spin factor
in the charge-conjugation eigenvalue of a quark-antiquark pair.

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
* `Jsq_tensor_spinHalfRep_mul_spinSingletProj`, `Jsq_tensor_spinHalfRep_mul_spinTripletProj`:
  the total spin squared is `0` on the singlet channel and `2` on the triplet channel.
* `Jsq_tensor_spinHalfRep_apply_of_mem_antisymmetricTensors`,
  `Jsq_tensor_spinHalfRep_apply_of_mem_symmetricTensors`: the same on states, `S² x = 0` for an
  antisymmetric `x` and `S² x = 2 x` for a symmetric `x`.

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

open Matrix TensorProduct PauliMatrix PhyslibAlpha.Sl2

/-- The spin space `ℂ²` of a spin-`1/2` particle. -/
local notation "ℂ²" => EuclideanSpace ℂ (Fin 2)

/-! ### The two projectors -/

/-- The projector `(1 - P₁₂) / 2` onto the spin-singlet channel of a pair of spin-`1/2`
particles, where `P₁₂` exchanges the two spins: the antisymmetrizer of `ℂ² ⊗ ℂ²`. -/
abbrev spinSingletProj : Module.End ℂ (ℂ² ⊗[ℂ] ℂ²) :=
  antisymmetrizer ℂ ℂ²

/-- The projector `(1 + P₁₂) / 2` onto the spin-triplet channel of a pair of spin-`1/2`
particles, where `P₁₂` exchanges the two spins: the symmetrizer of `ℂ² ⊗ ℂ²`. -/
abbrev spinTripletProj : Module.End ℂ (ℂ² ⊗[ℂ] ℂ²) :=
  symmetrizer ℂ ℂ²

/-! ### Traces -/

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

/-! ### The total spin squared -/

/-- The total spin squared vanishes on the singlet channel: `S (S + 1) = 0` for `S = 0`. -/
@[simp]
theorem Jsq_tensor_spinHalfRep_mul_spinSingletProj :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq * spinSingletProj = 0 := by
  rw [Jsq_tensor_spinHalfRep, smul_mul_assoc, symmetrizer_mul_antisymmetrizer, smul_zero]

/-- The total spin squared takes the value `2` on the triplet channel: `S (S + 1) = 2` for
`S = 1`. -/
@[simp]
theorem Jsq_tensor_spinHalfRep_mul_spinTripletProj :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq * spinTripletProj =
      (2 : ℂ) • spinTripletProj := by
  rw [Jsq_tensor_spinHalfRep, smul_mul_assoc, symmetrizer_mul_self]

/-- The total spin squared vanishes on the singlet channel, multiplying from the right. -/
@[simp]
theorem spinSingletProj_mul_Jsq_tensor_spinHalfRep :
    spinSingletProj * (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq = 0 := by
  rw [Jsq_tensor_spinHalfRep, mul_smul_comm, antisymmetrizer_mul_symmetrizer, smul_zero]

/-- The total spin squared takes the value `2` on the triplet channel, multiplying from the
right. -/
@[simp]
theorem spinTripletProj_mul_Jsq_tensor_spinHalfRep :
    spinTripletProj * (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq =
      (2 : ℂ) • spinTripletProj := by
  rw [Jsq_tensor_spinHalfRep, mul_smul_comm, symmetrizer_mul_self]

/-- The total spin squared vanishes on an antisymmetric state, which lies in the singlet
channel: `S² x = 0`. -/
theorem Jsq_tensor_spinHalfRep_apply_of_mem_antisymmetricTensors {x : ℂ² ⊗[ℂ] ℂ²}
    (hx : x ∈ TauCeti.antisymmetricTensors ℂ ℂ²) :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq x = 0 := by
  rw [← (antisymmetrizer_apply_eq_self_iff x).mpr hx, ← Module.End.mul_apply,
    Jsq_tensor_spinHalfRep_mul_spinSingletProj, LinearMap.zero_apply]

/-- The total spin squared takes the value `2` on a symmetric state, which lies in the triplet
channel: `S² x = 2 x`. -/
theorem Jsq_tensor_spinHalfRep_apply_of_mem_symmetricTensors {x : ℂ² ⊗[ℂ] ℂ²}
    (hx : x ∈ TauCeti.symmetricTensors ℂ ℂ²) :
    (AngularMomentumRepresentation.tensor spinHalfRep spinHalfRep).Jsq x = (2 : ℂ) • x := by
  rw [← (symmetrizer_apply_eq_self_iff x).mpr hx, ← Module.End.mul_apply,
    Jsq_tensor_spinHalfRep_mul_spinTripletProj, LinearMap.smul_apply]

end EpsilonEridani.QFT.Quarkonium
