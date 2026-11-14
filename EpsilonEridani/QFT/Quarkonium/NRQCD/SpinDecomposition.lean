/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer
public import EpsilonEridani.Relativity.PauliMatrices.BasicExtensions
public import Mathlib.LinearAlgebra.Trace

/-!
# The spin singlet and triplet channels of a heavy quark-antiquark pair

The heavy quark and the heavy antiquark each carry spin `1/2`, with spin space `ℂ²` on which the
spin operators are `Sᵢ = σᵢ / 2` (`PauliMatrix.spinGen`), forming the angular momentum
representation `PauliMatrix.spinRep`. The spin space of the pair is `ℂ² ⊗ ℂ²`, on which the total
spin `Sᵢ = S₁ᵢ + S₂ᵢ = Sᵢ ⊗ 1 + 1 ⊗ Sᵢ` is the coupled representation
`PhyslibAlpha.Sl2.AngularMomentumRepresentation.tensor spinRep spinRep`.

This module decomposes `2 ⊗ 2 = 1 ⊕ 3` into the spin-singlet and spin-triplet channels, by
symmetry under the operator `P₁₂ = TensorProduct.comm` exchanging the two spins. The singlet
projector is the antisymmetrizer `(1 - P₁₂) / 2` and the triplet projector the symmetrizer
`(1 + P₁₂) / 2` of `ℂ² ⊗ ℂ²`, so the general results on `TensorProduct.antisymmProj` and
`TensorProduct.symmProj` apply to them: they are complete orthogonal idempotents onto the
antisymmetric and symmetric tensors, the exchange acts on them by `-1` and `1`, and both commute
with the action `X ⊗ 1 + 1 ⊗ X` of every operator `X` on `ℂ²`
(`TensorProduct.commute_toEnd_antisymmProj`), the form in which the total spin acts. Specific to
spin `1/2` are

* the traces `1` and `3` of the two projectors, the dimensions of the two channels;
* the total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair, which is `1 + P₁₂`, that is twice the
  triplet projector, so it takes the value `S (S + 1) = 0` on the singlet channel and `2` on the
  triplet channel.

The computation of `S²` is the decomposition `S² = S₁² + S₂² + 2 S(1) · S(2)`
(`PhyslibAlpha.Sl2.AngularMomentumRepresentation.Jsq_tensor`) with `S₁² = S₂² = 3/4`
(`PauliMatrix.Jsq_spinRep`) and the exchange identity `S(1) · S(2) = (2 P₁₂ - 1) / 4` of the
Pauli matrices (`PauliMatrix.dot_spinRep_spinRep`), which give `S² = 1 + P₁₂`. Consequently the
exchange operator acts on the channel of total spin `S` by `(-1)^(S + 1)`: this is the spin
factor in the charge-conjugation eigenvalue of a quark-antiquark pair.

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
* `Jsq_tensor_spinRep`, `Jsq_tensor_spinRep_mul_spinSingletProj`,
  `Jsq_tensor_spinRep_mul_spinTripletProj`: the total spin squared is `0` on the singlet channel
  and `2` on the triplet channel.

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
  antisymmProj ℂ ℂ²

/-- The projector `(1 + P₁₂) / 2` onto the spin-triplet channel of a pair of spin-`1/2`
particles, where `P₁₂` exchanges the two spins: the symmetrizer of `ℂ² ⊗ ℂ²`. -/
abbrev spinTripletProj : Module.End ℂ (ℂ² ⊗[ℂ] ℂ²) :=
  symmProj ℂ ℂ²

/-! ### Traces -/

/-- The singlet channel is one-dimensional: its projector has trace `1`. -/
@[simp]
theorem trace_spinSingletProj :
    LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) spinSingletProj = 1 := by
  rw [spinSingletProj, trace_antisymmProj, finrank_euclideanSpace_fin, invOf_eq_inv]
  norm_num

/-- The triplet channel is three-dimensional: its projector has trace `3`. -/
@[simp]
theorem trace_spinTripletProj :
    LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) spinTripletProj = 3 := by
  rw [spinTripletProj, trace_symmProj, finrank_euclideanSpace_fin, invOf_eq_inv]
  norm_num

/-! ### The total spin squared -/

/-- The total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair is twice the triplet projector:
`S² = 1 + P₁₂ = 2 P₁`. -/
theorem Jsq_tensor_spinRep :
    (AngularMomentumRepresentation.tensor spinRep spinRep).Jsq = (2 : ℂ) • spinTripletProj := by
  rw [AngularMomentumRepresentation.Jsq_tensor, Jsq_spinRep, dot_spinRep_spinRep, spinTripletProj,
    symmProj_def, LinearMap.rTensor_smul, LinearMap.lTensor_smul, Module.End.one_eq_id,
    LinearMap.rTensor_id, LinearMap.lTensor_id, ← Module.End.one_eq_id, invOf_eq_inv]
  module

/-- The total spin squared vanishes on the singlet channel: `S (S + 1) = 0` for `S = 0`. -/
@[simp]
theorem Jsq_tensor_spinRep_mul_spinSingletProj :
    (AngularMomentumRepresentation.tensor spinRep spinRep).Jsq * spinSingletProj = 0 := by
  rw [Jsq_tensor_spinRep, smul_mul_assoc, symmProj_mul_antisymmProj, smul_zero]

/-- The total spin squared takes the value `2` on the triplet channel: `S (S + 1) = 2` for
`S = 1`. -/
@[simp]
theorem Jsq_tensor_spinRep_mul_spinTripletProj :
    (AngularMomentumRepresentation.tensor spinRep spinRep).Jsq * spinTripletProj =
      (2 : ℂ) • spinTripletProj := by
  rw [Jsq_tensor_spinRep, smul_mul_assoc, symmProj_mul_self]

/-- The total spin squared vanishes on the singlet channel, multiplying from the right. -/
@[simp]
theorem spinSingletProj_mul_Jsq_tensor_spinRep :
    spinSingletProj * (AngularMomentumRepresentation.tensor spinRep spinRep).Jsq = 0 := by
  rw [Jsq_tensor_spinRep, mul_smul_comm, antisymmProj_mul_symmProj, smul_zero]

/-- The total spin squared takes the value `2` on the triplet channel, multiplying from the
right. -/
@[simp]
theorem spinTripletProj_mul_Jsq_tensor_spinRep :
    spinTripletProj * (AngularMomentumRepresentation.tensor spinRep spinRep).Jsq =
      (2 : ℂ) • spinTripletProj := by
  rw [Jsq_tensor_spinRep, mul_smul_comm, symmProj_mul_self]

end EpsilonEridani.QFT.Quarkonium
