/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LieAlgebra.Casimir
public import EpsilonEridani.Mathematics.LinearAlgebra.TensorProduct.Symmetrizer
public import EpsilonEridani.Relativity.PauliMatrices.BasicExtensions
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.Trace

/-!
# The spin singlet and triplet channels of a heavy quark-antiquark pair

The heavy quark and the heavy antiquark each carry spin `1/2`, with spin space `ℂ²` on which the
spin operators are `Sᵢ = σᵢ / 2` (`PauliMatrix.spinGen`). The spin space of the pair is
`ℂ² ⊗ ℂ²`, on which an operator `X` on `ℂ²` acts through the tensor-product Lie module,
`X ↦ X ⊗ 1 + 1 ⊗ X`; for `X = Sᵢ` this is the total spin `Sᵢ = S₁ᵢ + S₂ᵢ` of the pair.

This module decomposes `2 ⊗ 2 = 1 ⊕ 3` into the spin-singlet and spin-triplet channels, by
symmetry under the operator `P₁₂ = TensorProduct.comm` exchanging the two spins. The singlet
projector is the antisymmetrizer `(1 - P₁₂) / 2` and the triplet projector the symmetrizer
`(1 + P₁₂) / 2` of `ℂ² ⊗ ℂ²`, so the general results on `TensorProduct.antisymmProj` and
`TensorProduct.symmProj` apply to them: they are complete orthogonal idempotents, the exchange
acts on them by `-1` and `1`, and both commute with the action of every operator on `ℂ²`
(`TensorProduct.commute_toEnd_antisymmProj`), in particular with the total spin. Specific to
spin `1/2` are

* the traces `1` and `3` of the two projectors, the dimensions of the two channels;
* the total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair, which is `1 + P₁₂`, that is twice the
  triplet projector, so it takes the value `S (S + 1) = 0` on the singlet channel and `2` on the
  triplet channel.

The computation of `S²` rests on the exchange identity `Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1` of the Pauli
matrices (`PauliMatrix.sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr`), which with
`Σᵢ Sᵢ Sᵢ = 3/4` on `ℂ²` gives `S² = 3/2 + (σ(1) · σ(2)) / 2 = 1 + P₁₂`. Consequently the
exchange operator acts on the channel of total spin `S` by `(-1)^(S + 1)`: this is the spin
factor in the charge-conjugation eigenvalue of a quark-antiquark pair.

The abstract counterpart of this decomposition is the Clebsch-Gordan rule
`V(1) ⊗ V(1) ≅ V(2) ⊕ V(0)` for `sl₂` (`TauCeti.Sl2Std.isInternal_cgSummand`); this file gives
the two channels as explicit projectors in the Pauli convention, together with the exchange
symmetry that distinguishes them.

## Main definitions

* `spinSingletProj`, `spinTripletProj`: the projectors onto the two spin channels of the pair.

## Main results

* `trace_spinSingletProj`, `trace_spinTripletProj`: the traces `1` and `3`.
* `casimir_spinGen_eq`, `casimir_spinGen_mul_spinSingletProj`,
  `casimir_spinGen_mul_spinTripletProj`: the total spin squared is `0` on the singlet channel and
  `2` on the triplet channel.

## Implementation notes

The spin space is `EuclideanSpace ℂ (Fin 2)`, on which the Pauli matrices act through
`Matrix.toEuclideanLin`, rather than `Fin 2 → ℂ`: over `Fin 2 → ℂ` the `Pi.addCommMonoid` and
`Pi.addCommGroup` instances on the tensor square do not agree syntactically, which keeps
`Module.End ℂ ((Fin 2 → ℂ) ⊗[ℂ] (Fin 2 → ℂ))` from being recognised as a ring and blocks every
ring lemma on the projectors.

The total spin squared is written `LieModule.casimir ℂ _ _ spinGen spinGen`, that is
`Σᵢ Sᵢ Sᵢ` for the action on the pair of the three su(2) generators `spinGen`, taken through the
general `LieModule.casimir` construction with `L` the whole of `Module.End ℂ ℂ²`. The three
`spinGen` do not span this four-dimensional `L`, so the centrality results of
`EpsilonEridani.Mathematics.LieAlgebra.Casimir`, which need a basis of `L` and its dual, do not
apply to it; the statements here are proved directly.

The Lie bracket on `Module.End ℂ ℂ²` used by the results on the total spin is the commutator
bracket of `LieRing.ofAssociativeRing`, which Mathlib does not make a global instance; a file
that states or rewrites with these results must enable it as this one does, with
`attribute [local instance 100] LieRing.ofAssociativeRing`.

## References

* G. T. Bodwin, E. Braaten and G. P. Lepage, *Rigorous QCD analysis of inclusive annihilation and
  production of heavy quarkonium*, Phys. Rev. D 51 (1995) 1125, Section II.
* N. Brambilla et al., *Heavy quarkonium physics*, CERN-2005-005, hep-ph/0412158.
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Quarkonium

open Matrix TensorProduct PauliMatrix

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
  rw [spinSingletProj, antisymmProj, map_smul, map_sub, trace_comm, LinearMap.trace_one,
    Module.finrank_tensorProduct, finrank_euclideanSpace_fin, invOf_eq_inv]
  norm_num

/-- The triplet channel is three-dimensional: its projector has trace `3`. -/
@[simp]
theorem trace_spinTripletProj :
    LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) spinTripletProj = 3 := by
  rw [spinTripletProj, symmProj_eq_one_sub, map_sub, ← spinSingletProj, trace_spinSingletProj,
    LinearMap.trace_one, Module.finrank_tensorProduct, finrank_euclideanSpace_fin]
  norm_num

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The total spin squared -/

/-- The total spin squared `S² = Σᵢ Sᵢ Sᵢ` of the pair is twice the triplet projector:
`S² = 1 + P₁₂ = 2 P₁`. -/
theorem casimir_spinGen_eq :
    LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen =
      (2 : ℂ) • spinTripletProj := by
  refine TensorProduct.ext' fun a b ↦ ?_
  have h := congr($sum_tensorProductMap_toEuclideanLin_pauliMatrix_inr (a ⊗ₜ b))
  simp only [LinearMap.sum_apply, map_tmul, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearEquiv.coe_coe, comm_tmul, Module.End.one_apply] at h
  have hs : ∑ i, spinGen i a ⊗ₜ[ℂ] spinGen i b = (4 : ℂ)⁻¹ • ((2 : ℂ) • b ⊗ₜ a - a ⊗ₜ b) := by
    simp only [spinGen, LinearMap.smul_apply, smul_tmul_smul, ← Finset.smul_sum, h]
    norm_num
  have ha := congr($sum_spinGen_mul_self a)
  have hb := congr($sum_spinGen_mul_self b)
  simp only [LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Module.End.one_apply] at ha hb
  simp only [LieModule.casimir_apply, lie_add, LieModule.lie_tmul_right, Module.End.lie_apply,
    Finset.sum_add_distrib, ← sum_tmul, ← tmul_sum, ha, hb, hs, ← smul_tmul', tmul_smul,
    LinearMap.smul_apply, symmProj_apply, comm_tmul, invOf_eq_inv]
  module

/-- The total spin squared vanishes on the singlet channel: `S (S + 1) = 0` for `S = 0`. -/
@[simp]
theorem casimir_spinGen_mul_spinSingletProj :
    LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen * spinSingletProj = 0 := by
  rw [casimir_spinGen_eq, smul_mul_assoc, symmProj_mul_antisymmProj, smul_zero]

/-- The total spin squared takes the value `2` on the triplet channel: `S (S + 1) = 2` for
`S = 1`. -/
@[simp]
theorem casimir_spinGen_mul_spinTripletProj :
    LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen * spinTripletProj =
      (2 : ℂ) • spinTripletProj := by
  rw [casimir_spinGen_eq, smul_mul_assoc, symmProj_mul_self]

/-- The total spin squared vanishes on the singlet channel, multiplying from the right. -/
@[simp]
theorem spinSingletProj_mul_casimir_spinGen :
    spinSingletProj * LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen = 0 := by
  rw [casimir_spinGen_eq, mul_smul_comm, antisymmProj_mul_symmProj, smul_zero]

/-- The total spin squared takes the value `2` on the triplet channel, multiplying from the
right. -/
@[simp]
theorem spinTripletProj_mul_casimir_spinGen :
    spinTripletProj * LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen =
      (2 : ℂ) • spinTripletProj := by
  rw [casimir_spinGen_eq, mul_smul_comm, symmProj_mul_self]

end EpsilonEridani.QFT.Quarkonium
