/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LieAlgebra.Casimir
public import EpsilonEridani.Relativity.PauliMatrices.RelationsExtensions
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Idempotents
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The spin singlet and triplet channels of a heavy quark-antiquark pair

The heavy quark and the heavy antiquark each carry spin `1/2`, with spin space `ℂ²` on which the
spin operators are `Sᵢ = σᵢ / 2` (`spinGen`). The spin space of the pair is `ℂ² ⊗ ℂ²`, on which
an operator `X` on `ℂ²` acts through the tensor-product Lie module, `X ↦ X ⊗ 1 + 1 ⊗ X`; for
`X = Sᵢ` this is the total spin `Sᵢ = S₁ᵢ + S₂ᵢ` of the pair.

This module decomposes `2 ⊗ 2 = 1 ⊕ 3` into the spin-singlet and spin-triplet channels, by
symmetry under the operator `P₁₂ = TensorProduct.comm` exchanging the two spins:

* the singlet projector `(1 - P₁₂) / 2` projects onto the states antisymmetric under exchange,
  and the triplet projector `(1 + P₁₂) / 2` onto the symmetric ones;
* the two are complete orthogonal idempotents, both commute with the action of every operator on
  `ℂ²` (in particular with the total spin), and their traces are `1` and `3`;
* the total-spin Casimir `S² = Σᵢ Sᵢ Sᵢ` of the pair is `1 + P₁₂`, that is twice the triplet
  projector, so it takes the value `S (S + 1) = 0` on the singlet channel and `2` on the triplet
  channel.

The Casimir computation rests on the exchange identity `Σᵢ σᵢ ⊗ σᵢ = 2 P₁₂ - 1` of the Pauli
matrices (`PauliMatrix.sum_map_toEuclideanLin_pauliMatrix_inr`), which with `Σᵢ Sᵢ Sᵢ = 3/4` on `ℂ²`
gives `S² = 3/2 + (σ(1) · σ(2)) / 2 = 1 + P₁₂`. Consequently the exchange operator acts on the
channel of total spin `S` by `(-1)^(S + 1)`: this is the spin factor in the charge-conjugation
eigenvalue of a quark-antiquark pair.

The abstract counterpart of this decomposition is the Clebsch-Gordan rule
`V(1) ⊗ V(1) ≅ V(2) ⊕ V(0)` for `sl₂` (`TauCeti.Sl2Std.isInternal_cgSummand`); this file gives
the two channels as explicit projectors in the Pauli convention, together with the exchange
symmetry that distinguishes them.

## Main definitions

* `spinGen i`: the spin operator `Sᵢ = σᵢ / 2` of a spin-`1/2` particle.
* `spinSingletProj`, `spinTripletProj`: the projectors onto the two spin channels of the pair.

The total-spin Casimir of the pair is `LieModule.casimir ℂ _ _ spinGen spinGen`.

## Main results

* `spinSingletProj_add_spinTripletProj`,
  `completeOrthogonalIdempotents_spinSingletProj_spinTripletProj`: the two projectors are
  complete orthogonal idempotents.
* `spinSingletProj_apply_eq_self_iff`, `spinTripletProj_apply_eq_self_iff`: the singlet channel
  consists of the states antisymmetric under exchange, and the triplet channel of the symmetric
  ones.
* `comm_mul_spinSingletProj`, `comm_mul_spinTripletProj`: the exchange operator acts by `-1` on
  the singlet channel and by `1` on the triplet channel.
* `trace_spinSingletProj`, `trace_spinTripletProj`: the traces `1` and `3`.
* `commute_toEnd_spinSingletProj`, `commute_toEnd_spinTripletProj`: both channels are invariant
  under the action of the pair.
* `casimir_spinGen_eq`, `casimir_spinGen_mul_spinSingletProj`,
  `casimir_spinGen_mul_spinTripletProj`: the total-spin Casimir is `0` on the singlet channel and
  `2` on the triplet channel.

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

/-! ### The spin of one heavy quark -/

/-- The spin operator `Sᵢ = σᵢ / 2` of a spin-`1/2` particle, acting on its spin space `ℂ²`. -/
def spinGen (i : Fin 3) : Module.End ℂ ℂ² :=
  (2 : ℂ)⁻¹ • toEuclideanLin (pauliMatrix (Sum.inr i))

@[simp]
theorem spinGen_apply (i : Fin 3) (v : ℂ²) :
    spinGen i v = (2 : ℂ)⁻¹ • toEuclideanLin (pauliMatrix (Sum.inr i)) v := by
  simp [spinGen]

/-- The spin Casimir of a single spin-`1/2` particle: `Σᵢ Sᵢ Sᵢ = s (s + 1) = 3/4`. -/
theorem sum_spinGen_mul_self : ∑ i : Fin 3, spinGen i * spinGen i = (3 / 4 : ℂ) • 1 := by
  have h (i : Fin 3) :
      toEuclideanLin (pauliMatrix (Sum.inr i)) * toEuclideanLin (pauliMatrix (Sum.inr i)) = 1 := by
    ext v k
    simp [mulVec_mulVec, pauliMatrix_mul_self]
  simp only [spinGen, smul_mul_smul_comm, h, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

/-! ### The two projectors -/

/-- The projector `(1 - P₁₂) / 2` onto the spin-singlet channel of a pair of spin-`1/2`
particles, where `P₁₂` exchanges the two spins. -/
def spinSingletProj : Module.End ℂ (ℂ² ⊗[ℂ] ℂ²) :=
  (2 : ℂ)⁻¹ • (1 - (TensorProduct.comm ℂ ℂ² ℂ²).toLinearMap)

/-- The projector `(1 + P₁₂) / 2` onto the spin-triplet channel of a pair of spin-`1/2`
particles, where `P₁₂` exchanges the two spins. -/
def spinTripletProj : Module.End ℂ (ℂ² ⊗[ℂ] ℂ²) :=
  (2 : ℂ)⁻¹ • (1 + (TensorProduct.comm ℂ ℂ² ℂ²).toLinearMap)

/-- The singlet projector is the antisymmetric part: `P₀ x = (x - P₁₂ x) / 2`. -/
@[simp]
theorem spinSingletProj_apply (x : ℂ² ⊗[ℂ] ℂ²) :
    spinSingletProj x = (2 : ℂ)⁻¹ • (x - TensorProduct.comm ℂ ℂ² ℂ² x) := by
  simp [spinSingletProj]

/-- The triplet projector is the symmetric part: `P₁ x = (x + P₁₂ x) / 2`. -/
@[simp]
theorem spinTripletProj_apply (x : ℂ² ⊗[ℂ] ℂ²) :
    spinTripletProj x = (2 : ℂ)⁻¹ • (x + TensorProduct.comm ℂ ℂ² ℂ² x) := by
  simp [spinTripletProj]

/-- The triplet projector is the complement of the singlet projector. -/
theorem spinTripletProj_eq : spinTripletProj = 1 - spinSingletProj := by
  rw [spinTripletProj, spinSingletProj]
  module

/-- The two spin channels exhaust the pair's spin space. -/
@[simp]
theorem spinSingletProj_add_spinTripletProj : spinSingletProj + spinTripletProj = 1 := by
  rw [spinTripletProj_eq, add_sub_cancel]

/-- The two spin channels exhaust the pair's spin space, in the reversed addition order. -/
@[simp]
theorem spinTripletProj_add_spinSingletProj : spinTripletProj + spinSingletProj = 1 := by
  rw [add_comm, spinSingletProj_add_spinTripletProj]

/-- The singlet projector is idempotent. -/
theorem isIdempotentElem_spinSingletProj : IsIdempotentElem spinSingletProj := by
  refine TensorProduct.ext' fun a b ↦ ?_
  simp only [Module.End.mul_apply, spinSingletProj_apply, comm_tmul, map_smul, map_sub]
  module

/-- The triplet projector is idempotent. -/
theorem isIdempotentElem_spinTripletProj : IsIdempotentElem spinTripletProj := by
  rw [spinTripletProj_eq]
  exact isIdempotentElem_spinSingletProj.one_sub

/-- The singlet projector squares to itself: `P₀ P₀ = P₀`. -/
@[simp]
theorem spinSingletProj_mul_self : spinSingletProj * spinSingletProj = spinSingletProj :=
  isIdempotentElem_spinSingletProj.eq

/-- The triplet projector squares to itself: `P₁ P₁ = P₁`. -/
@[simp]
theorem spinTripletProj_mul_self : spinTripletProj * spinTripletProj = spinTripletProj :=
  isIdempotentElem_spinTripletProj.eq

/-- The singlet and triplet channels are orthogonal. -/
@[simp]
theorem spinSingletProj_mul_spinTripletProj : spinSingletProj * spinTripletProj = 0 := by
  rw [spinTripletProj_eq, isIdempotentElem_spinSingletProj.mul_one_sub_self]

/-- The triplet and singlet channels are orthogonal. -/
@[simp]
theorem spinTripletProj_mul_spinSingletProj : spinTripletProj * spinSingletProj = 0 := by
  rw [spinTripletProj_eq, isIdempotentElem_spinSingletProj.one_sub_mul_self]

/-- The singlet and triplet projectors are complete orthogonal idempotents: the spin space of a
pair of spin-`1/2` particles is the direct sum of the two channels. -/
theorem completeOrthogonalIdempotents_spinSingletProj_spinTripletProj :
    CompleteOrthogonalIdempotents ![spinSingletProj, spinTripletProj] := by
  rw [spinTripletProj_eq]
  exact .of_isIdempotentElem isIdempotentElem_spinSingletProj

/-! ### Exchange symmetry -/

/-- The exchange operator acts by `-1` on the singlet channel: `P₁₂ P₀ = -P₀`. -/
@[simp]
theorem comm_mul_spinSingletProj :
    (TensorProduct.comm ℂ ℂ² ℂ²).toLinearMap * spinSingletProj =
      -spinSingletProj := by
  refine TensorProduct.ext' fun a b ↦ ?_
  simp only [Module.End.mul_apply, spinSingletProj_apply, comm_tmul, map_smul, map_sub,
    LinearEquiv.coe_coe, LinearMap.neg_apply]
  module

/-- The exchange operator acts by `1` on the triplet channel: `P₁₂ P₁ = P₁`. -/
@[simp]
theorem comm_mul_spinTripletProj :
    (TensorProduct.comm ℂ ℂ² ℂ²).toLinearMap * spinTripletProj =
      spinTripletProj := by
  refine TensorProduct.ext' fun a b ↦ ?_
  simp only [Module.End.mul_apply, spinTripletProj_apply, comm_tmul, map_smul, map_add,
    LinearEquiv.coe_coe]
  module

/-- A state lies in the singlet channel exactly when it is antisymmetric under exchange of the
two spins. -/
theorem spinSingletProj_apply_eq_self_iff (x : ℂ² ⊗[ℂ] ℂ²) :
    spinSingletProj x = x ↔ TensorProduct.comm ℂ ℂ² ℂ² x = -x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($comm_mul_spinSingletProj x)
    rwa [Module.End.mul_apply, LinearMap.neg_apply, h, LinearEquiv.coe_coe] at this
  · rw [spinSingletProj_apply, h]
    module

/-- A state lies in the triplet channel exactly when it is symmetric under exchange of the two
spins. -/
theorem spinTripletProj_apply_eq_self_iff (x : ℂ² ⊗[ℂ] ℂ²) :
    spinTripletProj x = x ↔ TensorProduct.comm ℂ ℂ² ℂ² x = x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($comm_mul_spinTripletProj x)
    rwa [Module.End.mul_apply, h, LinearEquiv.coe_coe] at this
  · rw [spinTripletProj_apply, h]
    module

/-! ### Traces -/

/-- The singlet channel is one-dimensional: its projector has trace `1`. -/
@[simp]
theorem trace_spinSingletProj :
    LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) spinSingletProj = 1 := by
  -- The exchange operator permutes the product basis `eₐ ⊗ e_b`, fixing the two diagonal
  -- vectors, so its trace is `2`.
  have hcomm : LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) (TensorProduct.comm ℂ ℂ² ℂ²).toLinearMap = 2 := by
    let b := (EuclideanSpace.basisFun (Fin 2) ℂ).toBasis
    rw [LinearMap.trace_eq_matrix_trace ℂ (b.tensorProduct b)]
    simp [b, Matrix.trace, Fintype.sum_prod_type, LinearMap.toMatrix_apply]
  rw [spinSingletProj, map_smul, map_sub, hcomm, LinearMap.trace_one,
    Module.finrank_tensorProduct, finrank_euclideanSpace_fin]
  norm_num

/-- The triplet channel is three-dimensional: its projector has trace `3`. -/
@[simp]
theorem trace_spinTripletProj :
    LinearMap.trace ℂ (ℂ² ⊗[ℂ] ℂ²) spinTripletProj = 3 := by
  rw [spinTripletProj_eq, map_sub, trace_spinSingletProj, LinearMap.trace_one,
    Module.finrank_tensorProduct, finrank_euclideanSpace_fin]
  norm_num

/-! ### The action on the pair

An operator `X` on `ℂ²` acts on the pair through the tensor-product Lie module,
`⁅X, a ⊗ b⁆ = X a ⊗ b + a ⊗ X b`. Both channels are invariant under every such action, since it
commutes with exchanging the two factors.

The Lie bracket on `Module.End ℂ ℂ²` used here, and by the Casimir results below, is the
commutator bracket of `LieRing.ofAssociativeRing`, which Mathlib does not make a global instance;
a file that states or rewrites with these results must enable it as this one does, with
`attribute [local instance 100] LieRing.ofAssociativeRing`. -/

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The singlet channel is invariant under the action of the pair. -/
theorem commute_toEnd_spinSingletProj (X : Module.End ℂ ℂ²) :
    Commute (LieModule.toEnd ℂ _ (ℂ² ⊗[ℂ] ℂ²) X) spinSingletProj := by
  refine TensorProduct.ext' fun a b ↦ ?_
  simp only [Module.End.mul_apply, LieModule.toEnd_apply_apply, spinSingletProj_apply, comm_tmul,
    lie_sub, LieModule.lie_tmul_right, Module.End.lie_apply, map_add, map_smul]
  module

/-- The triplet channel is invariant under the action of the pair. -/
theorem commute_toEnd_spinTripletProj (X : Module.End ℂ ℂ²) :
    Commute (LieModule.toEnd ℂ _ (ℂ² ⊗[ℂ] ℂ²) X) spinTripletProj := by
  rw [spinTripletProj_eq]
  exact (Commute.one_right _).sub_right (commute_toEnd_spinSingletProj X)

/-! ### The total-spin Casimir -/

/-- The total-spin Casimir of the pair is twice the triplet projector: `S² = 1 + P₁₂ = 2 P₁`.
It follows from `S² = 3/2 + (σ(1) · σ(2)) / 2` and the exchange identity
`σ(1) · σ(2) = 2 P₁₂ - 1`. -/
theorem casimir_spinGen_eq :
    LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen =
      (2 : ℂ) • spinTripletProj := by
  refine TensorProduct.ext' fun a b ↦ ?_
  have h := congr($sum_map_toEuclideanLin_pauliMatrix_inr (a ⊗ₜ b))
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
    LinearMap.smul_apply, spinTripletProj_apply, comm_tmul]
  module

/-- The total-spin Casimir vanishes on the singlet channel: `S (S + 1) = 0` for `S = 0`. -/
@[simp]
theorem casimir_spinGen_mul_spinSingletProj :
    LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen * spinSingletProj = 0 := by
  rw [casimir_spinGen_eq, smul_mul_assoc, spinTripletProj_mul_spinSingletProj, smul_zero]

/-- The total-spin Casimir takes the value `2` on the triplet channel: `S (S + 1) = 2` for
`S = 1`. -/
@[simp]
theorem casimir_spinGen_mul_spinTripletProj :
    LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen * spinTripletProj =
      (2 : ℂ) • spinTripletProj := by
  rw [casimir_spinGen_eq, smul_mul_assoc, spinTripletProj_mul_self]

/-- The total-spin Casimir vanishes on the singlet channel, multiplying from the right. -/
@[simp]
theorem spinSingletProj_mul_casimir_spinGen :
    spinSingletProj * LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen = 0 := by
  rw [casimir_spinGen_eq, mul_smul_comm, spinSingletProj_mul_spinTripletProj, smul_zero]

/-- The total-spin Casimir takes the value `2` on the triplet channel, multiplying from the
right. -/
@[simp]
theorem spinTripletProj_mul_casimir_spinGen :
    spinTripletProj * LieModule.casimir ℂ _ (ℂ² ⊗[ℂ] ℂ²) spinGen spinGen =
      (2 : ℂ) • spinTripletProj := by
  rw [casimir_spinGen_eq, mul_smul_comm, spinTripletProj_mul_self]

end EpsilonEridani.QFT.Quarkonium
