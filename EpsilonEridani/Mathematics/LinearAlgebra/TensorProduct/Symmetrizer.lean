/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Lie.TensorProduct
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Idempotents
public import TauCeti.LinearAlgebra.TensorProduct.Symmetric
public import TauCeti.RingTheory.Idempotents.SquareRootOne
public import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Projection

/-!
# The symmetrizer and antisymmetrizer on a tensor square

On the tensor square `M ⊗[R] M` the operator `P = TensorProduct.comm R M M` exchanging the two
factors is an involution, `P * P = 1` (`TensorProduct.comm_mul_comm`). When `2` is invertible in
`R` it is therefore a square root of one in the algebra `Module.End R (M ⊗[R] M)`, and cuts out the
complementary orthogonal pair of idempotents `TauCeti.halfOneAdd R (± P)`:

* `TensorProduct.symmProj R M = ⅟2 • (1 + P)`, the projector onto the symmetric tensors
  `TauCeti.symmetricTensors R M`, fixed by `P`;
* `TensorProduct.antisymmProj R M = ⅟2 • (1 - P)`, the projector onto the antisymmetric tensors
  `TauCeti.antisymmetricTensors R M`, negated by `P`.

This file specialises the general results on `TauCeti.halfOneAdd` to `P`, discharging the
hypothesis `P * P = 1`, and connects the two projectors to the eigenspaces of `P`: their ranges are
`TauCeti.symmetricTensors R M` and `TauCeti.antisymmetricTensors R M`, whose complementarity is
`TauCeti.isCompl_symmetricTensors_antisymmetricTensors`. The exchange operator commutes with the
action `x ↦ x ⊗ 1 + 1 ⊗ x` of every element `x` of a Lie algebra acting on `M`, so both parts are
invariant under it. For `M` finite free of rank `n`, the trace of the exchange operator is `n`, so
the symmetric and antisymmetric parts have ranks `n (n + 1) / 2` and `n (n - 1) / 2`.

## Main definitions

* `TensorProduct.symmProj`, `TensorProduct.antisymmProj`: the projectors onto the symmetric and
  antisymmetric parts of `M ⊗[R] M`.

## Main results

* `TensorProduct.comm_mul_comm`: the exchange operator is an involution.
* `TensorProduct.trace_comm`: its trace is `Module.finrank R M`.
* `TensorProduct.completeOrthogonalIdempotents_antisymmProj_symmProj`: the two projectors are
  complete orthogonal idempotents.
* `TensorProduct.comm_eq_symmProj_sub_antisymmProj`: the spectral decomposition of the exchange
  operator.
* `TensorProduct.range_symmProj`, `TensorProduct.range_antisymmProj`: the projectors project onto
  the symmetric and antisymmetric tensors.
* `TensorProduct.trace_symmProj`, `TensorProduct.trace_antisymmProj`: the traces of the projectors.
* `TensorProduct.commute_toEnd_comm`: the exchange commutes with the action of a Lie algebra.
-/

@[expose] public section

noncomputable section

namespace TensorProduct

open TauCeti

/-! ### The exchange operator -/

section Semiring

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The exchange operator on a tensor square is an involution: `P * P = 1`. -/
@[simp]
theorem comm_mul_comm :
    (TensorProduct.comm R M M).toLinearMap * (TensorProduct.comm R M M).toLinearMap = 1 :=
  comm_comp_comm R M M

end Semiring

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The trace of the exchange operator on the tensor square of a finite free module is its rank:
it is the case `f = id` of `LinearMap.trace_map_self_comp_comm`. -/
@[simp]
theorem trace_comm [Module.Free R M] [Module.Finite R M] :
    LinearMap.trace R (M ⊗[R] M) (TensorProduct.comm R M M).toLinearMap = Module.finrank R M := by
  have h := LinearMap.trace_map_self_comp_comm (LinearMap.id : M →ₗ[R] M)
  rwa [TensorProduct.map_id, LinearMap.id_comp, LinearMap.id_comp, LinearMap.trace_id] at h

/-! ### The action of a Lie algebra

An element `x` of a Lie algebra `L` acting on `M` acts on `M ⊗[R] M` through the tensor-product
Lie module, `⁅x, a ⊗ b⁆ = ⁅x, a⁆ ⊗ b + a ⊗ ⁅x, b⁆`. This action commutes with the exchange of
the two factors. -/

section Lie

variable {R M} {L : Type*} [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]

/-- For every element `x` of a Lie algebra acting on `M`, the action `x ⊗ 1 + 1 ⊗ x` of `x` on
`M ⊗[R] M` commutes with the exchange of the two factors. -/
theorem commute_toEnd_comm (x : L) :
    Commute (LieModule.toEnd R L (M ⊗[R] M) x) (TensorProduct.comm R M M).toLinearMap := by
  refine TensorProduct.ext' fun a b ↦ ?_
  simp [LieModule.lie_tmul_right, add_comm]

end Lie

/-! ### The two projectors -/

section Projectors

variable [Invertible (2 : R)]

/-- The projector `⅟2 • (1 + P)` onto the symmetric part of `M ⊗[R] M`, where `P` exchanges the
two factors: the idempotent `TauCeti.halfOneAdd` cut out by the square root of one `P`. -/
def symmProj : Module.End R (M ⊗[R] M) :=
  halfOneAdd R (TensorProduct.comm R M M).toLinearMap

/-- The projector `⅟2 • (1 - P)` onto the antisymmetric part of `M ⊗[R] M`, where `P` exchanges
the two factors: the idempotent `TauCeti.halfOneAdd` cut out by the square root of one `-P`. -/
def antisymmProj : Module.End R (M ⊗[R] M) :=
  halfOneAdd R (-(TensorProduct.comm R M M).toLinearMap)

/-- The defining formula `S = ⅟2 • (1 + P)` of the symmetrizer. -/
theorem symmProj_def :
    symmProj R M = ⅟(2 : R) • (1 + (TensorProduct.comm R M M).toLinearMap) :=
  halfOneAdd_def R _

/-- The defining formula `A = ⅟2 • (1 - P)` of the antisymmetrizer. -/
theorem antisymmProj_def :
    antisymmProj R M = ⅟(2 : R) • (1 - (TensorProduct.comm R M M).toLinearMap) := by
  rw [antisymmProj, halfOneAdd_def, sub_eq_add_neg]

variable {R M}

/-- The symmetrizer is the symmetric part: `S x = ⅟2 • (x + P x)`. -/
@[simp]
theorem symmProj_apply (x : M ⊗[R] M) :
    symmProj R M x = ⅟(2 : R) • (x + TensorProduct.comm R M M x) := by
  simp [symmProj_def]

/-- The antisymmetrizer is the antisymmetric part: `A x = ⅟2 • (x - P x)`. -/
@[simp]
theorem antisymmProj_apply (x : M ⊗[R] M) :
    antisymmProj R M x = ⅟(2 : R) • (x - TensorProduct.comm R M M x) := by
  simp [antisymmProj_def]

variable (R M)

/-- The symmetric and antisymmetric parts exhaust the tensor square. -/
@[simp]
theorem symmProj_add_antisymmProj : symmProj R M + antisymmProj R M = 1 :=
  halfOneAdd_add_halfOneAdd_neg R _

/-- The symmetric and antisymmetric parts exhaust the tensor square, in the reversed addition
order. -/
@[simp]
theorem antisymmProj_add_symmProj : antisymmProj R M + symmProj R M = 1 := by
  rw [add_comm, symmProj_add_antisymmProj]

/-- The antisymmetrizer is the complement of the symmetrizer. -/
theorem antisymmProj_eq_one_sub : antisymmProj R M = 1 - symmProj R M :=
  halfOneAdd_neg_eq_one_sub R _

/-- The symmetrizer is the complement of the antisymmetrizer. -/
theorem symmProj_eq_one_sub : symmProj R M = 1 - antisymmProj R M :=
  eq_sub_of_add_eq (symmProj_add_antisymmProj R M)

/-- The spectral decomposition of the exchange operator: `P = S - A`. -/
theorem comm_eq_symmProj_sub_antisymmProj :
    (TensorProduct.comm R M M).toLinearMap = symmProj R M - antisymmProj R M :=
  (halfOneAdd_sub_halfOneAdd_neg R _).symm

/-- The symmetrizer is idempotent. -/
theorem isIdempotentElem_symmProj : IsIdempotentElem (symmProj R M) :=
  isIdempotentElem_halfOneAdd R (comm_mul_comm R M)

/-- The antisymmetrizer is idempotent. -/
theorem isIdempotentElem_antisymmProj : IsIdempotentElem (antisymmProj R M) :=
  isIdempotentElem_halfOneAdd_neg R (comm_mul_comm R M)

/-- The antisymmetrizer squares to itself. -/
@[simp]
theorem antisymmProj_mul_self : antisymmProj R M * antisymmProj R M = antisymmProj R M :=
  (isIdempotentElem_antisymmProj R M).eq

/-- The symmetrizer squares to itself. -/
@[simp]
theorem symmProj_mul_self : symmProj R M * symmProj R M = symmProj R M :=
  (isIdempotentElem_symmProj R M).eq

/-- The antisymmetric and symmetric parts are orthogonal. -/
@[simp]
theorem antisymmProj_mul_symmProj : antisymmProj R M * symmProj R M = 0 :=
  halfOneAdd_neg_mul_halfOneAdd R (comm_mul_comm R M)

/-- The symmetric and antisymmetric parts are orthogonal. -/
@[simp]
theorem symmProj_mul_antisymmProj : symmProj R M * antisymmProj R M = 0 :=
  halfOneAdd_mul_halfOneAdd_neg R (comm_mul_comm R M)

/-- The antisymmetrizer and the symmetrizer are complete orthogonal idempotents: the tensor
square is the direct sum of its antisymmetric and symmetric parts. In submodule form this is
`TauCeti.isCompl_symmetricTensors_antisymmetricTensors`, through `TensorProduct.range_symmProj`
and `TensorProduct.range_antisymmProj`. -/
theorem completeOrthogonalIdempotents_antisymmProj_symmProj :
    CompleteOrthogonalIdempotents ![antisymmProj R M, symmProj R M] := by
  rw [symmProj_eq_one_sub]
  exact .of_isIdempotentElem (isIdempotentElem_antisymmProj R M)

/-- The exchange operator acts by `-1` on the antisymmetric part: `P * A = -A`. -/
@[simp]
theorem comm_mul_antisymmProj :
    (TensorProduct.comm R M M).toLinearMap * antisymmProj R M = -antisymmProj R M := by
  rw [antisymmProj_def, mul_smul_comm, mul_sub, mul_one, comm_mul_comm]
  match_scalars <;> simp

/-- The exchange operator acts by `-1` on the antisymmetric part: `A * P = -A`. -/
@[simp]
theorem antisymmProj_mul_comm :
    antisymmProj R M * (TensorProduct.comm R M M).toLinearMap = -antisymmProj R M := by
  rw [antisymmProj_def, smul_mul_assoc, sub_mul, one_mul, comm_mul_comm]
  match_scalars <;> simp

/-- The exchange operator acts by `1` on the symmetric part: `P * S = S`. -/
@[simp]
theorem comm_mul_symmProj :
    (TensorProduct.comm R M M).toLinearMap * symmProj R M = symmProj R M := by
  rw [symmProj_def, mul_smul_comm, mul_add, mul_one, comm_mul_comm, add_comm]

/-- The exchange operator acts by `1` on the symmetric part: `S * P = S`. -/
@[simp]
theorem symmProj_mul_comm :
    symmProj R M * (TensorProduct.comm R M M).toLinearMap = symmProj R M := by
  rw [symmProj_def, smul_mul_assoc, add_mul, one_mul, comm_mul_comm, add_comm]

/-! ### The ranges of the projectors -/

variable {R M}

/-- The antisymmetrizer fixes exactly the antisymmetric tensors. -/
theorem antisymmProj_apply_eq_self_iff (x : M ⊗[R] M) :
    antisymmProj R M x = x ↔ x ∈ antisymmetricTensors R M := by
  rw [mem_antisymmetricTensors]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($(comm_mul_antisymmProj R M) x)
    rwa [Module.End.mul_apply, LinearMap.neg_apply, h, LinearEquiv.coe_coe] at this
  · rw [antisymmProj_apply, h, sub_neg_eq_add, ← two_smul R x, invOf_smul_smul]

/-- The symmetrizer fixes exactly the symmetric tensors. -/
theorem symmProj_apply_eq_self_iff (x : M ⊗[R] M) :
    symmProj R M x = x ↔ x ∈ symmetricTensors R M := by
  rw [mem_symmetricTensors]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($(comm_mul_symmProj R M) x)
    rwa [Module.End.mul_apply, h, LinearEquiv.coe_coe] at this
  · rw [symmProj_apply, h, ← two_smul R x, invOf_smul_smul]

variable (R M)

/-- The antisymmetrizer projects onto the antisymmetric tensors. -/
theorem range_antisymmProj : LinearMap.range (antisymmProj R M) = antisymmetricTensors R M := by
  ext x
  rw [LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_antisymmProj R M),
    antisymmProj_apply_eq_self_iff]

/-- The symmetrizer projects onto the symmetric tensors. -/
theorem range_symmProj : LinearMap.range (symmProj R M) = symmetricTensors R M := by
  ext x
  rw [LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_symmProj R M),
    symmProj_apply_eq_self_iff]

/-! ### Traces -/

/-- The trace of the symmetrizer on the tensor square of a finite free module of rank `n` is
`n (n + 1) / 2`, the rank of the symmetric part. -/
theorem trace_symmProj [Module.Free R M] [Module.Finite R M] :
    LinearMap.trace R (M ⊗[R] M) (symmProj R M) =
      ⅟(2 : R) * (Module.finrank R M * (Module.finrank R M + 1)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  rw [symmProj_def, map_smul, map_add, LinearMap.trace_one, trace_comm,
    Module.finrank_tensorProduct, smul_eq_mul]
  push_cast
  ring

/-- The trace of the antisymmetrizer on the tensor square of a finite free module of rank `n` is
`n (n - 1) / 2`, the rank of the antisymmetric part. -/
theorem trace_antisymmProj [Module.Free R M] [Module.Finite R M] :
    LinearMap.trace R (M ⊗[R] M) (antisymmProj R M) =
      ⅟(2 : R) * (Module.finrank R M * (Module.finrank R M - 1)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  rw [antisymmProj_def, map_smul, map_sub, LinearMap.trace_one, trace_comm,
    Module.finrank_tensorProduct, smul_eq_mul]
  push_cast
  ring

/-! ### Invariance under a Lie algebra -/

section Lie

variable {R M} {L : Type*} [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]

/-- For every element `x` of a Lie algebra acting on `M`, the action `x ⊗ 1 + 1 ⊗ x` of `x` on
`M ⊗[R] M` commutes with the antisymmetrizer, so the antisymmetric part is an invariant
subspace. -/
theorem commute_toEnd_antisymmProj (x : L) :
    Commute (LieModule.toEnd R L (M ⊗[R] M) x) (antisymmProj R M) :=
  (commute_halfOneAdd R (commute_toEnd_comm x).symm.neg_left).symm

/-- For every element `x` of a Lie algebra acting on `M`, the action `x ⊗ 1 + 1 ⊗ x` of `x` on
`M ⊗[R] M` commutes with the symmetrizer, so the symmetric part is an invariant subspace. -/
theorem commute_toEnd_symmProj (x : L) :
    Commute (LieModule.toEnd R L (M ⊗[R] M) x) (symmProj R M) :=
  (commute_halfOneAdd R (commute_toEnd_comm x).symm).symm

end Lie

end Projectors

end TensorProduct
