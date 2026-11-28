/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Basic
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

* `TensorProduct.symmetrizer R M = ⅟2 • (1 + P)`, the projector onto the symmetric tensors
  `TauCeti.symmetricTensors R M`, fixed by `P`;
* `TensorProduct.antisymmetrizer R M = ⅟2 • (1 - P)`, the projector onto the antisymmetric tensors
  `TauCeti.antisymmetricTensors R M`, negated by `P`.

This file specialises the general results on `TauCeti.halfOneAdd` to `P`, discharging the
hypothesis `P * P = 1`, and connects the two projectors to the eigenspaces of `P`: their ranges are
`TauCeti.symmetricTensors R M` and `TauCeti.antisymmetricTensors R M`, whose complementarity is
`TauCeti.isCompl_symmetricTensors_antisymmetricTensors`. The exchange operator commutes with the
diagonal action `f ⊗ 1 + 1 ⊗ f` of every endomorphism `f` of `M`, so both parts are invariant
under it; this is the form in which an element of a Lie algebra acting on `M` acts on the tensor
square. For `M` finite free of rank `n`, the trace of the exchange operator is `n`, and the traces
of the symmetrizer and the antisymmetrizer are `n (n + 1) / 2` and `n (n - 1) / 2` as elements of
`R`. Over a field of characteristic zero these traces are the dimensions of the symmetric and
antisymmetric parts; that rank statement is not formalised here.

## Main definitions

* `TensorProduct.symmetrizer`, `TensorProduct.antisymmetrizer`: the projectors onto the symmetric
  and antisymmetric parts of `M ⊗[R] M`.

## Main results

* `TensorProduct.comm_mul_comm`: the exchange operator is an involution.
* `TensorProduct.trace_comm`: its trace is `Module.finrank R M`.
* `TensorProduct.completeOrthogonalIdempotents_antisymmetrizer_symmetrizer`: the two projectors
  are complete orthogonal idempotents.
* `TensorProduct.comm_eq_symmetrizer_sub_antisymmetrizer`: the spectral decomposition of the
  exchange operator.
* `TensorProduct.range_symmetrizer`, `TensorProduct.range_antisymmetrizer`: the projectors project
  onto the symmetric and antisymmetric tensors.
* `TensorProduct.trace_symmetrizer`, `TensorProduct.trace_antisymmetrizer`: the traces of the
  projectors.
* `TensorProduct.symmetrizer_tmul`, `TensorProduct.antisymmetrizer_tmul`: the projectors on a
  pure tensor, `x ⊗ y ↦ ⅟2 • (x ⊗ y ± y ⊗ x)`.
* `TensorProduct.commute_rTensor_add_lTensor_comm`,
  `TensorProduct.commute_rTensor_add_lTensor_symmetrizer`,
  `TensorProduct.commute_rTensor_add_lTensor_antisymmetrizer`: the exchange and the two projectors
  commute with the diagonal action `f ⊗ 1 + 1 ⊗ f` of an endomorphism `f` of `M`.
-/

public section

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

variable {R M}

/-- For every endomorphism `f` of `M`, the diagonal action `f ⊗ 1 + 1 ⊗ f` of `f` on `M ⊗[R] M`
commutes with the exchange of the two factors. -/
theorem commute_rTensor_add_lTensor_comm (f : Module.End R M) :
    Commute (f.rTensor M + f.lTensor M) (TensorProduct.comm R M M).toLinearMap := by
  rw [Commute, SemiconjBy, Module.End.mul_eq_comp, Module.End.mul_eq_comp, LinearMap.add_comp,
    LinearMap.comp_add, LinearMap.rTensor_comp_comm, LinearMap.lTensor_comp_comm, add_comm]

end Semiring

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-- The trace of the exchange operator on the tensor square of a finite free module is its
rank. -/
@[simp]
theorem trace_comm [Module.Free R M] [Module.Finite R M] :
    LinearMap.trace R (M ⊗[R] M) (TensorProduct.comm R M M).toLinearMap = Module.finrank R M := by
  -- The case `f = id` of `LinearMap.trace_map_self_comp_comm`.
  have h := LinearMap.trace_map_self_comp_comm (LinearMap.id : M →ₗ[R] M)
  rwa [TensorProduct.map_id, LinearMap.id_comp, LinearMap.id_comp, LinearMap.trace_id] at h

/-! ### The two projectors -/

section Projectors

variable [Invertible (2 : R)]

/-- The projector `⅟2 • (1 + P)` onto the symmetric part of `M ⊗[R] M`, where `P` exchanges the
two factors: the idempotent `TauCeti.halfOneAdd` cut out by the square root of one `P`. -/
def symmetrizer : Module.End R (M ⊗[R] M) :=
  halfOneAdd R (TensorProduct.comm R M M).toLinearMap

/-- The projector `⅟2 • (1 - P)` onto the antisymmetric part of `M ⊗[R] M`, where `P` exchanges
the two factors: the idempotent `TauCeti.halfOneAdd` cut out by the square root of one `-P`. -/
def antisymmetrizer : Module.End R (M ⊗[R] M) :=
  halfOneAdd R (-(TensorProduct.comm R M M).toLinearMap)

/-- The defining formula `S = ⅟2 • (1 + P)` of the symmetrizer. -/
theorem symmetrizer_def :
    symmetrizer R M = ⅟(2 : R) • (1 + (TensorProduct.comm R M M).toLinearMap) :=
  halfOneAdd_def R _

/-- The defining formula `A = ⅟2 • (1 - P)` of the antisymmetrizer. -/
theorem antisymmetrizer_def :
    antisymmetrizer R M = ⅟(2 : R) • (1 - (TensorProduct.comm R M M).toLinearMap) := by
  rw [antisymmetrizer, halfOneAdd_def, sub_eq_add_neg]

variable {R M}

/-- The symmetrizer is the symmetric part: `S x = ⅟2 • (x + P x)`. -/
@[simp]
theorem symmetrizer_apply (x : M ⊗[R] M) :
    symmetrizer R M x = ⅟(2 : R) • (x + TensorProduct.comm R M M x) := by
  simp [symmetrizer_def]

/-- The antisymmetrizer is the antisymmetric part: `A x = ⅟2 • (x - P x)`. -/
@[simp]
theorem antisymmetrizer_apply (x : M ⊗[R] M) :
    antisymmetrizer R M x = ⅟(2 : R) • (x - TensorProduct.comm R M M x) := by
  simp [antisymmetrizer_def]

/-- The symmetrizer on a pure tensor: `S (x ⊗ y) = ⅟2 • (x ⊗ y + y ⊗ x)`. Not `@[simp]`: `simp`
already derives it from `symmetrizer_apply` and `TensorProduct.comm_tmul`. -/
theorem symmetrizer_tmul (x y : M) :
    symmetrizer R M (x ⊗ₜ y) = ⅟(2 : R) • (x ⊗ₜ y + y ⊗ₜ x) := by
  rw [symmetrizer_apply, comm_tmul]

/-- The antisymmetrizer on a pure tensor: `A (x ⊗ y) = ⅟2 • (x ⊗ y - y ⊗ x)`. Not `@[simp]`:
`simp` already derives it from `antisymmetrizer_apply` and `TensorProduct.comm_tmul`. -/
theorem antisymmetrizer_tmul (x y : M) :
    antisymmetrizer R M (x ⊗ₜ y) = ⅟(2 : R) • (x ⊗ₜ y - y ⊗ₜ x) := by
  rw [antisymmetrizer_apply, comm_tmul]

variable (R M)

/-- The symmetric and antisymmetric parts exhaust the tensor square. -/
@[simp]
theorem symmetrizer_add_antisymmetrizer : symmetrizer R M + antisymmetrizer R M = 1 :=
  halfOneAdd_add_halfOneAdd_neg R _

/-- The symmetric and antisymmetric parts exhaust the tensor square, in the reversed addition
order. -/
@[simp]
theorem antisymmetrizer_add_symmetrizer : antisymmetrizer R M + symmetrizer R M = 1 := by
  rw [add_comm, symmetrizer_add_antisymmetrizer]

/-- The antisymmetrizer is the complement of the symmetrizer. -/
theorem antisymmetrizer_eq_one_sub : antisymmetrizer R M = 1 - symmetrizer R M :=
  halfOneAdd_neg_eq_one_sub R _

/-- The symmetrizer is the complement of the antisymmetrizer. -/
theorem symmetrizer_eq_one_sub : symmetrizer R M = 1 - antisymmetrizer R M :=
  eq_sub_of_add_eq (symmetrizer_add_antisymmetrizer R M)

/-- The spectral decomposition of the exchange operator: `P = S - A`. -/
theorem comm_eq_symmetrizer_sub_antisymmetrizer :
    (TensorProduct.comm R M M).toLinearMap = symmetrizer R M - antisymmetrizer R M :=
  (halfOneAdd_sub_halfOneAdd_neg R _).symm

/-- The symmetrizer is idempotent. -/
theorem isIdempotentElem_symmetrizer : IsIdempotentElem (symmetrizer R M) :=
  isIdempotentElem_halfOneAdd R (comm_mul_comm R M)

/-- The antisymmetrizer is idempotent. -/
theorem isIdempotentElem_antisymmetrizer : IsIdempotentElem (antisymmetrizer R M) :=
  isIdempotentElem_halfOneAdd_neg R (comm_mul_comm R M)

/-- The antisymmetrizer squares to itself. -/
@[simp]
theorem antisymmetrizer_mul_self :
    antisymmetrizer R M * antisymmetrizer R M = antisymmetrizer R M :=
  (isIdempotentElem_antisymmetrizer R M).eq

/-- The symmetrizer squares to itself. -/
@[simp]
theorem symmetrizer_mul_self : symmetrizer R M * symmetrizer R M = symmetrizer R M :=
  (isIdempotentElem_symmetrizer R M).eq

/-- The antisymmetric and symmetric parts are orthogonal. -/
@[simp]
theorem antisymmetrizer_mul_symmetrizer : antisymmetrizer R M * symmetrizer R M = 0 :=
  halfOneAdd_neg_mul_halfOneAdd R (comm_mul_comm R M)

/-- The symmetric and antisymmetric parts are orthogonal. -/
@[simp]
theorem symmetrizer_mul_antisymmetrizer : symmetrizer R M * antisymmetrizer R M = 0 :=
  halfOneAdd_mul_halfOneAdd_neg R (comm_mul_comm R M)

/-- The antisymmetrizer and the symmetrizer are complete orthogonal idempotents: the tensor
square is the direct sum of its antisymmetric and symmetric parts. In submodule form this is
`TauCeti.isCompl_symmetricTensors_antisymmetricTensors`, through `TensorProduct.range_symmetrizer`
and `TensorProduct.range_antisymmetrizer`. -/
theorem completeOrthogonalIdempotents_antisymmetrizer_symmetrizer :
    CompleteOrthogonalIdempotents ![antisymmetrizer R M, symmetrizer R M] := by
  rw [symmetrizer_eq_one_sub]
  exact .of_isIdempotentElem (isIdempotentElem_antisymmetrizer R M)

/-- The exchange operator acts by `-1` on the antisymmetric part: `P * A = -A`. -/
@[simp]
theorem comm_mul_antisymmetrizer :
    (TensorProduct.comm R M M).toLinearMap * antisymmetrizer R M = -antisymmetrizer R M := by
  rw [antisymmetrizer_def, mul_smul_comm, mul_sub, mul_one, comm_mul_comm]
  match_scalars <;> simp

/-- The exchange operator acts by `-1` on the antisymmetric part: `A * P = -A`. -/
@[simp]
theorem antisymmetrizer_mul_comm_eq_neg :
    antisymmetrizer R M * (TensorProduct.comm R M M).toLinearMap = -antisymmetrizer R M := by
  rw [antisymmetrizer_def, smul_mul_assoc, sub_mul, one_mul, comm_mul_comm]
  match_scalars <;> simp

/-- The exchange operator acts by `1` on the symmetric part: `P * S = S`. -/
@[simp]
theorem comm_mul_symmetrizer :
    (TensorProduct.comm R M M).toLinearMap * symmetrizer R M = symmetrizer R M := by
  rw [symmetrizer_def, mul_smul_comm, mul_add, mul_one, comm_mul_comm, add_comm]

/-- The exchange operator acts by `1` on the symmetric part: `S * P = S`. -/
@[simp]
theorem symmetrizer_mul_comm_eq_self :
    symmetrizer R M * (TensorProduct.comm R M M).toLinearMap = symmetrizer R M := by
  rw [symmetrizer_def, smul_mul_assoc, add_mul, one_mul, comm_mul_comm, add_comm]

/-! ### The ranges of the projectors -/

variable {R M}

/-- The antisymmetrizer fixes exactly the antisymmetric tensors. -/
theorem antisymmetrizer_apply_eq_self_iff (x : M ⊗[R] M) :
    antisymmetrizer R M x = x ↔ x ∈ antisymmetricTensors R M := by
  rw [mem_antisymmetricTensors]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($(comm_mul_antisymmetrizer R M) x)
    rwa [Module.End.mul_apply, LinearMap.neg_apply, h, LinearEquiv.coe_coe] at this
  · rw [antisymmetrizer_apply, h, sub_neg_eq_add, ← two_smul R x, invOf_smul_smul]

/-- The symmetrizer fixes exactly the symmetric tensors. -/
theorem symmetrizer_apply_eq_self_iff (x : M ⊗[R] M) :
    symmetrizer R M x = x ↔ x ∈ symmetricTensors R M := by
  rw [mem_symmetricTensors]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($(comm_mul_symmetrizer R M) x)
    rwa [Module.End.mul_apply, h, LinearEquiv.coe_coe] at this
  · rw [symmetrizer_apply, h, ← two_smul R x, invOf_smul_smul]

variable (R M)

/-- The antisymmetrizer projects onto the antisymmetric tensors. -/
theorem range_antisymmetrizer :
    LinearMap.range (antisymmetrizer R M) = antisymmetricTensors R M := by
  ext x
  rw [LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_antisymmetrizer R M),
    antisymmetrizer_apply_eq_self_iff]

/-- The symmetrizer projects onto the symmetric tensors. -/
theorem range_symmetrizer : LinearMap.range (symmetrizer R M) = symmetricTensors R M := by
  ext x
  rw [LinearMap.IsIdempotentElem.mem_range_iff (isIdempotentElem_symmetrizer R M),
    symmetrizer_apply_eq_self_iff]

/-! ### Traces -/

/-- The trace of the symmetrizer on the tensor square of a finite free module of rank `n` is
`n (n + 1) / 2`. Over a field of characteristic zero this is the dimension of the symmetric part,
which is not formalised here. -/
theorem trace_symmetrizer [Module.Free R M] [Module.Finite R M] :
    LinearMap.trace R (M ⊗[R] M) (symmetrizer R M) =
      ⅟(2 : R) * (Module.finrank R M * (Module.finrank R M + 1)) := by
  -- `Module.finrank_tensorProduct` needs `StrongRankCondition R`, which `Nontrivial R` supplies;
  -- over a trivial ring both sides are equal.
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  rw [symmetrizer_def, map_smul, map_add, LinearMap.trace_one, trace_comm,
    Module.finrank_tensorProduct, smul_eq_mul]
  push_cast
  ring

/-- The trace of the antisymmetrizer on the tensor square of a finite free module of rank `n` is
`n (n - 1) / 2`. Over a field of characteristic zero this is the dimension of the antisymmetric
part, which is not formalised here. -/
theorem trace_antisymmetrizer [Module.Free R M] [Module.Finite R M] :
    LinearMap.trace R (M ⊗[R] M) (antisymmetrizer R M) =
      ⅟(2 : R) * (Module.finrank R M * (Module.finrank R M - 1)) := by
  -- `Module.finrank_tensorProduct` needs `StrongRankCondition R`, which `Nontrivial R` supplies;
  -- over a trivial ring both sides are equal.
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  rw [antisymmetrizer_def, map_smul, map_sub, LinearMap.trace_one, trace_comm,
    Module.finrank_tensorProduct, smul_eq_mul]
  push_cast
  ring

/-! ### Invariance under the diagonal action -/

variable {R M}

/-- For every endomorphism `f` of `M`, the diagonal action `f ⊗ 1 + 1 ⊗ f` of `f` on
`M ⊗[R] M` commutes with the antisymmetrizer, so the antisymmetric part is an invariant
subspace. -/
theorem commute_rTensor_add_lTensor_antisymmetrizer (f : Module.End R M) :
    Commute (f.rTensor M + f.lTensor M) (antisymmetrizer R M) :=
  (commute_halfOneAdd R (commute_rTensor_add_lTensor_comm f).symm.neg_left).symm

/-- For every endomorphism `f` of `M`, the diagonal action `f ⊗ 1 + 1 ⊗ f` of `f` on
`M ⊗[R] M` commutes with the symmetrizer, so the symmetric part is an invariant subspace. -/
theorem commute_rTensor_add_lTensor_symmetrizer (f : Module.End R M) :
    Commute (f.rTensor M + f.lTensor M) (symmetrizer R M) :=
  (commute_halfOneAdd R (commute_rTensor_add_lTensor_comm f).symm).symm

end Projectors

end TensorProduct
