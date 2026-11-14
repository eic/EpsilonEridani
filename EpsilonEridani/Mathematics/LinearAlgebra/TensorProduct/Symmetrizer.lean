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
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-!
# The symmetrizer and antisymmetrizer on a tensor square

On the tensor square `M ⊗[R] M` the operator `P = TensorProduct.comm R M M` exchanging the two
factors is an involution, `P * P = 1` (`TensorProduct.comm_mul_comm`). When `2` is invertible in
`R` it therefore splits `M ⊗[R] M` into its symmetric and antisymmetric parts, with projectors

* `TensorProduct.symmProj R M = ⅟2 • (1 + P)`, onto the states fixed by `P`;
* `TensorProduct.antisymmProj R M = ⅟2 • (1 - P)`, onto the states negated by `P`.

The two are complete orthogonal idempotents, and `P = symmProj R M - antisymmProj R M`. The
exchange operator commutes with the action `x ↦ x ⊗ 1 + 1 ⊗ x` of every element `x` of a Lie
algebra acting on `M`, so both parts are invariant under it. For `M` finite free, the trace of
the exchange operator is the rank of `M`.

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
* `TensorProduct.antisymmProj_apply_eq_self_iff`, `TensorProduct.symmProj_apply_eq_self_iff`:
  the antisymmetric and symmetric parts are the `-1` and `1` eigenspaces of the exchange.
* `TensorProduct.commute_toEnd_comm`: the exchange commutes with the action of a Lie algebra.
-/

@[expose] public section

noncomputable section

namespace TensorProduct

variable (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]

/-! ### The exchange operator -/

/-- The exchange operator on a tensor square is an involution: `P * P = 1`. -/
@[simp]
theorem comm_mul_comm :
    (TensorProduct.comm R M M).toLinearMap * (TensorProduct.comm R M M).toLinearMap = 1 :=
  comm_comp_comm R M M

/-- The trace of the exchange operator on the tensor square of a finite free module is its rank:
in a product basis `eᵢ ⊗ eⱼ` it fixes the diagonal vectors and permutes the others. -/
theorem trace_comm [Module.Free R M] [Module.Finite R M] [Nontrivial R] :
    LinearMap.trace R (M ⊗[R] M) (TensorProduct.comm R M M).toLinearMap = Module.finrank R M := by
  let b := Module.Free.chooseBasis R M
  rw [LinearMap.trace_eq_matrix_trace R (b.tensorProduct b), TensorProduct.toMatrix_comm,
    Module.finrank_eq_card_chooseBasisIndex]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply, id, Fintype.sum_prod_type,
    Prod.swap_prod_mk, Matrix.one_apply, Prod.mk.injEq, and_iff_left_of_imp Eq.symm,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_const, Finset.card_univ,
    nsmul_one]

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
two factors. -/
def symmProj : Module.End R (M ⊗[R] M) :=
  ⅟(2 : R) • (1 + (TensorProduct.comm R M M).toLinearMap)

/-- The projector `⅟2 • (1 - P)` onto the antisymmetric part of `M ⊗[R] M`, where `P` exchanges
the two factors. -/
def antisymmProj : Module.End R (M ⊗[R] M) :=
  ⅟(2 : R) • (1 - (TensorProduct.comm R M M).toLinearMap)

variable {R M}

/-- The symmetrizer is the symmetric part: `S x = ⅟2 • (x + P x)`. -/
@[simp]
theorem symmProj_apply (x : M ⊗[R] M) :
    symmProj R M x = ⅟(2 : R) • (x + TensorProduct.comm R M M x) := by
  simp [symmProj]

/-- The antisymmetrizer is the antisymmetric part: `A x = ⅟2 • (x - P x)`. -/
@[simp]
theorem antisymmProj_apply (x : M ⊗[R] M) :
    antisymmProj R M x = ⅟(2 : R) • (x - TensorProduct.comm R M M x) := by
  simp [antisymmProj]

variable (R M)

/-- The symmetric and antisymmetric parts exhaust the tensor square. -/
@[simp]
theorem symmProj_add_antisymmProj : symmProj R M + antisymmProj R M = 1 := by
  rw [symmProj, antisymmProj, ← smul_add, add_add_sub_cancel, ← two_smul R, smul_smul,
    invOf_mul_self, one_smul]

/-- The symmetric and antisymmetric parts exhaust the tensor square, in the reversed addition
order. -/
@[simp]
theorem antisymmProj_add_symmProj : antisymmProj R M + symmProj R M = 1 := by
  rw [add_comm, symmProj_add_antisymmProj]

/-- The symmetrizer is the complement of the antisymmetrizer. -/
theorem symmProj_eq_one_sub : symmProj R M = 1 - antisymmProj R M :=
  eq_sub_of_add_eq (symmProj_add_antisymmProj R M)

/-- The exchange operator acts by `-1` on the antisymmetric part: `P * A = -A`. -/
@[simp]
theorem comm_mul_antisymmProj :
    (TensorProduct.comm R M M).toLinearMap * antisymmProj R M = -antisymmProj R M := by
  rw [antisymmProj, mul_smul_comm, mul_sub, mul_one, comm_mul_comm]
  match_scalars <;> simp

/-- The exchange operator acts by `-1` on the antisymmetric part: `A * P = -A`. -/
@[simp]
theorem antisymmProj_mul_comm :
    antisymmProj R M * (TensorProduct.comm R M M).toLinearMap = -antisymmProj R M := by
  rw [antisymmProj, smul_mul_assoc, sub_mul, one_mul, comm_mul_comm]
  match_scalars <;> simp

/-- The exchange operator acts by `1` on the symmetric part: `P * S = S`. -/
@[simp]
theorem comm_mul_symmProj :
    (TensorProduct.comm R M M).toLinearMap * symmProj R M = symmProj R M := by
  rw [symmProj, mul_smul_comm, mul_add, mul_one, comm_mul_comm, add_comm]

/-- The exchange operator acts by `1` on the symmetric part: `S * P = S`. -/
@[simp]
theorem symmProj_mul_comm :
    symmProj R M * (TensorProduct.comm R M M).toLinearMap = symmProj R M := by
  rw [symmProj, smul_mul_assoc, add_mul, one_mul, comm_mul_comm, add_comm]

/-- The spectral decomposition of the exchange operator: `P = S - A`. -/
theorem comm_eq_symmProj_sub_antisymmProj :
    (TensorProduct.comm R M M).toLinearMap = symmProj R M - antisymmProj R M := by
  rw [symmProj, antisymmProj]
  match_scalars <;> simp [← two_mul]

/-- The antisymmetrizer is idempotent. -/
theorem isIdempotentElem_antisymmProj : IsIdempotentElem (antisymmProj R M) := by
  rw [IsIdempotentElem]
  nth_rw 1 [antisymmProj]
  rw [smul_mul_assoc, sub_mul, one_mul, comm_mul_antisymmProj, sub_neg_eq_add]
  match_scalars
  simp [← mul_two]

/-- The symmetrizer is idempotent. -/
theorem isIdempotentElem_symmProj : IsIdempotentElem (symmProj R M) := by
  rw [symmProj_eq_one_sub]
  exact (isIdempotentElem_antisymmProj R M).one_sub

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
theorem antisymmProj_mul_symmProj : antisymmProj R M * symmProj R M = 0 := by
  rw [symmProj_eq_one_sub, (isIdempotentElem_antisymmProj R M).mul_one_sub_self]

/-- The symmetric and antisymmetric parts are orthogonal. -/
@[simp]
theorem symmProj_mul_antisymmProj : symmProj R M * antisymmProj R M = 0 := by
  rw [symmProj_eq_one_sub, (isIdempotentElem_antisymmProj R M).one_sub_mul_self]

/-- The antisymmetrizer and the symmetrizer are complete orthogonal idempotents: the tensor
square is the direct sum of its antisymmetric and symmetric parts. -/
theorem completeOrthogonalIdempotents_antisymmProj_symmProj :
    CompleteOrthogonalIdempotents ![antisymmProj R M, symmProj R M] := by
  rw [symmProj_eq_one_sub]
  exact .of_isIdempotentElem (isIdempotentElem_antisymmProj R M)

variable {R M}

/-- A vector lies in the antisymmetric part exactly when the exchange negates it. -/
theorem antisymmProj_apply_eq_self_iff (x : M ⊗[R] M) :
    antisymmProj R M x = x ↔ TensorProduct.comm R M M x = -x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($(comm_mul_antisymmProj R M) x)
    rwa [Module.End.mul_apply, LinearMap.neg_apply, h, LinearEquiv.coe_coe] at this
  · rw [antisymmProj_apply, h, sub_neg_eq_add, ← two_smul R x, smul_smul, invOf_mul_self,
      one_smul]

/-- A vector lies in the symmetric part exactly when the exchange fixes it. -/
theorem symmProj_apply_eq_self_iff (x : M ⊗[R] M) :
    symmProj R M x = x ↔ TensorProduct.comm R M M x = x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have := congr($(comm_mul_symmProj R M) x)
    rwa [Module.End.mul_apply, h, LinearEquiv.coe_coe] at this
  · rw [symmProj_apply, h, ← two_smul R x, smul_smul, invOf_mul_self, one_smul]


section Lie

variable {L : Type*} [LieRing L] [LieAlgebra R L] [LieRingModule L M] [LieModule R L M]

/-- For every element `x` of a Lie algebra acting on `M`, the action `x ⊗ 1 + 1 ⊗ x` of `x` on
`M ⊗[R] M` commutes with the antisymmetrizer, so the antisymmetric part is an invariant
subspace. -/
theorem commute_toEnd_antisymmProj (x : L) :
    Commute (LieModule.toEnd R L (M ⊗[R] M) x) (antisymmProj R M) :=
  ((Commute.one_right _).sub_right (commute_toEnd_comm x)).smul_right _

/-- For every element `x` of a Lie algebra acting on `M`, the action `x ⊗ 1 + 1 ⊗ x` of `x` on
`M ⊗[R] M` commutes with the symmetrizer, so the symmetric part is an invariant subspace. -/
theorem commute_toEnd_symmProj (x : L) :
    Commute (LieModule.toEnd R L (M ⊗[R] M) x) (symmProj R M) :=
  ((Commute.one_right _).add_right (commute_toEnd_comm x)).smul_right _

end Lie

end Projectors

end TensorProduct
