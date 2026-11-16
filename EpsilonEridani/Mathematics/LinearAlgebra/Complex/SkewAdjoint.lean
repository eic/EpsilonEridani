/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Real dimensions of the self-adjoint and skew-adjoint parts

Every element of a star module over a ring in which `2` is invertible is uniquely the sum of a
self-adjoint and a skew-adjoint element (`StarModule.decomposeProdAdjoint`), so the two parts
have complementary dimensions. Over `ℂ`, multiplication by `Complex.I` exchanges them
(`skewAdjoint.negISMul`), so they have the same real dimension, half that of the whole space.

For complex `n × n` matrices this computes the real dimension of the skew-Hermitian matrices,
the Lie algebra `𝔲(n)` of the unitary group, as `n²`.

## Main results

* `finrank_selfAdjoint_add_finrank_skewAdjoint`: the real dimensions of the self-adjoint and
  skew-adjoint parts add up to that of the space.
* `finrank_skewAdjoint_eq_finrank_selfAdjoint`: in a complex star module, the skew-adjoint and
  self-adjoint parts have the same real dimension.
* `Matrix.finrank_real_skewAdjoint`: the skew-Hermitian complex `n × n` matrices form a real
  vector space of dimension `n²`.
-/

public section

open Module

section SelfSkewAdjoint

variable (R : Type*) {A : Type*} [Field R] [StarMul R] [TrivialStar R]
  [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A] [FiniteDimensional R A]

/-- The self-adjoint part of a finite-dimensional star module is finite-dimensional. -/
instance : FiniteDimensional R (selfAdjoint A) :=
  .of_injective (selfAdjoint.submodule R A).subtype Subtype.val_injective

/-- The skew-adjoint part of a finite-dimensional star module is finite-dimensional. -/
instance : FiniteDimensional R (skewAdjoint A) :=
  .of_injective (skewAdjoint.submodule R A).subtype Subtype.val_injective

variable [Invertible (2 : R)]

/-- The dimensions of the self-adjoint and skew-adjoint parts of a finite-dimensional star module
add up to the dimension of the module. -/
theorem finrank_selfAdjoint_add_finrank_skewAdjoint :
    finrank R (selfAdjoint A) + finrank R (skewAdjoint A) = finrank R A := by
  rw [← Module.finrank_prod, (StarModule.decomposeProdAdjoint R A).finrank_eq]

end SelfSkewAdjoint

section Complex

open Complex

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- In a complex star module, multiplication by `-I` identifies the skew-adjoint part with the
self-adjoint part, so the two have the same real dimension. -/
theorem finrank_skewAdjoint_eq_finrank_selfAdjoint :
    finrank ℝ (skewAdjoint A) = finrank ℝ (selfAdjoint A) := by
  refine (LinearEquiv.ofBijective (skewAdjoint.negISMul (A := A)) ⟨fun a b h => ?_,
    fun b => ⟨⟨I • (b : A), I_smul_mem_skewAdjoint_iff_isSelfAdjoint.2 b.2⟩, ?_⟩⟩).finrank_eq
  · ext
    rw [← skewAdjoint.I_smul_neg_I a, ← skewAdjoint.I_smul_neg_I b, h]
  · ext
    simp [smul_smul]

end Complex

namespace Matrix

variable (n : Type*) [Fintype n]

/-- The skew-Hermitian complex `n × n` matrices, the Lie algebra `𝔲(n)` of the unitary group,
form a real vector space of dimension `n²`. -/
theorem finrank_real_skewAdjoint :
    finrank ℝ (skewAdjoint (Matrix n n ℂ)) = Fintype.card n ^ 2 := by
  have h := finrank_selfAdjoint_add_finrank_skewAdjoint ℝ (A := Matrix n n ℂ)
  rw [finrank_skewAdjoint_eq_finrank_selfAdjoint, finrank_matrix,
    Complex.finrank_real_complex] at h
  rw [finrank_skewAdjoint_eq_finrank_selfAdjoint]
  nlinarith

end Matrix
