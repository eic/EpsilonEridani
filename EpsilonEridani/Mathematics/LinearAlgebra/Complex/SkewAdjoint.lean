/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import EpsilonEridani.Mathematics.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose

/-!
# Real dimensions of the self-adjoint and skew-adjoint parts of a complex star module

In a complex star module, multiplication by `-Complex.I` is a real-linear equivalence from the
skew-adjoint part onto the self-adjoint part (`skewAdjoint.negISMulEquiv`), with inverse
multiplication by `Complex.I`. The two parts therefore have the same real dimension, and since
they are complementary (`finrank_selfAdjoint_add_finrank_skewAdjoint`) each has real dimension
equal to the complex dimension of the whole space.

For complex `n × n` matrices this computes the real dimensions of the Hermitian matrices and of the
skew-Hermitian matrices, the Lie algebra `𝔲(n)` of the unitary group, as `n²`.

## Main results

* `skewAdjoint.negISMulEquiv`: multiplication by `-I` as a real-linear equivalence
  `skewAdjoint A ≃ₗ[ℝ] selfAdjoint A`.
* `Complex.finrank_real_skewAdjoint_eq_finrank_selfAdjoint`: in a complex star module, the
  skew-adjoint and self-adjoint parts have the same real dimension.
* `Complex.finrank_real_selfAdjoint`, `Complex.finrank_real_skewAdjoint`: in a finite-dimensional
  complex star module, each part has real dimension equal to the complex dimension of the space.
* `Matrix.finrank_real_selfAdjoint_complex`, `Matrix.finrank_real_skewAdjoint_complex`: the
  Hermitian and the skew-Hermitian complex `n × n` matrices each form a real vector space of
  dimension `n²`.
-/

public section

open Module Complex

variable {A : Type*} [AddCommGroup A] [Module ℂ A] [StarAddMonoid A] [StarModule ℂ A]

/-- Multiplication by `-I` as a real-linear equivalence from the skew-adjoint part of a complex
star module onto its self-adjoint part, with inverse multiplication by `I`. Its forward map is
`skewAdjoint.negISMul`. -/
def skewAdjoint.negISMulEquiv : skewAdjoint A ≃ₗ[ℝ] selfAdjoint A where
  toFun := skewAdjoint.negISMul
  map_add' := skewAdjoint.negISMul.map_add
  map_smul' := skewAdjoint.negISMul.map_smul
  invFun b := ⟨I • (b : A), I_smul_mem_skewAdjoint_iff_isSelfAdjoint.2 b.2⟩
  left_inv a := Subtype.ext (skewAdjoint.I_smul_neg_I a)
  right_inv b := by ext; simp [smul_smul]

/-- The forward map of `skewAdjoint.negISMulEquiv` is `skewAdjoint.negISMul`. -/
@[simp]
theorem skewAdjoint.negISMulEquiv_apply (a : skewAdjoint A) :
    skewAdjoint.negISMulEquiv a = skewAdjoint.negISMul a :=
  (rfl)

/-- The inverse of `skewAdjoint.negISMulEquiv` is multiplication by `I`. -/
@[simp]
theorem skewAdjoint.coe_negISMulEquiv_symm_apply (b : selfAdjoint A) :
    ((skewAdjoint.negISMulEquiv.symm b : skewAdjoint A) : A) = I • (b : A) :=
  (rfl)

namespace Complex

/-- In a complex star module, multiplication by `-I` identifies the skew-adjoint part with the
self-adjoint part, so the two have the same real dimension. -/
theorem finrank_real_skewAdjoint_eq_finrank_selfAdjoint :
    finrank ℝ (skewAdjoint A) = finrank ℝ (selfAdjoint A) :=
  skewAdjoint.negISMulEquiv.finrank_eq

variable [FiniteDimensional ℝ A]

/-- The self-adjoint part of a finite-dimensional complex star module has real dimension equal to
the complex dimension of the module. -/
theorem finrank_real_selfAdjoint : finrank ℝ (selfAdjoint A) = finrank ℂ A := by
  have h := finrank_selfAdjoint_add_finrank_skewAdjoint ℝ (A := A)
  rw [finrank_real_skewAdjoint_eq_finrank_selfAdjoint, finrank_real_of_complex] at h
  omega

/-- The skew-adjoint part of a finite-dimensional complex star module has real dimension equal to
the complex dimension of the module. -/
theorem finrank_real_skewAdjoint : finrank ℝ (skewAdjoint A) = finrank ℂ A := by
  rw [finrank_real_skewAdjoint_eq_finrank_selfAdjoint, finrank_real_selfAdjoint]

end Complex

namespace Matrix

variable (n : Type*) [Fintype n]

/-- The Hermitian complex `n × n` matrices form a real vector space of dimension `n²`. -/
theorem finrank_real_selfAdjoint_complex :
    finrank ℝ (selfAdjoint (Matrix n n ℂ)) = Fintype.card n ^ 2 := by
  rw [Complex.finrank_real_selfAdjoint, finrank_matrix, Module.finrank_self, mul_one, sq]

/-- The skew-Hermitian complex `n × n` matrices, the Lie algebra `𝔲(n)` of the unitary group,
form a real vector space of dimension `n²`. -/
theorem finrank_real_skewAdjoint_complex :
    finrank ℝ (skewAdjoint (Matrix n n ℂ)) = Fintype.card n ^ 2 := by
  rw [Complex.finrank_real_skewAdjoint_eq_finrank_selfAdjoint, finrank_real_selfAdjoint_complex]

end Matrix
