/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Moments.Variance
/-!

# The covariance matrix of a finite family of random variables

For a finite family `X : ι → Ω → ℝ` of real random variables, `covarianceMatrix X μ` is the
matrix of pairwise covariances `cov[X i, X j; μ]`. This file proves that it is the matrix of the
covariance of linear combinations: the covariance of `c ⬝ᵥ X` and `c' ⬝ᵥ X` is
`c ⬝ᵥ covarianceMatrix X μ *ᵥ c'`. Positive semidefiniteness and the characterisation of the
linear combinations that are almost surely constant follow from this.

Mathlib records the same object coordinate-free, as `ProbabilityTheory.covarianceBilin` of the law
of `X` on `EuclideanSpace ℝ ι` (see `ProbabilityTheory.covarianceBilin_apply_pi`); the matrix form
here is the one in which a finite covariance enters linear algebra as a `Matrix.PosSemidef`.

All declarations live in the namespace `EpsilonEridani.ProbabilityTheory`.

## Main results

* `covariance_dotProduct_dotProduct`: `cov[c ⬝ᵥ X, c' ⬝ᵥ X] = c ⬝ᵥ covarianceMatrix X μ *ᵥ c'`,
  and `variance_dotProduct` for the variance.
* `posSemidef_covarianceMatrix`: the covariance matrix of square-integrable random variables is
  positive semidefinite.
* `ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero`: the linear combination `c ⬝ᵥ X` is almost
  surely equal to its mean exactly when `c` lies in the kernel of the covariance matrix.
-/

public section

namespace EpsilonEridani
namespace ProbabilityTheory

open MeasureTheory _root_.ProbabilityTheory Matrix

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : ι → Ω → ℝ}

/-- The *covariance matrix* of a family of real random variables: its `(i, j)` entry is
`cov[X i, X j; μ]`. -/
noncomputable def covarianceMatrix (X : ι → Ω → ℝ) (μ : Measure Ω) : Matrix ι ι ℝ :=
  Matrix.of fun i j => cov[X i, X j; μ]

/-- The entries of the covariance matrix are the pairwise covariances. -/
@[simp]
theorem covarianceMatrix_apply (X : ι → Ω → ℝ) (μ : Measure Ω) (i j : ι) :
    covarianceMatrix X μ i j = cov[X i, X j; μ] :=
  (rfl)

/-- The covariance matrix of a reindexed family is the corresponding submatrix. -/
theorem covarianceMatrix_comp (X : ι → Ω → ℝ) (μ : Measure Ω) (e : κ → ι) :
    covarianceMatrix (X ∘ e) μ = (covarianceMatrix X μ).submatrix e e := by
  ext
  simp

/-- The covariance matrix is symmetric. -/
theorem isHermitian_covarianceMatrix (X : ι → Ω → ℝ) (μ : Measure Ω) :
    (covarianceMatrix X μ).IsHermitian := by
  ext i j
  simp [covariance_comm]

variable [Fintype ι]

/-- A linear combination of random variables in `Lᵖ` is in `Lᵖ`. -/
theorem memLp_dotProduct {p : ENNReal} (hX : ∀ i, MemLp (X i) p μ) (c : ι → ℝ) :
    MemLp (fun ω => c ⬝ᵥ (X · ω)) p μ := by
  simp only [dotProduct]
  exact memLp_finsetSum _ fun i _ => (hX i).const_mul (c i)

variable [IsFiniteMeasure μ]

/-- The covariance of two linear combinations of square-integrable random variables is the
bilinear form of the covariance matrix. -/
theorem covariance_dotProduct_dotProduct (hX : ∀ i, MemLp (X i) 2 μ) (c c' : ι → ℝ) :
    cov[fun ω => c ⬝ᵥ (X · ω), fun ω => c' ⬝ᵥ (X · ω); μ] =
      c ⬝ᵥ covarianceMatrix X μ *ᵥ c' := by
  have hc : ∀ (a : ι → ℝ) i, MemLp (fun ω => a i * X i ω) 2 μ := fun a i => (hX i).const_mul _
  simp only [dotProduct, covariance_fun_sum_fun_sum (hc c) (hc c'), covariance_const_mul_left,
    covariance_const_mul_right, mulVec, covarianceMatrix_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The variance of a linear combination of square-integrable random variables is the quadratic
form of the covariance matrix. -/
theorem variance_dotProduct (hX : ∀ i, MemLp (X i) 2 μ) (c : ι → ℝ) :
    Var[fun ω => c ⬝ᵥ (X · ω); μ] = c ⬝ᵥ covarianceMatrix X μ *ᵥ c := by
  rw [← covariance_dotProduct_dotProduct hX, covariance_self (memLp_dotProduct hX c).aemeasurable]

omit [Fintype ι] in
/-- The covariance matrix of square-integrable random variables is positive semidefinite. -/
theorem posSemidef_covarianceMatrix [Finite ι] (hX : ∀ i, MemLp (X i) 2 μ) :
    (covarianceMatrix X μ).PosSemidef :=
  have := Fintype.ofFinite ι
  .of_dotProduct_mulVec_nonneg (isHermitian_covarianceMatrix X μ) fun c => by
    simpa [variance_dotProduct hX] using variance_nonneg (fun ω => c ⬝ᵥ (X · ω)) μ

/-- A linear combination of square-integrable random variables has zero variance exactly when its
coefficient vector lies in the kernel of the covariance matrix. -/
theorem variance_dotProduct_eq_zero_iff (hX : ∀ i, MemLp (X i) 2 μ) (c : ι → ℝ) :
    Var[fun ω => c ⬝ᵥ (X · ω); μ] = 0 ↔ covarianceMatrix X μ *ᵥ c = 0 := by
  simpa [variance_dotProduct hX] using (posSemidef_covarianceMatrix hX).dotProduct_mulVec_zero_iff

/-- A linear combination of square-integrable random variables is almost surely equal to its mean
exactly when its coefficient vector lies in the kernel of the covariance matrix. -/
theorem ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero (hX : ∀ i, MemLp (X i) 2 μ)
    (c : ι → ℝ) :
    ((fun ω => c ⬝ᵥ (X · ω)) =ᵐ[μ] fun _ => μ[fun ω => c ⬝ᵥ (X · ω)]) ↔
      covarianceMatrix X μ *ᵥ c = 0 := by
  have hc := memLp_dotProduct hX c
  rw [← variance_dotProduct_eq_zero_iff hX, ← evariance_eq_zero_iff hc.aemeasurable]
  simp [variance, ENNReal.toReal_eq_zero_iff, (evariance_lt_top hc).ne]

end ProbabilityTheory
end EpsilonEridani
