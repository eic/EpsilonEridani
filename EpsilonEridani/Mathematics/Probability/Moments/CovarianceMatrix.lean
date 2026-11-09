/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Moments.Covariance
/-!

# The covariance matrix of a finite family of random variables

For a finite family `X : ι → Ω → ℝ` of real random variables, `covarianceMatrix X μ` is the
matrix of pairwise covariances `cov[X i, X j; μ]`. This file proves that it is the matrix of the
covariance of linear combinations: the covariance of `c ⬝ᵥ X` and `c' ⬝ᵥ X` is
`c ⬝ᵥ covarianceMatrix X μ *ᵥ c'`. Positive semidefiniteness and the characterisation of the
linear combinations that are almost surely equal to their integral follow from this.

Mathlib records the same object coordinate-free, as `ProbabilityTheory.covarianceBilin` of the law
of `X` on `EuclideanSpace ℝ ι` (see `ProbabilityTheory.covarianceBilin_apply_pi`), and Tau Ceti
records the matrix of that law as `TauCeti.covMatrix`. The family-indexed matrix here is the one
in which a finite covariance enters linear algebra as a `Matrix.PosSemidef` without passing to the
law; `covarianceMatrix_eq_covMatrix_map` identifies it with Tau Ceti's matrix of the law, and
`covarianceMatrix_proj_eq_covMatrix` with Tau Ceti's matrix of a measure on `EuclideanSpace ℝ ι`.

All declarations live in the namespace `EpsilonEridani.ProbabilityTheory`.

## Main results

* `covariance_dotProduct_dotProduct`: `cov[c ⬝ᵥ X, c' ⬝ᵥ X] = c ⬝ᵥ covarianceMatrix X μ *ᵥ c'`,
  and `variance_dotProduct` for the variance.
* `posSemidef_covarianceMatrix`: the covariance matrix of square-integrable random variables is
  positive semidefinite.
* `variance_eq_zero_iff`: a square-integrable random variable has zero variance exactly when it is
  almost surely equal to its integral.
* `ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero`: the linear combination `c ⬝ᵥ X` is almost
  surely equal to its integral exactly when `c` lies in the kernel of the covariance matrix.
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
@[simp]
theorem covarianceMatrix_comp (X : ι → Ω → ℝ) (μ : Measure Ω) (e : κ → ι) :
    covarianceMatrix (X ∘ e) μ = (covarianceMatrix X μ).submatrix e e := by
  ext
  simp

/-- The covariance matrix of the coordinate projections of a measure on `EuclideanSpace ℝ ι` is
Tau Ceti's covariance matrix of that measure. -/
theorem covarianceMatrix_proj_eq_covMatrix (μ : Measure (EuclideanSpace ℝ ι)) :
    covarianceMatrix (fun i (z : EuclideanSpace ℝ ι) => z i) μ = TauCeti.covMatrix μ := by
  ext
  simp

/-- The covariance matrix of a countable family of almost everywhere measurable random variables
is Tau Ceti's covariance matrix of the law of the random vector `X` on `EuclideanSpace ℝ ι`. -/
theorem covarianceMatrix_eq_covMatrix_map [Countable ι] (hX : ∀ i, AEMeasurable (X i) μ) :
    covarianceMatrix X μ = TauCeti.covMatrix (μ.map fun ω => WithLp.toLp 2 (X · ω)) := by
  have hmeas : AEMeasurable (fun ω => (WithLp.toLp 2 (X · ω) : EuclideanSpace ℝ ι)) μ :=
    (WithLp.measurable_toLp 2 _).comp_aemeasurable (aemeasurable_pi_iff.2 hX)
  ext i j
  -- The coordinates of `WithLp.toLp 2 (X · ω)` are the `X i ω` by `PiLp.toLp_apply`, which is
  -- `rfl`, so pulling the covariance back along the random vector gives `cov[X i, X j; μ]`.
  have h : cov[fun z : EuclideanSpace ℝ ι => z i, fun z => z j;
      μ.map fun ω => WithLp.toLp 2 (X · ω)] = cov[X i, X j; μ] :=
    covariance_map_fun (by fun_prop) (by fun_prop) hmeas
  rw [covarianceMatrix_apply, TauCeti.covMatrix_apply, h]

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

omit [Fintype ι] in
/-- A square-integrable random variable has zero variance exactly when it is almost surely equal
to its integral `μ[·]`. -/
theorem variance_eq_zero_iff {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    Var[Y; μ] = 0 ↔ Y =ᵐ[μ] fun _ => μ[Y] := by
  rw [← evariance_eq_zero_iff hY.aemeasurable, variance, ENNReal.toReal_eq_zero_iff,
    or_iff_left (evariance_lt_top hY).ne]

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

/-- A linear combination of square-integrable random variables is almost surely equal to its
integral `μ[·]` exactly when its coefficient vector lies in the kernel of the covariance matrix.
For a probability measure the integral is the mean. -/
theorem ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero (hX : ∀ i, MemLp (X i) 2 μ)
    (c : ι → ℝ) :
    ((fun ω => c ⬝ᵥ (X · ω)) =ᵐ[μ] fun _ => μ[fun ω => c ⬝ᵥ (X · ω)]) ↔
      covarianceMatrix X μ *ᵥ c = 0 := by
  rw [← variance_dotProduct_eq_zero_iff hX, variance_eq_zero_iff (memLp_dotProduct hX c)]

end ProbabilityTheory
end EpsilonEridani
