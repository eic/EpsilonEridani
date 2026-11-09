/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.DataStructures.Matrix.Extend
public import EpsilonEridani.Mathematics.Probability.Moments.CovarianceMatrix
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.LinearAlgebra.Matrix.ToQuadraticForm
/-!

# Euclidean datasets and their noise model

A Euclidean calculation returns finitely many renormalised matrix elements together with their
covariance. This file axiomatises that output as data, so that statements about what a Euclidean
calculation determines can be made about it without any lattice construction.

* A `EuclideanDataset ι` is a family of real central values `value : ι → ℝ` indexed by a finite
  type `ι` labelling the observations, with a positive semidefinite covariance matrix.
* A linear functional of the data is a coefficient vector `c : ι → ℝ`. The covariance of two
  functionals is the bilinear form `EuclideanDataset.covarianceForm` of the covariance matrix,
  the variance of one is the associated quadratic form `EuclideanDataset.variance`, and the
  functionals of variance zero form the *determined subspace*
  `EuclideanDataset.determinedSubspace`, the kernel of the covariance.
* `EuclideanDataset.IsNoiseModel` says that a random vector on a probability space has the
  central values of a dataset as its means and the covariance of the dataset as its covariance
  matrix. For a noise model the covariance of two functionals is the covariance of the
  corresponding random variables, and a functional lies in the determined subspace exactly when
  the random variable is almost surely equal to the functional of the central values: the exactly
  determined functionals are those that carry no noise.
* `EuclideanDataset.HasContinuumLimit` says that a family of datasets indexed by the lattice
  spacing `a` converges as `a → 0⁺`. It is a property of a family, never of one dataset.

## Main results

* `EuclideanDataset.comp`: the reindexing of a dataset along any map is a dataset, its covariance
  being the corresponding submatrix of the original one.
* `EuclideanDataset.mem_determinedSubspace_iff_variance_eq_zero`: the functionals of variance zero
  are the kernel of the covariance; adding one to a functional does not change its variance
  (`EuclideanDataset.variance_add_of_mem_determinedSubspace`).
* `EuclideanDataset.IsNoiseModel.ae_eq_dotProduct_value_iff_mem_determinedSubspace`: under a noise
  model, `c ⬝ᵥ X` is almost surely `c ⬝ᵥ value` exactly when `c` is in the determined subspace.
* `EuclideanDataset.hasContinuumLimit_ofTendsto`: if the covariances of a family converge, the
  limit covariance is again positive semidefinite, so together with any central values it forms a
  dataset `EuclideanDataset.ofTendsto`; when the central values converge as well, the limits form
  the continuum limit of the family; it is unique
  (`EuclideanDataset.HasContinuumLimit.unique`), and covariances and variances converge with it.

## Implementation notes

`covarianceForm` is `Matrix.toBilin'` of the covariance and `variance` is
`Matrix.toQuadraticForm'` of it, the quadratic form `LinearMap.BilinMap.toQuadraticMap` of the
same matrix, so that linearity in each functional is Mathlib's `map_add` and `map_smul` and the
polarisation identity is `LinearMap.BilinMap.polar_toQuadraticMap`. Both `Matrix.toBilin'` and
`Matrix.toQuadraticForm'` are stated under a `DecidableEq ι` instance, which is taken classically:
every use of the forms is propositional.

## References

* J. Karpie, K. Orginos, A. Rothkopf and S. Zafeiropoulos, *Reconstructing parton distribution
  functions from Ioffe time data: from Bayesian methods to neural networks*, JHEP 04 (2019) 057.
* X. Ji, Y.-S. Liu, Y. Liu, J.-H. Zhang and Y. Zhao, *Large-momentum effective theory*,
  Rev. Mod. Phys. 93 (2021) 035005.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Lattice

open MeasureTheory _root_.ProbabilityTheory _root_.Matrix Filter Topology
open _root_.EpsilonEridani.ProbabilityTheory

/-- A *Euclidean dataset*: renormalised matrix elements `value i`, one for each of finitely many
observation labels `i : ι`, together with their covariance matrix, which is positive
semidefinite. -/
@[ext]
structure EuclideanDataset (ι : Type*) [Finite ι] where
  /-- The central value of each observation. -/
  value : ι → ℝ
  /-- The covariance matrix of the observations. -/
  covariance : Matrix ι ι ℝ
  /-- The covariance matrix is positive semidefinite. -/
  posSemidef_covariance : covariance.PosSemidef

namespace EuclideanDataset

variable {ι κ ν : Type*}

section Finite

variable [Finite ι] [Finite κ] [Finite ν]

/-! ### Reindexing -/

/-- The reindexing of a dataset along a map `e : κ → ι`: the central values `value ∘ e` with the
covariance submatrix along `e`. -/
def comp (D : EuclideanDataset ι) (e : κ → ι) : EuclideanDataset κ where
  value := D.value ∘ e
  covariance := D.covariance.submatrix e e
  posSemidef_covariance := D.posSemidef_covariance.submatrix e

/-- The central values of a reindexed dataset are the central values along the reindexing. -/
@[simp]
theorem comp_value (D : EuclideanDataset ι) (e : κ → ι) : (D.comp e).value = D.value ∘ e :=
  (rfl)

/-- The covariance of a reindexed dataset is the covariance submatrix along the reindexing. -/
@[simp]
theorem comp_covariance (D : EuclideanDataset ι) (e : κ → ι) :
    (D.comp e).covariance = D.covariance.submatrix e e :=
  (rfl)

/-- Reindexing along the identity does nothing. -/
@[simp]
theorem comp_id (D : EuclideanDataset ι) : D.comp id = D :=
  (rfl)

/-- Reindexing twice is reindexing along the composite. -/
@[simp]
theorem comp_comp (D : EuclideanDataset ι) (e : κ → ι) (e' : ν → κ) :
    (D.comp e).comp e' = D.comp (e ∘ e') :=
  (rfl)

/-! ### Continuum limits -/

/-- A family `F a` of datasets at lattice spacing `a`, all with the same observation labels, has
*continuum limit* `D` when its central values and covariances converge to those of `D` as the
spacing tends to zero from above. -/
structure HasContinuumLimit (F : ℝ → EuclideanDataset ι) (D : EuclideanDataset ι) : Prop where
  /-- The central values converge as `a → 0⁺`. -/
  tendsto_value : Tendsto (fun a => (F a).value) (𝓝[>] 0) (𝓝 D.value)
  /-- The covariances converge as `a → 0⁺`. -/
  tendsto_covariance : Tendsto (fun a => (F a).covariance) (𝓝[>] 0) (𝓝 D.covariance)

section ofTendsto

variable {F : ℝ → EuclideanDataset ι} {v : ι → ℝ} {S : Matrix ι ι ℝ}

/-- The dataset with central values `v` and covariance `S`, where the covariances of a family of
datasets converge to `S` as `a → 0⁺`: the limit of positive semidefinite matrices is again
positive semidefinite. When the central values also converge to `v`, it is the continuum limit of
the family (`hasContinuumLimit_ofTendsto`). -/
def ofTendsto (v : ι → ℝ) (hS : Tendsto (fun a => (F a).covariance) (𝓝[>] 0) (𝓝 S)) :
    EuclideanDataset ι where
  value := v
  covariance := S
  posSemidef_covariance :=
    posSemidef_is_closed.mem_of_tendsto hS (.of_forall fun a => (F a).posSemidef_covariance)

/-- The central values of `ofTendsto v hS` are `v`. -/
@[simp]
theorem ofTendsto_value (v : ι → ℝ) (hS : Tendsto (fun a => (F a).covariance) (𝓝[>] 0) (𝓝 S)) :
    (ofTendsto v hS).value = v :=
  (rfl)

/-- The covariance of `ofTendsto v hS` is the limit of the covariances. -/
@[simp]
theorem ofTendsto_covariance (v : ι → ℝ) (hS : Tendsto (fun a => (F a).covariance) (𝓝[>] 0) (𝓝 S)) :
    (ofTendsto v hS).covariance = S :=
  (rfl)

/-- If the central values and the covariances of a family of datasets converge as `a → 0⁺`, then
the limits form the continuum limit of the family. -/
theorem hasContinuumLimit_ofTendsto (hv : Tendsto (fun a => (F a).value) (𝓝[>] 0) (𝓝 v))
    (hS : Tendsto (fun a => (F a).covariance) (𝓝[>] 0) (𝓝 S)) :
    HasContinuumLimit F (ofTendsto v hS) :=
  ⟨hv, hS⟩

end ofTendsto

namespace HasContinuumLimit

variable {F : ℝ → EuclideanDataset ι} {D D' : EuclideanDataset ι}

/-- The continuum limit of a family of datasets is unique. -/
theorem unique (h : HasContinuumLimit F D) (h' : HasContinuumLimit F D') : D = D' :=
  EuclideanDataset.ext (tendsto_nhds_unique h.tendsto_value h'.tendsto_value)
    (tendsto_nhds_unique h.tendsto_covariance h'.tendsto_covariance)

/-- Reindexing commutes with the continuum limit. -/
theorem comp (h : HasContinuumLimit F D) (e : κ → ι) :
    HasContinuumLimit (fun a => (F a).comp e) (D.comp e) where
  tendsto_value := by
    simp only [comp_value]
    exact ((continuous_pi fun k => continuous_apply (e k)).tendsto _).comp h.tendsto_value
  tendsto_covariance := by
    simp only [comp_covariance]
    exact ((continuous_id.matrix_submatrix e e).tendsto _).comp h.tendsto_covariance

end HasContinuumLimit

/-! ### Noise models -/

section NoiseModel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (D : EuclideanDataset ι)

/-- A random vector `X` on a probability space `(Ω, μ)` is a *noise model* for a dataset when its
components are square-integrable with the central values of the dataset as their means, and their
covariance matrix is the covariance of the dataset. -/
structure IsNoiseModel (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- The noise model lives on a probability space. -/
  isProbabilityMeasure : IsProbabilityMeasure μ
  /-- The components of the noise model are square-integrable. -/
  memLp : ∀ i, MemLp (X i) 2 μ
  /-- The means of the components of the noise model are the central values of the dataset. -/
  integral_eq_value : ∀ i, μ[X i] = D.value i
  /-- The covariance matrix of the noise model is the covariance of the dataset. -/
  covarianceMatrix_eq : covarianceMatrix X μ = D.covariance

/-- The dataset of a square-integrable random vector `X` on a probability space: its central
values are the means of the components of `X` and its covariance is the covariance matrix of
`X`. -/
noncomputable def ofRandomVector (X : ι → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) : EuclideanDataset ι where
  value i := μ[X i]
  covariance := covarianceMatrix X μ
  posSemidef_covariance := posSemidef_covarianceMatrix hX

/-- The central values of `ofRandomVector X μ hX` are the means of the components of `X`. -/
@[simp]
theorem ofRandomVector_value (X : ι → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector X μ hX).value = fun i => μ[X i] :=
  (rfl)

/-- The covariance of `ofRandomVector X μ hX` is the covariance matrix of `X`. -/
@[simp]
theorem ofRandomVector_covariance (X : ι → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector X μ hX).covariance = covarianceMatrix X μ :=
  (rfl)

/-- A random vector on a probability space is a noise model for the dataset built from it. -/
theorem isNoiseModel_ofRandomVector (X : ι → Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector X μ hX).IsNoiseModel X μ :=
  ⟨inferInstance, hX, fun i => (congrFun (ofRandomVector_value X μ hX) i).symm,
    (ofRandomVector_covariance X μ hX).symm⟩

variable {D} {X : ι → Ω → ℝ} {μ : Measure Ω}

/-- The reindexing of a noise model is a noise model of the reindexed dataset. -/
theorem IsNoiseModel.comp (h : D.IsNoiseModel X μ) (e : κ → ι) :
    (D.comp e).IsNoiseModel (X ∘ e) μ :=
  ⟨h.isProbabilityMeasure, fun k => h.memLp (e k), fun k => h.integral_eq_value (e k), by
    rw [covarianceMatrix_comp, h.covarianceMatrix_eq, comp_covariance]⟩

end NoiseModel

end Finite

/-! ### Covariance and variance of linear functionals -/

variable [Fintype ι] (D : EuclideanDataset ι)

open Classical in
/-- The covariance of the measured values of the linear functionals `c` and `c'` of the data: the
bilinear form `c ⬝ᵥ covariance *ᵥ c'` of the covariance matrix. Under any noise model `X` it is
the covariance of `c ⬝ᵥ X` and `c' ⬝ᵥ X` (`IsNoiseModel.covariance_dotProduct`). -/
noncomputable def covarianceForm : LinearMap.BilinForm ℝ (ι → ℝ) :=
  Matrix.toBilin' D.covariance

/-- The covariance of two functionals is the bilinear form of the covariance. -/
theorem covarianceForm_apply (c c' : ι → ℝ) :
    D.covarianceForm c c' = c ⬝ᵥ D.covariance *ᵥ c' := by
  classical
  exact Matrix.toBilin'_apply' _ _ _

/-- The covariance of two functionals is symmetric. -/
theorem covarianceForm_comm (c c' : ι → ℝ) : D.covarianceForm c c' = D.covarianceForm c' c := by
  simpa [covarianceForm_apply] using
    D.posSemidef_covariance.isHermitian.star_dotProduct_mulVec_comm c c'

open Classical in
/-- The variance of the measured value of the linear functional `c` of the data: the quadratic
form `c ⬝ᵥ covariance *ᵥ c` of the covariance matrix. Under any noise model `X` it is the
variance of `c ⬝ᵥ X` (`IsNoiseModel.variance_dotProduct`). -/
noncomputable def variance : QuadraticForm ℝ (ι → ℝ) :=
  Matrix.toQuadraticForm' D.covariance

/-- The variance of a functional is the quadratic form of the covariance. -/
theorem variance_apply (c : ι → ℝ) : D.variance c = c ⬝ᵥ D.covariance *ᵥ c := by
  classical
  exact Matrix.toQuadraticForm'_apply _ _

/-- The covariance of a functional with itself is its variance. -/
@[simp]
theorem covarianceForm_self (c : ι → ℝ) : D.covarianceForm c c = D.variance c := by
  rw [covarianceForm_apply, variance_apply]

/-- The polar form of the variance is twice the covariance. -/
theorem polar_variance (c c' : ι → ℝ) :
    QuadraticMap.polar D.variance c c' = 2 * D.covarianceForm c c' := by
  classical
  rw [variance, Matrix.toQuadraticForm', LinearMap.BilinMap.polar_toQuadraticMap,
    Matrix.toLinearMap₂'_apply', Matrix.toLinearMap₂'_apply', ← covarianceForm_apply,
    ← covarianceForm_apply, D.covarianceForm_comm c' c, two_mul]

/-- The variance of a sum of functionals. -/
theorem variance_add (c c' : ι → ℝ) :
    D.variance (c + c') = D.variance c + 2 * D.covarianceForm c c' + D.variance c' := by
  rw [← polar_variance, QuadraticMap.polar]
  ring

/-- The variance of a multiple of a functional. -/
theorem variance_smul (r : ℝ) (c : ι → ℝ) : D.variance (r • c) = r ^ 2 * D.variance c := by
  rw [QuadraticMap.map_smul, smul_eq_mul, sq]

/-- Variances are nonnegative. -/
@[simp]
theorem variance_nonneg (c : ι → ℝ) : 0 ≤ D.variance c := by
  simpa [variance_apply] using D.posSemidef_covariance.dotProduct_mulVec_nonneg c

/-- A functional has zero variance exactly when it lies in the kernel of the covariance. -/
theorem variance_eq_zero_iff {c : ι → ℝ} : D.variance c = 0 ↔ D.covariance *ᵥ c = 0 := by
  simpa [variance_apply] using D.posSemidef_covariance.dotProduct_mulVec_zero_iff

/-- The covariance of two functionals of a dataset reindexed along an injection is the covariance
of the functionals extended by zero to the whole dataset. -/
theorem comp_covarianceForm [Fintype κ] {e : κ → ι} (he : Function.Injective e) (c c' : κ → ℝ) :
    (D.comp e).covarianceForm c c' =
      D.covarianceForm (Function.extend e c 0) (Function.extend e c' 0) := by
  rw [covarianceForm_apply, covarianceForm_apply, he.extend_zero_dotProduct_mulVec_extend_zero he,
    comp_covariance]

/-- The variance of a functional of a dataset reindexed along an injection is the variance of the
functional extended by zero to the whole dataset. -/
theorem comp_variance [Fintype κ] {e : κ → ι} (he : Function.Injective e) (c : κ → ℝ) :
    (D.comp e).variance c = D.variance (Function.extend e c 0) := by
  simp only [← covarianceForm_self, D.comp_covarianceForm he]

/-- The *determined subspace* of a dataset: the linear functionals of the data with zero variance,
that is the kernel of the covariance. These are the functionals exactly determined by the data. -/
def determinedSubspace : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker D.covariance.mulVecLin

/-- A functional is in the determined subspace when the covariance annihilates it. -/
@[simp]
theorem mem_determinedSubspace {c : ι → ℝ} : c ∈ D.determinedSubspace ↔ D.covariance *ᵥ c = 0 :=
  by rw [determinedSubspace, LinearMap.mem_ker, Matrix.mulVecLin_apply]

/-- The determined subspace consists of the functionals of zero variance. -/
theorem mem_determinedSubspace_iff_variance_eq_zero {c : ι → ℝ} :
    c ∈ D.determinedSubspace ↔ D.variance c = 0 := by
  rw [mem_determinedSubspace, variance_eq_zero_iff]

/-- The covariance of an exactly determined functional with any functional is zero. -/
theorem covarianceForm_eq_zero_of_mem_determinedSubspace {c : ι → ℝ}
    (hc : c ∈ D.determinedSubspace) (c' : ι → ℝ) : D.covarianceForm c c' = 0 := by
  rw [covarianceForm_comm, covarianceForm_apply, D.mem_determinedSubspace.1 hc, dotProduct_zero]

/-- Adding an exactly determined functional to a functional does not change its variance. -/
theorem variance_add_of_mem_determinedSubspace {c : ι → ℝ} (hc : c ∈ D.determinedSubspace)
    (c' : ι → ℝ) : D.variance (c + c') = D.variance c' := by
  rw [variance_add, D.covarianceForm_eq_zero_of_mem_determinedSubspace hc,
    D.mem_determinedSubspace_iff_variance_eq_zero.1 hc]
  ring

variable {D} in
/-- The covariances of pairs of functionals converge along a continuum limit. -/
theorem HasContinuumLimit.tendsto_covarianceForm {F : ℝ → EuclideanDataset ι}
    (h : HasContinuumLimit F D) (c c' : ι → ℝ) :
    Tendsto (fun a => (F a).covarianceForm c c') (𝓝[>] 0) (𝓝 (D.covarianceForm c c')) := by
  have hb : Continuous fun S : Matrix ι ι ℝ => c ⬝ᵥ S *ᵥ c' :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  simp only [covarianceForm_apply]
  exact (hb.tendsto _).comp h.tendsto_covariance

variable {D} in
/-- Variances converge along a continuum limit. -/
theorem HasContinuumLimit.tendsto_variance {F : ℝ → EuclideanDataset ι}
    (h : HasContinuumLimit F D) (c : ι → ℝ) :
    Tendsto (fun a => (F a).variance c) (𝓝[>] 0) (𝓝 (D.variance c)) := by
  simpa only [covarianceForm_self] using h.tendsto_covarianceForm c c

variable {D} in
/-- The functionals of the central values converge along a continuum limit. -/
theorem HasContinuumLimit.tendsto_dotProduct_value {F : ℝ → EuclideanDataset ι}
    (h : HasContinuumLimit F D) (c : ι → ℝ) :
    Tendsto (fun a => c ⬝ᵥ (F a).value) (𝓝[>] 0) (𝓝 (c ⬝ᵥ D.value)) :=
  ((continuous_const.dotProduct continuous_id).tendsto _).comp h.tendsto_value

/-! ### Variances under a noise model -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsNoiseModel

variable {D} {X : ι → Ω → ℝ} {μ : Measure Ω}

/-- Under a noise model, the mean of a linear combination of the random data `X` is the
corresponding functional of the central values. -/
theorem integral_dotProduct (h : D.IsNoiseModel X μ) (c : ι → ℝ) :
    μ[fun ω => c ⬝ᵥ (X · ω)] = c ⬝ᵥ D.value := by
  have := h.isProbabilityMeasure
  simp only [dotProduct]
  rw [integral_finsetSum _ fun i _ => ((h.memLp i).integrable one_le_two).const_mul (c i)]
  simp [integral_const_mul, h.integral_eq_value]

/-- Under a noise model, the covariance of two functionals of the data is the covariance of the
corresponding linear combinations of the random data `X`. -/
theorem covariance_dotProduct (h : D.IsNoiseModel X μ) (c c' : ι → ℝ) :
    cov[fun ω => c ⬝ᵥ (X · ω), fun ω => c' ⬝ᵥ (X · ω); μ] = D.covarianceForm c c' := by
  have := h.isProbabilityMeasure
  rw [covariance_dotProduct_dotProduct h.memLp, h.covarianceMatrix_eq, covarianceForm_apply]

/-- Under a noise model, the variance of a functional of the data is the variance of the
corresponding linear combination of the random data `X`. -/
theorem variance_dotProduct (h : D.IsNoiseModel X μ) (c : ι → ℝ) :
    Var[fun ω => c ⬝ᵥ (X · ω); μ] = D.variance c := by
  rw [← covariance_self (memLp_dotProduct h.memLp c).aemeasurable, h.covariance_dotProduct,
    covarianceForm_self]

/-- Under a noise model, a functional lies in the determined subspace exactly when the
corresponding linear combination of the random data `X` is almost surely equal to the functional
of the central values. -/
theorem ae_eq_dotProduct_value_iff_mem_determinedSubspace (h : D.IsNoiseModel X μ)
    (c : ι → ℝ) :
    ((fun ω => c ⬝ᵥ (X · ω)) =ᵐ[μ] fun _ => c ⬝ᵥ D.value) ↔ c ∈ D.determinedSubspace := by
  have := h.isProbabilityMeasure
  rw [← h.integral_dotProduct, ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero h.memLp,
    h.covarianceMatrix_eq, mem_determinedSubspace]

end IsNoiseModel

end EuclideanDataset

end Lattice
end QFT
end EpsilonEridani
