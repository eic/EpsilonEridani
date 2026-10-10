/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.DataStructures.Matrix.Extend
public import EpsilonEridani.Mathematics.Probability.Moments.CovarianceMatrix
public import Mathlib.Analysis.Matrix.Order
/-!

# Euclidean datasets and their noise model

A Euclidean calculation returns finitely many renormalised matrix elements together with their
covariance. This file axiomatises that output as data, so that statements about what a Euclidean
calculation determines can be made about it without any lattice construction.

* A `EuclideanDataset ι` is a family of real central values `value : ι → ℝ` indexed by a type `ι`
  labelling the observations, with a positive semidefinite covariance matrix. The label type is
  finite in every statement that forms a variance.
* A linear functional of the data is a coefficient vector `c : ι → ℝ`. The covariance of two
  functionals is the bilinear form `EuclideanDataset.covarianceForm`, the variance of one is the
  quadratic form `EuclideanDataset.variance`, and the functionals of variance zero form the
  *determined subspace* `EuclideanDataset.determinedSubspace`, the kernel of the covariance.
* `EuclideanDataset.IsNoiseModel` says that a random vector has the central values of a dataset
  as its means and the covariance of the dataset as its covariance matrix. For a noise model the
  covariance of two functionals is the covariance of the corresponding random variables, and a
  functional lies in the determined subspace exactly when the random variable is almost surely
  equal to the functional of the central values: the exactly determined functionals are those
  that carry no noise.
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
* `EuclideanDataset.hasContinuumLimit_ofTendsto`: if the central values and covariances of a family
  converge, the limit covariance is again positive semidefinite, so the limits form a dataset
  `EuclideanDataset.ofTendsto`, the continuum limit of the family; it is unique
  (`EuclideanDataset.HasContinuumLimit.unique`), and variances converge with it.

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

/-- A *Euclidean dataset*: renormalised matrix elements `value i`, one for each observation label
`i : ι`, together with their covariance matrix, which is positive semidefinite. -/
@[ext]
structure EuclideanDataset (ι : Type*) where
  /-- The central value of each observation. -/
  value : ι → ℝ
  /-- The covariance matrix of the observations. -/
  covariance : Matrix ι ι ℝ
  /-- The covariance matrix is positive semidefinite. -/
  posSemidef_covariance : covariance.PosSemidef

namespace EuclideanDataset

variable {ι κ ν : Type*}

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

variable {F : ℝ → EuclideanDataset ι} {S : Matrix ι ι ℝ}

/-- The dataset with central values `v` whose covariance is the limit `S` of the covariances of a
family of datasets as `a → 0⁺`; the limit of positive semidefinite matrices is again positive
semidefinite. When the central values of the family converge to `v`, this is the continuum limit
of the family (`hasContinuumLimit_ofTendsto`). -/
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

/-- The covariance of `ofTendsto v hS` is the limit `S` of the covariances. -/
@[simp]
theorem ofTendsto_covariance (v : ι → ℝ)
    (hS : Tendsto (fun a => (F a).covariance) (𝓝[>] 0) (𝓝 S)) :
    (ofTendsto v hS).covariance = S :=
  (rfl)

/-- If the central values and the covariances of a family of datasets converge as `a → 0⁺`, then
the limits form the continuum limit of the family. -/
theorem hasContinuumLimit_ofTendsto {v : ι → ℝ}
    (hv : Tendsto (fun a => (F a).value) (𝓝[>] 0) (𝓝 v))
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

/-- A random vector `X` on `(Ω, μ)` is a *noise model* for a dataset when its components are
square-integrable with the central values of the dataset as their means, and their covariance
matrix is the covariance of the dataset. -/
structure IsNoiseModel (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- The components of the noise model are square-integrable. -/
  memLp : ∀ i, MemLp (X i) 2 μ
  /-- The means of the components of the noise model are the central values of the dataset. -/
  integral_eq_value : ∀ i, μ[X i] = D.value i
  /-- The covariance matrix of the noise model is the covariance of the dataset. -/
  covarianceMatrix_eq : covarianceMatrix X μ = D.covariance

/-- The dataset of a square-integrable random vector `X`: its central values are the means of the
components of `X` and its covariance is the covariance matrix of `X`. -/
noncomputable def ofRandomVector (X : ι → Ω → ℝ) (μ : Measure Ω) [Finite ι] [IsFiniteMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) : EuclideanDataset ι where
  value i := μ[X i]
  covariance := covarianceMatrix X μ
  posSemidef_covariance := posSemidef_covarianceMatrix hX

/-- The central values of `ofRandomVector X μ hX` are the means of the components of `X`. -/
@[simp]
theorem ofRandomVector_value (X : ι → Ω → ℝ) (μ : Measure Ω) [Finite ι] [IsFiniteMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector X μ hX).value = fun i => μ[X i] :=
  (rfl)

/-- The covariance of `ofRandomVector X μ hX` is the covariance matrix of `X`. -/
@[simp]
theorem ofRandomVector_covariance (X : ι → Ω → ℝ) (μ : Measure Ω) [Finite ι] [IsFiniteMeasure μ]
    (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector X μ hX).covariance = covarianceMatrix X μ :=
  (rfl)

/-- A random vector is a noise model for the dataset built from it. -/
theorem isNoiseModel_ofRandomVector (X : ι → Ω → ℝ) (μ : Measure Ω) [Finite ι]
    [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector X μ hX).IsNoiseModel X μ :=
  ⟨hX, fun i => (congrFun (ofRandomVector_value X μ hX) i).symm,
    (ofRandomVector_covariance X μ hX).symm⟩

variable {D} {X : ι → Ω → ℝ} {μ : Measure Ω}

/-- The reindexing of a noise model is a noise model of the reindexed dataset. -/
theorem IsNoiseModel.comp (h : D.IsNoiseModel X μ) (e : κ → ι) :
    (D.comp e).IsNoiseModel (X ∘ e) μ :=
  ⟨fun k => h.memLp (e k), fun k => h.integral_eq_value (e k), by
    rw [covarianceMatrix_comp, h.covarianceMatrix_eq, comp_covariance]⟩

end NoiseModel

/-! ### Variance of a linear functional -/

variable [Fintype ι] (D : EuclideanDataset ι)

/-- The covariance of the linear functionals `c ⬝ᵥ value` and `c' ⬝ᵥ value` of the data: the
bilinear form `c ⬝ᵥ covariance *ᵥ c'`. -/
def covarianceForm (c c' : ι → ℝ) : ℝ :=
  c ⬝ᵥ D.covariance *ᵥ c'

/-- The covariance of two functionals is the bilinear form of the covariance. -/
theorem covarianceForm_def (c c' : ι → ℝ) : D.covarianceForm c c' = c ⬝ᵥ D.covariance *ᵥ c' :=
  (rfl)

/-- The covariance of two functionals is symmetric. -/
theorem covarianceForm_comm (c c' : ι → ℝ) : D.covarianceForm c c' = D.covarianceForm c' c := by
  simpa [covarianceForm_def] using
    D.posSemidef_covariance.isHermitian.star_dotProduct_mulVec_comm c c'

/-- The variance of the linear functional `c ⬝ᵥ value` of the data: the quadratic form
`c ⬝ᵥ covariance *ᵥ c`. -/
def variance (c : ι → ℝ) : ℝ :=
  D.covarianceForm c c

/-- The variance of a functional is the quadratic form of the covariance. -/
theorem variance_def (c : ι → ℝ) : D.variance c = c ⬝ᵥ D.covariance *ᵥ c :=
  (rfl)

/-- The covariance of a functional with itself is its variance. -/
@[simp]
theorem covarianceForm_self (c : ι → ℝ) : D.covarianceForm c c = D.variance c :=
  (rfl)

/-- The variance of a sum of functionals. -/
theorem variance_add (c c' : ι → ℝ) :
    D.variance (c + c') = D.variance c + 2 * D.covarianceForm c c' + D.variance c' := by
  have := D.covarianceForm_comm c' c
  simp only [variance_def, covarianceForm_def] at this ⊢
  simp only [mulVec_add, dotProduct_add, add_dotProduct, this]
  ring

/-- Variances are nonnegative. -/
theorem variance_nonneg (c : ι → ℝ) : 0 ≤ D.variance c := by
  simpa [variance_def] using D.posSemidef_covariance.dotProduct_mulVec_nonneg c

/-- A functional has zero variance exactly when it lies in the kernel of the covariance. -/
theorem variance_eq_zero_iff {c : ι → ℝ} : D.variance c = 0 ↔ D.covariance *ᵥ c = 0 := by
  simpa [variance_def] using D.posSemidef_covariance.dotProduct_mulVec_zero_iff

/-- The variance of a functional of a dataset reindexed along an injection is the variance of the
functional extended by zero to the whole dataset. -/
theorem comp_variance [Fintype κ] {e : κ → ι} (he : Function.Injective e) (c : κ → ℝ) :
    (D.comp e).variance c = D.variance (Function.extend e c 0) := by
  rw [variance_def, variance_def, Matrix.extend_dotProduct_mulVec_extend he, comp_covariance]

/-- The *determined subspace* of a dataset: the linear functionals of the data with zero variance,
that is the kernel of the covariance. These are the functionals exactly determined by the data. -/
def determinedSubspace : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker D.covariance.mulVecLin

/-- A functional is in the determined subspace when the covariance annihilates it. -/
@[simp]
theorem mem_determinedSubspace {c : ι → ℝ} : c ∈ D.determinedSubspace ↔ D.covariance *ᵥ c = 0 :=
  LinearMap.mem_ker

/-- The determined subspace consists of the functionals of zero variance. -/
theorem mem_determinedSubspace_iff_variance_eq_zero {c : ι → ℝ} :
    c ∈ D.determinedSubspace ↔ D.variance c = 0 := by
  rw [mem_determinedSubspace, variance_eq_zero_iff]

/-- Adding an exactly determined functional to a functional does not change its variance. -/
theorem variance_add_of_mem_determinedSubspace {c : ι → ℝ} (hc : c ∈ D.determinedSubspace)
    (c' : ι → ℝ) : D.variance (c + c') = D.variance c' := by
  have hc' : D.covarianceForm c c' = 0 := by
    rw [covarianceForm_comm, covarianceForm_def, D.mem_determinedSubspace.1 hc, dotProduct_zero]
  rw [variance_add, hc', D.mem_determinedSubspace_iff_variance_eq_zero.1 hc]
  ring

variable {D} in
/-- Variances converge along a continuum limit. -/
theorem HasContinuumLimit.tendsto_variance {F : ℝ → EuclideanDataset ι}
    (h : HasContinuumLimit F D) (c : ι → ℝ) :
    Tendsto (fun a => (F a).variance c) (𝓝[>] 0) (𝓝 (D.variance c)) := by
  have hq : Continuous fun S : Matrix ι ι ℝ => c ⬝ᵥ S *ᵥ c :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  simp only [variance_def]
  exact (hq.tendsto _).comp h.tendsto_covariance

/-! ### Variances under a noise model -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

namespace IsNoiseModel

variable {D} {X : ι → Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Under a noise model, the mean of a linear combination of the noise is the corresponding
functional of the central values. -/
theorem integral_dotProduct (h : D.IsNoiseModel X μ) (c : ι → ℝ) :
    μ[fun ω => c ⬝ᵥ (X · ω)] = c ⬝ᵥ D.value := by
  simp only [dotProduct]
  rw [integral_finsetSum _ fun i _ => ((h.memLp i).integrable one_le_two).const_mul (c i)]
  simp [integral_const_mul, h.integral_eq_value]

/-- Under a noise model, the covariance of two functionals of the data is the covariance of the
corresponding linear combinations of the noise. -/
theorem covariance_dotProduct (h : D.IsNoiseModel X μ) (c c' : ι → ℝ) :
    cov[fun ω => c ⬝ᵥ (X · ω), fun ω => c' ⬝ᵥ (X · ω); μ] = D.covarianceForm c c' := by
  rw [covariance_dotProduct_dotProduct h.memLp, h.covarianceMatrix_eq, covarianceForm_def]

/-- Under a noise model, the variance of a functional of the data is the variance of the
corresponding linear combination of the noise. -/
theorem variance_dotProduct (h : D.IsNoiseModel X μ) (c : ι → ℝ) :
    Var[fun ω => c ⬝ᵥ (X · ω); μ] = D.variance c := by
  rw [← covariance_self (memLp_dotProduct h.memLp c).aemeasurable, h.covariance_dotProduct,
    covarianceForm_self]

/-- Under a noise model, a functional lies in the determined subspace exactly when the
corresponding linear combination of the noise is almost surely equal to the functional of the
central values. -/
theorem ae_eq_dotProduct_value_iff_mem_determinedSubspace (h : D.IsNoiseModel X μ)
    (c : ι → ℝ) :
    ((fun ω => c ⬝ᵥ (X · ω)) =ᵐ[μ] fun _ => c ⬝ᵥ D.value) ↔ c ∈ D.determinedSubspace := by
  rw [← h.integral_dotProduct, ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero h.memLp,
    h.covarianceMatrix_eq, mem_determinedSubspace]

end IsNoiseModel

end EuclideanDataset

end Lattice
end QFT
end EpsilonEridani
