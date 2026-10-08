/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

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
* A linear functional of the data is a coefficient vector `c : ι → ℝ`. Its variance is the
  quadratic form `EuclideanDataset.variance`, and the functionals of variance zero form the
  *exact subspace* `EuclideanDataset.exactSubspace`, the kernel of the covariance.
* `EuclideanDataset.IsNoiseModel` says that a random vector realises the covariance of a dataset.
  For a noise model the variance of a functional is the variance of the corresponding random
  variable, and a functional lies in the exact subspace exactly when the random variable is
  almost surely constant: the exactly determined functionals are those that carry no noise.
* `EuclideanDataset.HasContinuumLimit` says that a family of datasets indexed by the lattice
  spacing `a` converges as `a → 0⁺`. It is a property of a family, never of one dataset.

## Main results

* `EuclideanDataset.restrict`: the subfamily along any reindexing is a dataset, its covariance
  being the corresponding submatrix of the original one.
* `EuclideanDataset.mem_exactSubspace_iff_variance_eq_zero`: the functionals of variance zero are
  the kernel of the covariance; adding one to a functional does not change its variance
  (`EuclideanDataset.variance_add_of_mem_exactSubspace`).
* `EuclideanDataset.IsNoiseModel.ae_eq_integral_iff_mem_exactSubspace`: under a noise model,
  `c ⬝ᵥ X` is almost surely its mean exactly when `c` is in the exact subspace.
* `EuclideanDataset.exists_hasContinuumLimit`: if the central values and covariances of a family
  converge, the limit covariance is again positive semidefinite, so the limit is a dataset; it is
  unique (`EuclideanDataset.HasContinuumLimit.unique`), and variances converge with it.

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

open MeasureTheory ProbabilityTheory Matrix Filter Topology

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

/-! ### Subfamilies -/

/-- The subfamily of a dataset along a reindexing `e : κ → ι`: the central values `value ∘ e` with
the covariance submatrix along `e`. -/
def restrict (D : EuclideanDataset ι) (e : κ → ι) : EuclideanDataset κ where
  value := D.value ∘ e
  covariance := D.covariance.submatrix e e
  posSemidef_covariance := D.posSemidef_covariance.submatrix e

/-- The central values of a subfamily are the central values along the reindexing. -/
@[simp]
theorem restrict_value (D : EuclideanDataset ι) (e : κ → ι) : (D.restrict e).value = D.value ∘ e :=
  (rfl)

/-- The covariance of a subfamily is the covariance submatrix along the reindexing. -/
@[simp]
theorem restrict_covariance (D : EuclideanDataset ι) (e : κ → ι) :
    (D.restrict e).covariance = D.covariance.submatrix e e :=
  (rfl)

/-- Restricting along the identity does nothing. -/
@[simp]
theorem restrict_id (D : EuclideanDataset ι) : D.restrict id = D :=
  (rfl)

/-- Restricting twice is restricting along the composite. -/
@[simp]
theorem restrict_restrict (D : EuclideanDataset ι) (e : κ → ι) (e' : ν → κ) :
    (D.restrict e).restrict e' = D.restrict (e ∘ e') :=
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

/-- If the central values and the covariances of a family of datasets converge as `a → 0⁺`, then
the limit covariance is positive semidefinite, so the limits form a dataset, the continuum limit
of the family. -/
theorem exists_hasContinuumLimit {F : ℝ → EuclideanDataset ι} {v : ι → ℝ} {S : Matrix ι ι ℝ}
    (hv : Tendsto (fun a => (F a).value) (𝓝[>] 0) (𝓝 v))
    (hS : Tendsto (fun a => (F a).covariance) (𝓝[>] 0) (𝓝 S)) :
    ∃ D : EuclideanDataset ι, D.value = v ∧ D.covariance = S ∧ HasContinuumLimit F D :=
  ⟨⟨v, S, posSemidef_is_closed.mem_of_tendsto hS
    (.of_forall fun a => (F a).posSemidef_covariance)⟩, rfl, rfl, ⟨hv, hS⟩⟩

namespace HasContinuumLimit

variable {F : ℝ → EuclideanDataset ι} {D D' : EuclideanDataset ι}

/-- The continuum limit of a family of datasets is unique. -/
theorem unique (h : HasContinuumLimit F D) (h' : HasContinuumLimit F D') : D = D' :=
  EuclideanDataset.ext (tendsto_nhds_unique h.tendsto_value h'.tendsto_value)
    (tendsto_nhds_unique h.tendsto_covariance h'.tendsto_covariance)

/-- Taking a subfamily commutes with the continuum limit. -/
theorem restrict (h : HasContinuumLimit F D) (e : κ → ι) :
    HasContinuumLimit (fun a => (F a).restrict e) (D.restrict e) where
  tendsto_value := by
    simp only [restrict_value]
    exact ((continuous_pi fun k => continuous_apply (e k)).tendsto _).comp h.tendsto_value
  tendsto_covariance := by
    simp only [restrict_covariance]
    exact ((continuous_id.matrix_submatrix e e).tendsto _).comp h.tendsto_covariance

end HasContinuumLimit

/-! ### Noise models -/

section NoiseModel

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (D : EuclideanDataset ι)

/-- A random vector `X` on `(Ω, μ)` is a *noise model* for a dataset when its components are
square-integrable and their covariance matrix is the covariance of the dataset. -/
structure IsNoiseModel (X : ι → Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- The components of the noise model are square-integrable. -/
  memLp : ∀ i, MemLp (X i) 2 μ
  /-- The covariance matrix of the noise model is the covariance of the dataset. -/
  covarianceMatrix_eq : covarianceMatrix X μ = D.covariance

/-- The dataset with central values `value` whose covariance is that of a square-integrable
random vector `X`. -/
noncomputable def ofRandomVector (value : ι → ℝ) (X : ι → Ω → ℝ) (μ : Measure Ω)
    [Finite ι] [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) : EuclideanDataset ι where
  value := value
  covariance := covarianceMatrix X μ
  posSemidef_covariance := posSemidef_covarianceMatrix hX

/-- The central values of `ofRandomVector value X μ hX` are `value`. -/
@[simp]
theorem ofRandomVector_value (value : ι → ℝ) (X : ι → Ω → ℝ) (μ : Measure Ω)
    [Finite ι] [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector value X μ hX).value = value :=
  (rfl)

/-- The covariance of `ofRandomVector value X μ hX` is the covariance matrix of `X`. -/
@[simp]
theorem ofRandomVector_covariance (value : ι → ℝ) (X : ι → Ω → ℝ) (μ : Measure Ω)
    [Finite ι] [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector value X μ hX).covariance = covarianceMatrix X μ :=
  (rfl)

/-- A random vector is a noise model for the dataset built from its covariance. -/
theorem isNoiseModel_ofRandomVector (value : ι → ℝ) (X : ι → Ω → ℝ) (μ : Measure Ω)
    [Finite ι] [IsFiniteMeasure μ] (hX : ∀ i, MemLp (X i) 2 μ) :
    (ofRandomVector value X μ hX).IsNoiseModel X μ :=
  ⟨hX, (ofRandomVector_covariance value X μ hX).symm⟩

variable {D} {X : ι → Ω → ℝ} {μ : Measure Ω}

/-- The restriction of a noise model along a reindexing is a noise model of the subfamily. -/
theorem IsNoiseModel.restrict (h : D.IsNoiseModel X μ) (e : κ → ι) :
    (D.restrict e).IsNoiseModel (X ∘ e) μ :=
  ⟨fun k => h.memLp (e k), by
    rw [covarianceMatrix_comp, h.covarianceMatrix_eq, restrict_covariance]⟩

end NoiseModel

/-! ### Variance of a linear functional -/

variable [Fintype ι] (D : EuclideanDataset ι)

/-- The variance of the linear functional `c ⬝ᵥ value` of the data: the quadratic form
`c ⬝ᵥ covariance *ᵥ c`. -/
def variance (c : ι → ℝ) : ℝ :=
  c ⬝ᵥ D.covariance *ᵥ c

/-- The variance of a functional is the quadratic form of the covariance. -/
theorem variance_def (c : ι → ℝ) : D.variance c = c ⬝ᵥ D.covariance *ᵥ c :=
  (rfl)

/-- Variances are nonnegative. -/
theorem variance_nonneg (c : ι → ℝ) : 0 ≤ D.variance c := by
  simpa [variance_def] using D.posSemidef_covariance.dotProduct_mulVec_nonneg c

/-- A functional has zero variance exactly when it lies in the kernel of the covariance. -/
theorem variance_eq_zero_iff {c : ι → ℝ} : D.variance c = 0 ↔ D.covariance *ᵥ c = 0 := by
  simpa [variance_def] using D.posSemidef_covariance.dotProduct_mulVec_zero_iff

/-- The variance of a functional of a subfamily along an injective reindexing is the variance of
the functional extended by zero to the whole family. -/
theorem variance_restrict [Fintype κ] {e : κ → ι} (he : Function.Injective e) (c : κ → ℝ) :
    (D.restrict e).variance c = D.variance (Function.extend e c 0) := by
  -- Pairing with a functional extended by zero only sees the entries on the range of `e`.
  have key (f : ι → ℝ) : Function.extend e c 0 ⬝ᵥ f = c ⬝ᵥ (f ∘ e) :=
    (Fintype.sum_of_injective e he _ _
      (fun i hi => by simp [Function.extend_apply' _ _ _ (by simpa using hi)])
      (fun k => by simp [he.extend_apply])).symm
  rw [variance_def, variance_def, key, restrict_covariance]
  congr 1
  ext k
  simp only [Function.comp_apply, mulVec, dotProduct_comm _ (Function.extend e c 0), key]
  exact dotProduct_comm _ _

/-- The *exact subspace* of a dataset: the linear functionals of the data with zero variance,
that is the kernel of the covariance. -/
def exactSubspace : Submodule ℝ (ι → ℝ) :=
  LinearMap.ker D.covariance.mulVecLin

/-- A functional is in the exact subspace when the covariance annihilates it. -/
@[simp]
theorem mem_exactSubspace {c : ι → ℝ} : c ∈ D.exactSubspace ↔ D.covariance *ᵥ c = 0 :=
  LinearMap.mem_ker

/-- The exact subspace consists of the functionals of zero variance. -/
theorem mem_exactSubspace_iff_variance_eq_zero {c : ι → ℝ} :
    c ∈ D.exactSubspace ↔ D.variance c = 0 := by
  rw [mem_exactSubspace, variance_eq_zero_iff]

/-- Adding an exactly determined functional to a functional does not change its variance. -/
theorem variance_add_of_mem_exactSubspace {c : ι → ℝ} (hc : c ∈ D.exactSubspace)
    (c' : ι → ℝ) : D.variance (c + c') = D.variance c' := by
  rw [mem_exactSubspace] at hc
  have hc' : c ⬝ᵥ D.covariance *ᵥ c' = 0 := by
    simpa [hc] using (D.posSemidef_covariance.isHermitian.star_dotProduct_mulVec_comm c' c).symm
  simp [variance_def, mulVec_add, add_dotProduct, hc, hc']

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

/-- Under a noise model, the variance of a functional of the data is the variance of the
corresponding linear combination of the noise. -/
theorem variance_dotProduct (h : D.IsNoiseModel X μ) (c : ι → ℝ) :
    Var[fun ω => c ⬝ᵥ (X · ω); μ] = D.variance c := by
  rw [EpsilonEridani.variance_dotProduct h.memLp, h.covarianceMatrix_eq, variance_def]

/-- Under a noise model, a functional lies in the exact subspace exactly when the corresponding
linear combination of the noise is almost surely equal to its mean. -/
theorem ae_eq_integral_iff_mem_exactSubspace (h : D.IsNoiseModel X μ) (c : ι → ℝ) :
    ((fun ω => c ⬝ᵥ (X · ω)) =ᵐ[μ] fun _ => μ[fun ω => c ⬝ᵥ (X · ω)]) ↔
      c ∈ D.exactSubspace := by
  rw [ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero h.memLp, h.covarianceMatrix_eq,
    mem_exactSubspace]

end IsNoiseModel

end EuclideanDataset

end Lattice
end QFT
end EpsilonEridani
