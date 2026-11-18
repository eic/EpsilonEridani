/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The second moment of the standard Gaussian

Mathlib's standard Gaussian measure `stdGaussian E` on a finite-dimensional real inner product
space has independent standard normal coordinates in any orthonormal basis. This file computes its
second moment, `∫ ‖x‖² ∂(stdGaussian E) = dim E` (`ProbabilityTheory.integral_norm_sq_stdGaussian`),
so that its image under `x ↦ σ • x` has root-mean-square norm `|σ| √(dim E)`.
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The second moment of the standard Gaussian is the dimension: `∫ ‖x‖² ∂(stdGaussian E) = dim E`.
-/
theorem integral_norm_sq_stdGaussian :
    ∫ x, ‖x‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  -- each coordinate `⟪x, b i⟫` is a centred random variable of variance `‖b i‖² = 1`
  have hL : ∀ i, ∫ x, ⟪x, b i⟫ ^ 2 ∂(stdGaussian E) = 1 := fun i ↦ by
    have hv := variance_dual_stdGaussian (innerSL ℝ (b i))
    rw [variance_of_integral_eq_zero (by fun_prop) (integral_strongDual_stdGaussian _)] at hv
    simpa [b.norm_eq_one, real_inner_comm] using hv
  have hI : ∀ i, Integrable (fun x : E ↦ ⟪x, b i⟫ ^ 2) (stdGaussian E) := fun i ↦ by
    have := (innerSL ℝ (b i)).comp_memLp' (IsGaussian.memLp_two_id (μ := stdGaussian E))
    simpa [Function.comp_def, real_inner_comm] using this.integrable_sq
  simp_rw [← b.sum_sq_inner_left]
  rw [integral_finsetSum _ fun i _ ↦ hI i]
  simp [hL]

end ProbabilityTheory
