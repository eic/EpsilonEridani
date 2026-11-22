/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# The second moment and the characteristic function of the standard Gaussian

Mathlib's standard Gaussian measure `stdGaussian E` on a finite-dimensional real inner product
space has independent standard normal coordinates in any orthonormal basis. This file computes
its second moment, `∫ ‖x‖² ∂(stdGaussian E) = dim E`
(`ProbabilityTheory.integral_norm_sq_stdGaussian`), and the same moment for its image under
`x ↦ σ • x`, the isotropic Gaussian of width `σ`,
`∫ ‖x‖² ∂((stdGaussian E).map (σ • ·)) = σ² dim E`
(`ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian`), whose root-mean-square norm is
`|σ| √(dim E)`.

The characteristic function of the image under `x ↦ σ • x` — in physics the form factor of the
isotropic Gaussian charge distribution of width `σ` — decays as a Gaussian in the momentum:
`charFun ((stdGaussian E).map (σ • ·)) t = exp (-σ² ‖t‖² / 2)`
(`ProbabilityTheory.charFun_map_smul_stdGaussian`), with squared modulus
`exp (-σ² ‖t‖²)` (`ProbabilityTheory.norm_sq_charFun_map_smul_stdGaussian`).
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The second moment of the standard Gaussian is the dimension: `∫ ‖x‖² ∂(stdGaussian E) = dim E`.
-/
@[simp]
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

/-- The second moment of the standard Gaussian dilated by `σ` is `σ²` times the dimension:
`∫ ‖x‖² ∂((stdGaussian E).map (σ • ·)) = σ² dim E`. -/
@[simp]
theorem integral_norm_sq_map_smul_stdGaussian (σ : ℝ) :
    ∫ x, ‖x‖ ^ 2 ∂((stdGaussian E).map (σ • ·)) = σ ^ 2 * Module.finrank ℝ E := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, integral_norm_sq_stdGaussian]

/-- The characteristic function of the standard Gaussian dilated by `σ` — in physics the form
factor of the isotropic Gaussian charge distribution of width `σ` — is the exponential of the
real number `-σ² ‖t‖² / 2`. -/
theorem charFun_map_smul_stdGaussian (σ : ℝ) (t : E) :
    charFun ((stdGaussian E).map (σ • ·)) t = Complex.exp (-(σ ^ 2 * ‖t‖ ^ 2) / 2 : ℝ) := by
  rw [charFun_map_smul, charFun_stdGaussian, ← Complex.ofReal_pow, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  push_cast
  ring_nf

/-- The squared modulus of the characteristic function of the standard Gaussian dilated by `σ`
decays as `exp (-σ² ‖t‖²)`; in physics this is the factor by which the coherent rate of the
isotropic Gaussian charge distribution of width `σ` is suppressed at momentum `t`. -/
theorem norm_sq_charFun_map_smul_stdGaussian (σ : ℝ) (t : E) :
    ‖charFun ((stdGaussian E).map (σ • ·)) t‖ ^ 2 = Real.exp (-(σ ^ 2 * ‖t‖ ^ 2)) := by
  rw [charFun_map_smul_stdGaussian, Complex.norm_exp_ofReal, ← Real.exp_nat_mul]
  push_cast
  ring_nf

end ProbabilityTheory
