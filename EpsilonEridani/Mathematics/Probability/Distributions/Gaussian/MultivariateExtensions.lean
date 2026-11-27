/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import EpsilonEridani.Mathematics.Probability.Distributions.Gaussian.BasicExtensions
public import EpsilonEridani.Mathematics.MeasureTheory.Integral.Bochner.BasicExtensions

/-!
# The second moment and the characteristic function of the standard Gaussian

Mathlib's standard Gaussian measure `stdGaussian E` on a finite-dimensional real inner product
space has independent standard normal coordinates in any orthonormal basis. This file computes
its second moment, `∫ ‖x‖² ∂(stdGaussian E) = dim E`
(`ProbabilityTheory.integral_norm_sq_stdGaussian`), as the sum over an orthonormal basis of the
second moments `∫ ⟪x, v⟫² ∂(stdGaussian E) = ‖v‖²` of the coordinates
(`ProbabilityTheory.integral_inner_sq_stdGaussian`), themselves the case `L = innerSL ℝ v` of the
second moment `∫ (L x)² ∂(stdGaussian E) = ‖L‖²` of a continuous linear functional `L`
(`ProbabilityTheory.integral_dual_sq_stdGaussian`), and the same moment for its image under
`x ↦ σ • x`, the isotropic Gaussian of width `σ`,
`∫ ‖x‖² ∂((stdGaussian E).map (σ • ·)) = σ² dim E`
(`ProbabilityTheory.integral_norm_sq_map_smul_stdGaussian`), whose root-mean-square norm is
`|σ| √(dim E)`; this dilated moment is the general dilation of a moment of the norm,
`MeasureTheory.integral_norm_pow_map_smul`, applied to the undilated one.

The characteristic function of the image under `x ↦ σ • x` — in physics the form factor of the
isotropic Gaussian charge distribution of width `σ` — decays as a Gaussian in the momentum:
`charFun ((stdGaussian E).map (σ • ·)) t = exp (-σ² ‖t‖² / 2)`
(`ProbabilityTheory.charFun_map_smul_stdGaussian`), with modulus `exp (-σ² ‖t‖² / 2)`
(`ProbabilityTheory.norm_charFun_map_smul_stdGaussian`), which departs from one by at most
`σ² ‖t‖² / 2` (`ProbabilityTheory.one_sub_norm_charFun_map_smul_stdGaussian_le`), and squared
modulus `exp (-σ² ‖t‖²)` (`ProbabilityTheory.norm_sq_charFun_map_smul_stdGaussian`).
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A continuous linear functional `L` of the standard Gaussian has second moment `‖L‖²`:
`∫ (L x)² ∂(stdGaussian E) = ‖L‖²`. -/
@[simp]
theorem integral_dual_sq_stdGaussian (L : StrongDual ℝ E) :
    ∫ x, L x ^ 2 ∂(stdGaussian E) = ‖L‖ ^ 2 := by
  -- `L` is a centred random variable of variance `‖L‖²`
  rw [← variance_of_integral_eq_zero (by fun_prop) (integral_strongDual_stdGaussian L),
    variance_dual_stdGaussian]

/-- The coordinate `⟪x, v⟫` of the standard Gaussian has second moment `‖v‖²`:
`∫ ⟪x, v⟫² ∂(stdGaussian E) = ‖v‖²`. -/
@[simp]
theorem integral_inner_sq_stdGaussian (v : E) :
    ∫ x, ⟪x, v⟫ ^ 2 ∂(stdGaussian E) = ‖v‖ ^ 2 := by
  -- the coordinate is the continuous linear functional `innerSL ℝ v`, up to symmetry
  simpa [real_inner_comm] using integral_dual_sq_stdGaussian (innerSL ℝ v)

/-- The second moment of the standard Gaussian is the dimension: `∫ ‖x‖² ∂(stdGaussian E) = dim E`.
-/
@[simp]
theorem integral_norm_sq_stdGaussian :
    ∫ x, ‖x‖ ^ 2 ∂(stdGaussian E) = Module.finrank ℝ E := by
  let b := stdOrthonormalBasis ℝ E
  simp_rw [← b.sum_sq_inner_left]
  rw [integral_finsetSum _ fun i _ ↦ IsGaussian.integrable_inner_sq _ (b i)]
  simp [b.norm_eq_one]

/-- The second moment of the standard Gaussian dilated by `σ` is `σ²` times the dimension:
`∫ ‖x‖² ∂((stdGaussian E).map (σ • ·)) = σ² dim E`. -/
@[simp]
theorem integral_norm_sq_map_smul_stdGaussian (σ : ℝ) :
    ∫ x, ‖x‖ ^ 2 ∂((stdGaussian E).map (σ • ·)) = σ ^ 2 * Module.finrank ℝ E := by
  rw [integral_norm_pow_map_smul, integral_norm_sq_stdGaussian, Real.norm_eq_abs, sq_abs]

/-- The characteristic function of the standard Gaussian dilated by `σ` — in physics the form
factor of the isotropic Gaussian charge distribution of width `σ` — is the exponential of the
real number `-σ² ‖t‖² / 2`. -/
theorem charFun_map_smul_stdGaussian (σ : ℝ) (t : E) :
    charFun ((stdGaussian E).map (σ • ·)) t = Complex.exp (-(σ ^ 2 * ‖t‖ ^ 2) / 2 : ℝ) := by
  rw [charFun_map_smul, charFun_stdGaussian, ← Complex.ofReal_pow, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs]
  congr 1
  push_cast
  ring

/-- The modulus of the characteristic function of the standard Gaussian dilated by `σ` — in
physics the modulus of the form factor of the isotropic Gaussian charge distribution of width
`σ` — is `exp (-σ² ‖t‖² / 2)`. -/
theorem norm_charFun_map_smul_stdGaussian (σ : ℝ) (t : E) :
    ‖charFun ((stdGaussian E).map (σ • ·)) t‖ = Real.exp (-(σ ^ 2 * ‖t‖ ^ 2) / 2) := by
  rw [charFun_map_smul_stdGaussian, Complex.norm_exp_ofReal]

/-- The characteristic function of the standard Gaussian dilated by `σ` departs from one by at most
`σ² ‖t‖² / 2`: `1 - ‖charFun ((stdGaussian E).map (σ • ·)) t‖ ≤ σ² ‖t‖² / 2`. -/
theorem one_sub_norm_charFun_map_smul_stdGaussian_le (σ : ℝ) (t : E) :
    1 - ‖charFun ((stdGaussian E).map (σ • ·)) t‖ ≤ σ ^ 2 * ‖t‖ ^ 2 / 2 := by
  rw [norm_charFun_map_smul_stdGaussian]
  -- `1 - exp (-y) ≤ y` for `y = σ² ‖t‖² / 2`
  linarith [Real.add_one_le_exp (-(σ ^ 2 * ‖t‖ ^ 2) / 2)]

/-- The squared modulus of the characteristic function of the standard Gaussian dilated by `σ`
decays as `exp (-σ² ‖t‖²)`; in physics this is the factor by which the coherent rate of the
isotropic Gaussian charge distribution of width `σ` is suppressed at momentum `t`. -/
theorem norm_sq_charFun_map_smul_stdGaussian (σ : ℝ) (t : E) :
    ‖charFun ((stdGaussian E).map (σ • ·)) t‖ ^ 2 = Real.exp (-(σ ^ 2 * ‖t‖ ^ 2)) := by
  rw [norm_charFun_map_smul_stdGaussian, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

end ProbabilityTheory
