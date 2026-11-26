/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Probability.Moments.Variance

/-!
# The variance of a function with values in a real inner product space

Let `f` be a square-integrable function on a probability space `(α, μ)` with values in a real
inner product space `E`. Its mean squared deviation from its mean is its second moment minus the
squared norm of its mean,

`∫ ‖f - ∫ f dμ‖² dμ = ∫ ‖f‖² dμ - ‖∫ f dμ‖²`,

and it vanishes exactly when `f` is almost everywhere equal to its mean.

For real-valued `f` the first identity is `ProbabilityTheory.variance_eq_sub` and the second is
`ProbabilityTheory.ae_eq_integral_of_variance_eq_zero`. Mathlib's `ProbabilityTheory.variance`
is real-valued only; the statements here cover `ℂ`-valued and, more generally,
Hilbert-space-valued functions, as needed for quantum-mechanical amplitudes. Together with
`TauCeti.integral_norm_sub_sq_prod`, which expresses the same quantity as half the mean squared
distance between two independent samples, they are the moment identities behind the
coherent/incoherent decomposition of a configuration-averaged cross section.

The file also records, in the namespace `EpsilonEridani.ProbabilityTheory`, the real-valued
equivalence between zero variance and almost-sure constancy for a square-integrable random
variable, in which form it enters the covariance matrix of a finite family
(`EpsilonEridani.ProbabilityTheory.ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero`).
Mathlib's `ProbabilityTheory.evariance_eq_zero_iff` characterises the random variables of zero
extended variance, and `ProbabilityTheory.ae_eq_integral_of_variance_eq_zero` gives one direction
for the real variance.

## Main results

* `MeasureTheory.MemLp.integral_norm_sub_integral_sq`: `∫ ‖f - ∫ f‖² = ∫ ‖f‖² - ‖∫ f‖²`.
* `MeasureTheory.MemLp.norm_integral_sq_le_integral_norm_sq`: `‖∫ f‖² ≤ ∫ ‖f‖²` in any real
  normed space; in an inner product space this is the non-negativity of the mean squared
  deviation.
* `MeasureTheory.MemLp.integral_norm_sub_integral_sq_eq_zero_iff`: the mean squared deviation
  vanishes if and only if `f` is almost everywhere equal to its mean; this holds in any real
  normed space.
* `EpsilonEridani.ProbabilityTheory.variance_eq_zero_iff`: a square-integrable real random
  variable has zero variance exactly when it is almost surely equal to its integral.
-/

public section

open MeasureTheory
open scoped RealInnerProductSpace

namespace MeasureTheory.MemLp

variable {α E : Type*} {mα : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {f : α → E}

/-- **The variance as second moment minus squared mean.** For a square-integrable function `f`
with values in a real inner product space and a probability measure `μ`, the mean squared
deviation of `f` from its mean is `∫ ‖f‖² dμ - ‖∫ f dμ‖²`. -/
theorem integral_norm_sub_integral_sq [InnerProductSpace ℝ E] [CompleteSpace E]
    [IsProbabilityMeasure μ] (hf : MemLp f 2 μ) :
    ∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ - ‖∫ x, f x ∂μ‖ ^ 2 := by
  have hf₁ : Integrable f μ := hf.integrable one_le_two
  have hsq : Integrable (fun x ↦ ‖f x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).1 hf
  have hin : Integrable (fun x ↦ 2 * ⟪∫ y, f y ∂μ, f x⟫) μ :=
    (hf₁.const_inner _).const_mul 2
  simp_rw [norm_sub_sq_real, real_inner_comm (∫ y, f y ∂μ)]
  rw [integral_add (f := fun x ↦ ‖f x‖ ^ 2 - 2 * ⟪∫ y, f y ∂μ, f x⟫) (hsq.sub hin)
    (integrable_const _), integral_sub hsq hin, integral_const_mul,
    integral_inner hf₁, real_inner_self_eq_norm_sq, integral_const]
  simp only [probReal_univ, one_smul]
  ring

/-- **The squared mean is at most the second moment.** For a square-integrable function `f` with
values in a real normed space and a probability measure `μ`, `‖∫ f dμ‖² ≤ ∫ ‖f‖² dμ`. In an inner
product space the difference is the mean squared deviation, see `integral_norm_sub_integral_sq`. -/
theorem norm_integral_sq_le_integral_norm_sq [NormedSpace ℝ E] [IsProbabilityMeasure μ]
    (hf : MemLp f 2 μ) : ‖∫ x, f x ∂μ‖ ^ 2 ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by
  -- `‖∫ f‖ ≤ ∫ ‖f‖`, and `(∫ ‖f‖)² ≤ ∫ ‖f‖²` is the non-negativity of the variance of `‖f‖`.
  have h := ProbabilityTheory.variance_nonneg (fun x ↦ ‖f x‖) μ
  rw [ProbabilityTheory.variance_eq_sub hf.norm, sub_nonneg] at h
  calc ‖∫ x, f x ∂μ‖ ^ 2 ≤ (∫ x, ‖f x‖ ∂μ) ^ 2 := by
        gcongr
        exact norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ ^ 2 ∂μ := by simpa using h

/-- **Vanishing of the variance.** For a square-integrable function `f` with values in a real
normed space and a finite measure `μ`, the integral `∫ ‖f - ∫ f dμ‖² dμ` vanishes if and only if
`f` is almost everywhere equal to the vector `∫ f dμ`. For a probability measure this integral is
the variance of `f` and `∫ f dμ` is its mean. -/
theorem integral_norm_sub_integral_sq_eq_zero_iff [NormedSpace ℝ E] [IsFiniteMeasure μ]
    (hf : MemLp f 2 μ) :
    ∫ x, ‖f x - ∫ y, f y ∂μ‖ ^ 2 ∂μ = 0 ↔ f =ᵐ[μ] fun _ ↦ ∫ y, f y ∂μ := by
  have hint : Integrable (fun x ↦ ‖f x - ∫ y, f y ∂μ‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (hf.sub (memLp_const _)).aestronglyMeasurable).1
      (hf.sub (memLp_const _))
  rw [integral_eq_zero_iff_of_nonneg (fun _ ↦ by positivity) hint]
  constructor
  · intro h
    filter_upwards [h] with x hx
    simpa [sub_eq_zero] using hx
  · intro h
    filter_upwards [h] with x hx
    simp [hx]

end MeasureTheory.MemLp

namespace EpsilonEridani
namespace ProbabilityTheory

open MeasureTheory _root_.ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A square-integrable random variable has zero variance exactly when it is almost surely equal
to its integral `μ[·]`. -/
theorem variance_eq_zero_iff {Y : Ω → ℝ} (hY : MemLp Y 2 μ) :
    Var[Y; μ] = 0 ↔ Y =ᵐ[μ] fun _ => μ[Y] := by
  rw [← evariance_eq_zero_iff hY.aemeasurable, variance, ENNReal.toReal_eq_zero_iff,
    or_iff_left (evariance_lt_top hY).ne]

end ProbabilityTheory
end EpsilonEridani
