/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Probability.Moments.Variance
/-!

# Zero variance of a single random variable

Mathlib's `ProbabilityTheory.evariance_eq_zero_iff` characterises the random variables of zero
extended variance, and `ProbabilityTheory.ae_eq_integral_of_variance_eq_zero` gives one direction
for the real variance. This file records the real-valued equivalence for a square-integrable
random variable, in which form it enters the covariance matrix of a finite family
(`EpsilonEridani.ProbabilityTheory.ae_eq_integral_iff_covarianceMatrix_mulVec_eq_zero`).

All declarations live in the namespace `EpsilonEridani.ProbabilityTheory`.

## Main results

* `variance_eq_zero_iff`: a square-integrable random variable has zero variance exactly when it is
  almost surely equal to its integral.
-/

public section

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
