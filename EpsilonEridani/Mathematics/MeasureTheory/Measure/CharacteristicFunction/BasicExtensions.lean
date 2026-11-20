/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The characteristic function near the origin, from the second moment

For a probability measure `μ` on a real inner product space with finite second moment, the
characteristic function `charFun μ t = ∫ x, exp (i ⟪x, t⟫) ∂μ` stays close to its value `1` at the
origin as long as `‖t‖² ∫ ‖x‖² ∂μ` is small:

* `MeasureTheory.one_sub_re_charFun_le`: `1 - Re (charFun μ t) ≤ ‖t‖² (∫ ‖x‖² ∂μ) / 2`;
* `MeasureTheory.one_sub_norm_charFun_le`: the same bound for `1 - ‖charFun μ t‖`.

Both follow by integrating `1 - cos y ≤ y² / 2` at `y = ⟪x, t⟫` and Cauchy–Schwarz. No assumption
on the shape of `μ` beyond its second moment is used. In physics the characteristic function of a
normalised charge distribution is its form factor, and the bound says that a probe whose momentum
`t` is small against the inverse root-mean-square radius does not resolve the distribution.
-/

public section

open Complex
open scoped RealInnerProductSpace

namespace MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- **The characteristic function near the origin.** For a probability measure with finite second
moment, `1 - Re (charFun μ t) ≤ ‖t‖² (∫ ‖x‖² ∂μ) / 2`. -/
theorem one_sub_re_charFun_le (hμ : Integrable (fun x ↦ ‖x‖ ^ 2) μ) (t : E) :
    1 - (charFun μ t).re ≤ ‖t‖ ^ 2 * (∫ x, ‖x‖ ^ 2 ∂μ) / 2 := by
  have hint : Integrable (fun x ↦ exp (⟪x, t⟫ * I)) μ :=
    BoundedContinuousFunction.integrable μ (BoundedContinuousFunction.innerProbChar t)
  have hsq : Integrable (fun x ↦ ‖t‖ ^ 2 * ‖x‖ ^ 2 / 2) μ := (hμ.const_mul _).div_const _
  -- pointwise, `1 - ‖t‖² ‖x‖² / 2 ≤ 1 - ⟪x, t⟫² / 2 ≤ cos ⟪x, t⟫`
  have hpt : ∀ x, 1 - ‖t‖ ^ 2 * ‖x‖ ^ 2 / 2 ≤ (exp (⟪x, t⟫ * I)).re := fun x ↦ by
    rw [exp_ofReal_mul_I_re]
    have hcs : ⟪x, t⟫ ^ 2 ≤ (‖x‖ * ‖t‖) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm x t) 2
    nlinarith [Real.one_sub_sq_div_two_le_cos (x := ⟪x, t⟫)]
  have hmono : ∫ x, (1 - ‖t‖ ^ 2 * ‖x‖ ^ 2 / 2) ∂μ ≤ ∫ x, (exp (⟪x, t⟫ * I)).re ∂μ :=
    integral_mono ((integrable_const 1).sub hsq) hint.re hpt
  rw [integral_sub (integrable_const 1) hsq, integral_div, integral_const_mul] at hmono
  rw [charFun_apply, ← RCLike.re_to_complex, ← integral_re hint]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, RCLike.re_to_complex] at hmono ⊢
  linarith

/-- For a probability measure with finite second moment,
`1 - ‖charFun μ t‖ ≤ ‖t‖² (∫ ‖x‖² ∂μ) / 2`. -/
theorem one_sub_norm_charFun_le (hμ : Integrable (fun x ↦ ‖x‖ ^ 2) μ) (t : E) :
    1 - ‖charFun μ t‖ ≤ ‖t‖ ^ 2 * (∫ x, ‖x‖ ^ 2 ∂μ) / 2 :=
  (sub_le_sub_left (re_le_norm _) 1).trans (one_sub_re_charFun_le hμ t)

end MeasureTheory
