/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Moments of the norm under a dilation

The image of a measure `μ` on a normed space under the dilation `x ↦ c • x` has its moments of the
norm scaled by the corresponding power of `‖c‖`:
`∫ ‖x‖ ^ n ∂(μ.map (c • ·)) = ‖c‖ ^ n * ∫ ‖x‖ ^ n ∂μ`
(`MeasureTheory.integral_norm_pow_map_smul`). No integrability is needed: both sides vanish
together when `‖x‖ ^ n` is not integrable. For `n = 2` this says that dilating a distribution by
`c` scales its root-mean-square norm by `‖c‖`.
-/

public section

namespace MeasureTheory

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [MeasurableSpace E] [BorelSpace E]

/-- The `n`-th moment of the norm of the image of a measure under the dilation `x ↦ c • x` is
`‖c‖ ^ n` times the `n`-th moment of the norm of the measure:
`∫ ‖x‖ ^ n ∂(μ.map (c • ·)) = ‖c‖ ^ n * ∫ ‖x‖ ^ n ∂μ`. -/
theorem integral_norm_pow_map_smul (μ : Measure E) (c : 𝕜) (n : ℕ) :
    ∫ x, ‖x‖ ^ n ∂(μ.map (c • ·)) = ‖c‖ ^ n * ∫ x, ‖x‖ ^ n ∂μ := by
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [norm_smul, mul_pow]
  exact integral_const_mul _ _

end MeasureTheory
