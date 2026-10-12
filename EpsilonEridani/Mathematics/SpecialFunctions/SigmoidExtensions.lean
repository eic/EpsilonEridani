/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Sigmoid extensions

Local extensions to `Mathlib.Analysis.SpecialFunctions.Sigmoid`, not yet upstreamed to Mathlib:
the bound `Real.sigmoid_le_exp` between the logistic function and the exponential.
-/

public section

namespace Real

/-- The logistic function is bounded by the exponential: `Real.sigmoid x ≤ Real.exp x`. -/
lemma sigmoid_le_exp (x : ℝ) : sigmoid x ≤ exp x := by
  rw [sigmoid_def, ← inv_inv (exp x), inv_le_inv₀ (by positivity) (by positivity), ← exp_neg]
  exact le_add_of_nonneg_left zero_le_one

end Real
