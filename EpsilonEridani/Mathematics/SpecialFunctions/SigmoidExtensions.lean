/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
# Sigmoid extensions

Extensions to `Mathlib.Analysis.SpecialFunctions.Sigmoid`: the bound `Real.sigmoid_le_exp`,
`sigmoid x ≤ exp x`. It dominates the logistic function by its exponential tail, which is what
makes the logistic (Woods–Saxon) nuclear density profile integrable over `ℝ³`
(`EpsilonEridani.Particles.Nuclei.integrable_woodsSaxonDensity_norm`).
-/

public section

namespace Real

/-- The logistic function is bounded by the exponential: `Real.sigmoid x ≤ Real.exp x`. -/
lemma sigmoid_le_exp (x : ℝ) : sigmoid x ≤ exp x := by
  calc sigmoid x = (1 + exp (-x))⁻¹ := sigmoid_def x
    _ ≤ (exp (-x))⁻¹ := inv_anti₀ (exp_pos _) (le_add_of_nonneg_left zero_le_one)
    _ = exp x := by rw [← exp_neg, neg_neg]

end Real
