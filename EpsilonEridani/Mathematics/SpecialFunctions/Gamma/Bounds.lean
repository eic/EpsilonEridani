/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Bounds on the real Gamma function

Mathlib proves that the real Gamma function is convex on `(0, ∞)` (`Real.convexOn_Gamma`) and
takes the value one at `1` and `2` (`Real.Gamma_one`, `Real.Gamma_two`). This file records the
resulting bound on the interval between them:

* `EpsilonEridani.Gamma_le_one_of_mem_Icc`: `Γ(x) ≤ 1` for `1 ≤ x ≤ 2`.
-/

@[expose] public section

open Set

namespace EpsilonEridani

/-- The real Gamma function is at most one on `[1, 2]`, the interval between its two values
`Γ(1) = Γ(2) = 1`. -/
theorem Gamma_le_one_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (1 : ℝ) 2) : Real.Gamma x ≤ 1 := by
  have h := Real.convexOn_Gamma.le_on_segment (mem_Ioi.mpr one_pos) (mem_Ioi.mpr two_pos)
    (by rwa [segment_eq_Icc one_le_two])
  simpa [Real.Gamma_one, Real.Gamma_two] using h

end EpsilonEridani
