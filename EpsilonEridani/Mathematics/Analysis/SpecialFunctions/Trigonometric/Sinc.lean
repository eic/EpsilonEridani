/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import EpsilonEridani.Mathematics.Analysis.Analytic.DSlope

/-!
# Analyticity of `Real.sinc`

Mathlib proves that `Real.sinc` is continuous (`Real.continuous_sinc`). Since `sinc` is the slope
function `dslope sin 0` (`Real.sinc_eq_dslope`) and `dslope` preserves analyticity
(`EpsilonEridani.analyticAt_dslope`), `sinc` is real analytic on the whole line
(`EpsilonEridani.Real.analyticAt_sinc`).
-/

public section

open Real

namespace EpsilonEridani.Real

/-- `Real.sinc` is real analytic at every point. -/
@[fun_prop]
theorem analyticAt_sinc (x : ℝ) : AnalyticAt ℝ sinc x := by
  rw [sinc_eq_dslope]
  exact analyticAt_dslope.mpr analyticAt_sin

end EpsilonEridani.Real
