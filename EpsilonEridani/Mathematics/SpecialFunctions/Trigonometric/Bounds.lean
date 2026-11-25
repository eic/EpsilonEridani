/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Boundedness of `Real.sin` and `Real.cos` along a filter

Since `|sin y| ≤ 1` and `|cos y| ≤ 1` (`Real.abs_sin_le_one`, `Real.abs_cos_le_one`), the sine
and cosine of any real-valued function are `O(1)` along any filter:

* `Real.isBigO_sin_comp_one`: `sin (f x) = O(1)`;
* `Real.isBigO_cos_comp_one`: `cos (f x) = O(1)`.

These are the bounds used to show that oscillatory terms such as `sin (x - φ) / x` are
`O(1 / x)` in large-argument asymptotics.
-/

public section

open Asymptotics

namespace Real

/-- The sine of any function is bounded, along any filter. -/
theorem isBigO_sin_comp_one {α : Type*} (l : Filter α) (f : α → ℝ) :
    (fun x => sin (f x)) =O[l] fun _ => (1 : ℝ) :=
  .of_bound 1 (.of_forall fun x => by simpa using abs_sin_le_one (f x))

/-- The cosine of any function is bounded, along any filter. -/
theorem isBigO_cos_comp_one {α : Type*} (l : Filter α) (f : α → ℝ) :
    (fun x => cos (f x)) =O[l] fun _ => (1 : ℝ) :=
  .of_bound 1 (.of_forall fun x => by simpa using abs_cos_le_one (f x))

end Real
