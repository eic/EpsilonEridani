/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift

import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Derivatives within a set of `x ↦ f (-x)`

Mathlib's `derivWithin_comp_neg` computes `derivWithin (fun x ↦ f (-x)) s x`; this file supplies
the companion `HasDerivWithinAt.comp_neg`: if `f` has derivative `f'` at `-x` within `-s`, then
`x ↦ f (-x)` has derivative `-f'` at `x` within `s`. It turns a one-sided derivative in one variable
into the opposite one-sided derivative in the reflected variable, as in the dictionary between the
momentum transfer `t ≤ 0` and `Q² = -t ≥ 0`
(`EpsilonEridani.Particles.Hadron.GravitationalFormFactors.Kinematics`).
-/

@[expose] public section

open scoped Pointwise

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : 𝕜 → F} {f' : F} {s : Set 𝕜} {x : 𝕜}

/-- If `f` has derivative `f'` at `-x` within `-s`, then `x ↦ f (-x)` has derivative `-f'` at `x`
within `s`. -/
theorem HasDerivWithinAt.comp_neg (hf : HasDerivWithinAt f f' (-s) (-x)) :
    HasDerivWithinAt (fun y => f (-y)) (-f') s x := by
  simpa [Function.comp_def] using
    HasDerivWithinAt.scomp x hf (hasDerivWithinAt_neg x s) fun y hy => Set.neg_mem_neg.mpr hy
