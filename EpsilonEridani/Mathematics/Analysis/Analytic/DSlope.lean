/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Analyticity of the slope function `dslope`

`dslope f a` is the difference quotient `(f b - f a) / (b - a)`, extended at `b = a` by the
derivative of `f`. Continuity and differentiability transfer away from `a` via Mathlib's
`continuousAt_dslope_of_ne` and `differentiableAt_dslope_of_ne`. At `a`,
`continuousAt_dslope_same` equates continuity of `dslope f a` with differentiability of `f` at `a`,
not continuity of `f`. Analyticity needs no such case distinction, and Mathlib provides one
direction of it: `AnalyticAt.dslope` and `AnalyticOnNhd.dslope` state that `dslope f a` is analytic
at a point, or on a neighbourhood of a set, whenever `f` is. This file proves the converse
direction, which Mathlib lacks: `f` is analytic at `b` whenever `dslope f a` is
(`AnalyticAt.of_dslope`), in the shape of Mathlib's `ContinuousAt.of_dslope` and
`DifferentiableAt.of_dslope`.

Removing the removable singularity of `f' / x` at the origin in this way keeps the iterates of
`(1 / x) d/dx` analytic, which is how the Rayleigh formula for the spherical Bessel functions
(`EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`) is made total.
-/

@[expose] public section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a b : 𝕜}

namespace EpsilonEridani

/-- If `dslope f a` is analytic at `b`, then so is `f`, for any base point `a`. Combined with
Mathlib's `AnalyticAt.dslope`, which gives the converse, `dslope f a` is analytic at `b` if and
only if `f` is, with no case distinction on `b = a` (contrast `continuousAt_dslope_same`, which at
`b = a` relates `dslope f a` to the differentiability of `f` instead). This is the analytic
analogue of Mathlib's `ContinuousAt.of_dslope` and `DifferentiableAt.of_dslope`. -/
theorem _root_.AnalyticAt.of_dslope (h : AnalyticAt 𝕜 (dslope f a) b) : AnalyticAt 𝕜 f b := by
  -- `f x = f a + (x - a) • dslope f a x`
  have heq : (fun x => f a + (x - a) • dslope f a x) = f := by
    funext x
    rw [sub_smul_dslope, add_sub_cancel]
  rw [← heq]
  exact analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul h)

end EpsilonEridani
