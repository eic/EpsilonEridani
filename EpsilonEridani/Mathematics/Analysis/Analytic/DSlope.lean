/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Analyticity of the slope function `dslope`

`dslope f a` is the difference quotient `(f b - f a) / (b - a)`, extended at `b = a` by the
derivative of `f`. Continuity and differentiability transfer away from `a` via Mathlib's
`continuousAt_dslope_of_ne` and `differentiableAt_dslope_of_ne`. At `a`,
`continuousAt_dslope_same` equates continuity of `dslope f a` with differentiability of `f` at `a`,
not continuity of `f`. This file proves the analytic analogue, which needs no such case
distinction: `dslope f a` is analytic at a point if and only if `f` is
(`EpsilonEridani.analyticAt_dslope`), and so on any set (`EpsilonEridani.analyticOnNhd_dslope`).

Removing the removable singularity of `f' / x` at the origin in this way keeps the iterates of
`(1 / x) d/dx` analytic, which is how the Rayleigh formula for the spherical Bessel functions
(`EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`) is made total.
-/

public section

open Filter Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a b : 𝕜} {s : Set 𝕜}

namespace EpsilonEridani

/-- The slope function `dslope f a` is analytic at `b` if and only if `f` is. -/
theorem analyticAt_dslope : AnalyticAt 𝕜 (dslope f a) b ↔ AnalyticAt 𝕜 f b := by
  refine ⟨fun h => ?_, fun hf => ?_⟩
  · -- `f x = f a + (x - a) • dslope f a x`
    have heq : (fun x => f a + (x - a) • dslope f a x) = f := by
      funext x
      rw [sub_smul_dslope, add_sub_cancel]
    rw [← heq]
    exact analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul h)
  rcases eq_or_ne b a with rfl | h
  · obtain ⟨p, hp⟩ := hf
    exact ⟨_, hp.has_fpower_series_dslope_fslope⟩
  · -- away from `a`, `dslope f a` agrees near `b` with the difference quotient
    refine AnalyticAt.congr ?_ (dslope_eventuallyEq_slope_of_ne f h).symm
    have hslope : slope f a = fun x => (x - a)⁻¹ • (f x - f a) := by
      funext x
      rw [slope_def_module]
    rw [hslope]
    exact ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h)).smul
      (hf.sub analyticAt_const)

/-- The slope function `dslope f a` is analytic on a neighbourhood of each point of `s` if and
only if `f` is. -/
theorem analyticOnNhd_dslope : AnalyticOnNhd 𝕜 (dslope f a) s ↔ AnalyticOnNhd 𝕜 f s :=
  forall₂_congr fun _ _ => analyticAt_dslope

end EpsilonEridani
