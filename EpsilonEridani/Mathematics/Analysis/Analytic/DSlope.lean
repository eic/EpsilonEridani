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
derivative of `f`. Mathlib (`Mathlib.Analysis.Calculus.DSlope`) proves that `dslope f a` is
continuous or differentiable exactly where `f` is. This file proves the analytic counterpart:
`dslope f a` is analytic at a point if and only if `f` is.

At `b = a` the forward direction is `HasFPowerSeriesAt.has_fpower_series_dslope_fslope`; away from
`a`, `dslope f a` agrees near `b` with the difference quotient. The converse comes from the identity
`f b = f a + (b - a) • dslope f a b`. All four transfer lemmas hold on any set, without restriction.

Removing the removable singularity of `f' / x` at the origin in this way keeps the iterates of
`(1 / x) d/dx` analytic, which is how the Rayleigh formula for the spherical Bessel functions
(`EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`) is made total.

The continuity and differentiability transfer lemmas from Mathlib (`continuousAt_dslope_same`,
`continuousAt_dslope_of_ne`, `differentiableAt_dslope_of_ne`) give: `dslope f a` is continuous or
differentiable away from `a` exactly where `f` is; at `a`, continuity of `dslope f a` corresponds
to differentiability of `f` at `a`. This file proves the stronger analytic analogue: on any set,
`dslope f a` is analytic exactly where `f` is.
-/

@[expose] public section

open Filter Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {f : 𝕜 → E} {a b : 𝕜} {s : Set 𝕜}

namespace EpsilonEridani

/-- A function is analytic wherever its slope function `dslope f a` is. -/
theorem analyticAt_of_dslope (h : AnalyticAt 𝕜 (dslope f a) b) : AnalyticAt 𝕜 f b := by
  have hf : (fun x => f a + (x - a) • dslope f a x) = f := by
    funext x
    rw [sub_smul_dslope, add_sub_cancel]
  rw [← hf]
  exact analyticAt_const.add ((analyticAt_id.sub analyticAt_const).smul h)

/-- The slope function `dslope f a` is analytic at `a` if and only if `f` is. -/
theorem analyticAt_dslope_same : AnalyticAt 𝕜 (dslope f a) a ↔ AnalyticAt 𝕜 f a := by
  refine ⟨analyticAt_of_dslope, fun ⟨p, hp⟩ => ⟨_, hp.has_fpower_series_dslope_fslope⟩⟩

/-- Away from `a`, the slope function `dslope f a` is analytic at `b` if and only if `f` is. -/
theorem analyticAt_dslope_of_ne (h : b ≠ a) :
    AnalyticAt 𝕜 (dslope f a) b ↔ AnalyticAt 𝕜 f b := by
  refine ⟨analyticAt_of_dslope, fun hf => ?_⟩
  refine AnalyticAt.congr ?_ (dslope_eventuallyEq_slope_of_ne f h).symm
  have hslope : slope f a = fun x => (x - a)⁻¹ • (f x - f a) := by
    funext x
    rw [slope_def_module]
  rw [hslope]
  exact ((analyticAt_id.sub analyticAt_const).inv (sub_ne_zero.mpr h)).smul
    (hf.sub analyticAt_const)

/-- The slope function `dslope f a` is analytic on a neighbourhood of each point of `s` if and
only if `f` is. -/
theorem analyticOnNhd_dslope :
    AnalyticOnNhd 𝕜 (dslope f a) s ↔ AnalyticOnNhd 𝕜 f s := by
  refine ⟨fun h b hb => analyticAt_of_dslope (h b hb), fun h b hb => ?_⟩
  rcases eq_or_ne b a with rfl | hba
  · exact analyticAt_dslope_same.mpr (h b hb)
  · exact (analyticAt_dslope_of_ne hba).mpr (h b hb)

end EpsilonEridani
