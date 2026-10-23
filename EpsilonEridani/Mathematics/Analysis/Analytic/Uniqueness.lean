/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Analytic.Uniqueness
public import TauCeti.Analysis.Analytic.Complexification.Basic

/-!
# The identity theorem from the real points of `ℂ^ι`

Mathlib's identity theorem in several variables,
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, asks two analytic functions to agree on a
whole neighbourhood of a point of `ℂ^ι`. This file derives from it the corresponding statement in
which the functions only agree at the *real* points near one real point: the real slice `ℝ^ι ⊆ ℂ^ι`
is a maximal totally real subspace, so agreement there already forces agreement on an open set.

## Main results

* `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq_ofReal`: two functions analytic on a
  preconnected set `U` that agree at the real points near one real point of `U` agree on all of
  `U`.

## Implementation notes

The local step is not reproved here: two functions analytic at a real point of `ℂ^ι` that agree at
the nearby real points agree on a whole neighbourhood of that point. This is TauCeti's identity
theorem on the real points, `AnalyticAt.eventuallyEq_of_eventually_real`. The global statement
then follows from Mathlib's several-variable identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
-/

public section

open Filter Set Topology

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Identity theorem from the real points.** Two functions analytic on a preconnected set
`U ⊆ ℂ^ι` that agree at the real points near one real point of `U` agree on all of `U`. -/
theorem AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq_ofReal {f g : (ι → ℂ) → F}
    {U : Set (ι → ℂ)} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) {x₀ : ι → ℝ} (h₀ : (fun i => (x₀ i : ℂ)) ∈ U)
    (hfg : (fun x : ι → ℝ => f fun i => (x i : ℂ)) =ᶠ[𝓝 x₀] fun x => g fun i => (x i : ℂ)) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU h₀
    ((hf _ h₀).eventuallyEq_of_eventually_real (hg _ h₀) hfg)
