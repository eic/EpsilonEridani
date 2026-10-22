/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Completion

/-!
# The identity theorem from the real points of `ℂ^ι`

Mathlib's identity theorem in several variables,
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, asks two analytic functions to agree on a
whole neighbourhood of a point of `ℂ^ι`. This file shows that agreement on a neighbourhood of a
point in the *real* slice `ℝ^ι ⊆ ℂ^ι` is already enough: the real slice is a maximal totally real
subspace, and an analytic function vanishing on an open piece of it vanishes on an open set.

## Main results

* `AnalyticAt.eventuallyEq_zero_of_eventuallyEq_zero_ofReal`: a function analytic at a real
  point that vanishes at the nearby real points vanishes on a neighbourhood of it in `ℂ^ι`.
* `AnalyticAt.eventuallyEq_of_eventuallyEq_ofReal`: two functions analytic at a real point that
  agree at the nearby real points agree on a neighbourhood of it in `ℂ^ι`.
* `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq_ofReal`: two functions analytic on a
  preconnected set `U` that agree at the real points near one real point of `U` agree on all of
  `U`.

## Implementation notes

The local step restricts the function to the complex line `λ ↦ re w + λ • im w` through a point
`w` near the real slice. That line meets the real slice in a real segment and passes through `w`
at `λ = I`, so the one-variable identity theorem carries the vanishing from the segment to `w`.
The local statement for two functions follows by applying this vanishing statement to their
difference, and the global statement then follows from Mathlib's several-variable identity theorem
`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. The target space need not be complete: the
vanishing statement is first proved for complete targets, where Mathlib's
`AnalyticAt.exists_ball_analyticOnNhd` spreads analyticity from the point to a ball around it, and
then transferred through the completion, as Mathlib does for its own identity theorem.
-/

public section

open Complex Filter Metric Set Topology

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The vanishing statement of `AnalyticAt.eventuallyEq_zero_of_eventuallyEq_zero_ofReal` for a
complete target. Completeness is what Mathlib's `AnalyticAt.exists_ball_analyticOnNhd` asks for to
make the function analytic on a whole ball around the point. -/
private theorem eventuallyEq_zero_of_eventuallyEq_zero_ofReal_aux [CompleteSpace F]
    {f : (ι → ℂ) → F} {x₀ : ι → ℝ} (hf : AnalyticAt ℂ f (fun i => (x₀ i : ℂ)))
    (h₀ : (fun x : ι → ℝ => f fun i => (x i : ℂ)) =ᶠ[𝓝 x₀] 0) :
    f =ᶠ[𝓝 (fun i => (x₀ i : ℂ))] 0 := by
  set z₀ : ι → ℂ := fun i => (x₀ i : ℂ)
  obtain ⟨r, hr, hfr⟩ := hf.exists_ball_analyticOnNhd
  obtain ⟨ρ, hρ, hρ₀⟩ := Metric.eventually_nhds_iff.1 h₀
  set ε := min r ρ
  have hε : 0 < ε := lt_min hr hρ
  refine Metric.eventually_nhds_iff.2 ⟨ε, hε, fun w hw => ?_⟩
  -- The real and imaginary parts of `w`, and the complex line through them.
  set u : ι → ℝ := fun i => (w i).re
  set v : ι → ℝ := fun i => (w i).im
  set p : ℂ → ι → ℂ := fun c => (fun i => (u i : ℂ)) + c • fun i => (v i : ℂ)
  -- The real part of `w` is as close to `x₀` as `w` is to `z₀`.
  have hu : dist u x₀ < ε := by
    refine (dist_pi_lt_iff hε).2 fun i => ?_
    calc dist (u i) (x₀ i) = |(w i - z₀ i).re| := by simp [u, z₀, Real.dist_eq]
      _ ≤ ‖w i - z₀ i‖ := abs_re_le_norm _
      _ = dist (w i) (z₀ i) := (dist_eq_norm _ _).symm
      _ < ε := (dist_pi_lt_iff hε).1 hw i
  -- The parameters of the points of the line inside the ball form a convex open set.
  set S : Set ℂ := p ⁻¹' ball z₀ ε
  have hS : Convex ℝ S :=
    ((convex_ball z₀ ε).translate_preimage_right fun i => (u i : ℂ)).linear_preimage
      ((LinearMap.toSpanSingleton ℂ _ fun i => (v i : ℂ)).restrictScalars ℝ)
  have hS₀ : (0 : ℂ) ∈ S := by
    simp only [S, mem_preimage, mem_ball]
    refine (dist_pi_lt_iff hε).2 fun i => ?_
    simpa [p, z₀, Complex.dist_eq, ← ofReal_sub, Real.dist_eq] using (dist_pi_lt_iff hε).1 hu i
  have hpI : p I = w := funext fun i => by simp [p, u, v, mul_comm I, re_add_im]
  -- Along the line, `f` vanishes at the real parameters near `0`.
  have hfreq : ∃ᶠ c in 𝓝[≠] (0 : ℂ), (f ∘ p) c = 0 := by
    have hreal : ∀ᶠ s in 𝓝 (0 : ℝ), u + s • v ∈ ball x₀ ρ := by
      have hc : Continuous fun s : ℝ => u + s • v := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds
        (isOpen_ball.mem_nhds (by simpa using hu.trans_le (min_le_right r ρ)))
    have hpreal : ∀ s : ℝ, p s = fun i => ((u + s • v) i : ℂ) := fun s => funext fun i => by
      simp [p]
    -- The inclusion `ℝ → ℂ` maps punctured neighbourhoods to punctured neighbourhoods.
    have htof : Tendsto ((↑) : ℝ → ℂ) (𝓝[≠] (0 : ℝ)) (𝓝[≠] ((0 : ℝ) : ℂ)) :=
      continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin fun _ hs => ofReal_injective.ne hs
    refine (ofReal_zero ▸ htof).frequently ?_
    refine (eventually_nhdsWithin_of_eventually_nhds (hreal.mono fun s hs => ?_)).frequently
    simpa [hpreal s] using hρ₀ (mem_ball.1 hs)
  have hS' : AnalyticOnNhd ℂ (f ∘ p) S :=
    (hfr.mono (ball_subset_ball (min_le_left r ρ))).comp
      (fun _ _ => analyticAt_const.add (analyticAt_id.smul analyticAt_const)) fun _ hc => hc
  have hI : (f ∘ p) I = 0 := hS'.eqOn_zero_of_preconnected_of_frequently_eq_zero
    hS.isPreconnected hS₀ hfreq (x := I) (by simpa [S, hpI] using hw)
  simpa [hpI] using hI

/-- A function analytic at a real point of `ℂ^ι` that vanishes at the nearby real points vanishes
on a neighbourhood of that point. -/
theorem AnalyticAt.eventuallyEq_zero_of_eventuallyEq_zero_ofReal {f : (ι → ℂ) → F}
    {x₀ : ι → ℝ} (hf : AnalyticAt ℂ f (fun i => (x₀ i : ℂ)))
    (h₀ : (fun x : ι → ℝ => f fun i => (x i : ℂ)) =ᶠ[𝓝 x₀] 0) :
    f =ᶠ[𝓝 (fun i => (x₀ i : ℂ))] 0 := by
  -- Pass to the completion of `F`, which is complete, and come back along its injective inclusion.
  set e : F →L[ℂ] UniformSpace.Completion F := UniformSpace.Completion.toComplL
  have he := eventuallyEq_zero_of_eventuallyEq_zero_ofReal_aux ((e.analyticAt _).comp hf)
    (h₀.mono fun x hx => by simp only [Pi.zero_apply] at hx ⊢; simp [hx])
  exact he.mono fun w hw => by simpa [e] using hw

/-- **Analytic functions on `ℂ^ι` are determined near a real point by their real values.** Two
functions analytic at a real point that agree at the nearby real points agree on a neighbourhood
of that point in `ℂ^ι`. -/
theorem AnalyticAt.eventuallyEq_of_eventuallyEq_ofReal {f g : (ι → ℂ) → F} {x₀ : ι → ℝ}
    (hf : AnalyticAt ℂ f (fun i => (x₀ i : ℂ))) (hg : AnalyticAt ℂ g (fun i => (x₀ i : ℂ)))
    (hfg : (fun x : ι → ℝ => f fun i => (x i : ℂ)) =ᶠ[𝓝 x₀] fun x => g fun i => (x i : ℂ)) :
    f =ᶠ[𝓝 (fun i => (x₀ i : ℂ))] g :=
  ((hf.sub hg).eventuallyEq_zero_of_eventuallyEq_zero_ofReal
    (hfg.mono fun _ hx => by simp [hx])).mono fun _ hw => by simpa [sub_eq_zero] using hw

/-- **Identity theorem from the real points.** Two functions analytic on a preconnected set
`U ⊆ ℂ^ι` that agree at the real points near one real point of `U` agree on all of `U`. -/
theorem AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq_ofReal {f g : (ι → ℂ) → F}
    {U : Set (ι → ℂ)} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (hU : IsPreconnected U) {x₀ : ι → ℝ} (h₀ : (fun i => (x₀ i : ℂ)) ∈ U)
    (hfg : (fun x : ι → ℝ => f fun i => (x i : ℂ)) =ᶠ[𝓝 x₀] fun x => g fun i => (x i : ℂ)) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg hU h₀
    ((hf _ h₀).eventuallyEq_of_eventuallyEq_ofReal (hg _ h₀) hfg)
