/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Extensions for the Gamma and digamma functions

Mathlib's Gamma theory proves that the reciprocal `1/Γ` of the Gamma function is entire, that
the digamma function `ψ = Γ'/Γ` (`Complex.digamma`) is meromorphic, and that `Γ` itself is
complex-differentiable away from the non-positive integers (`Complex.differentiableAt_Gamma`),
but it does not provide `AnalyticAt` statements for `Γ` or `ψ`. Both functions have simple
poles exactly at the non-positive integers `0, -1, -2, …` and are analytic everywhere else.
This file supplies those analyticity statements, together with the discreteness of the
negative integers in `ℂ` that the pole structure rests on:

* `EpsilonEridani.analyticAt_Gamma`: `Γ` is analytic away from the non-positive integers;
* `EpsilonEridani.analyticAt_digamma`: `ψ` is analytic away from the non-positive integers;
* `EpsilonEridani.eventually_forall_ne_neg_nat_succ`: near a negative integer `-(m + 1)`, every
  other point avoids all negative integers, the punctured neighbourhood on which `Γ` and `ψ`
  are analytic there.

The analyticity statements are the facts that the meromorphic continuation of the first
harmonic sum (`EpsilonEridani.Mathematics.HarmonicSum.Continuation`) inherits its regularity
and pole structure from.
-/

@[expose] public section

open Complex Filter Topology

namespace EpsilonEridani

/-- `Γ` is analytic away from its poles `0, -1, -2, …`. -/
@[fun_prop]
theorem analyticAt_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : AnalyticAt ℂ Gamma s := by
  -- `Γ` is the reciprocal of the entire function `1/Γ`, which does not vanish at `s`.
  have h := (differentiable_one_div_Gamma.analyticAt s).inv (inv_ne_zero (Gamma_ne_zero hs))
  simpa only [Pi.inv_def, inv_inv] using h

/-- The digamma function `ψ = Γ'/Γ` is analytic away from its poles `0, -1, -2, …`. -/
@[fun_prop]
theorem analyticAt_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : AnalyticAt ℂ digamma s := by
  have hΓ := analyticAt_Gamma hs
  rw [digamma_def, logDeriv]
  exact hΓ.deriv.div hΓ (Gamma_ne_zero hs)

/-- Near a negative integer `-(m + 1)`, every other point avoids the negative integers. -/
theorem eventually_forall_ne_neg_nat_succ (m : ℕ) :
    ∀ᶠ s in 𝓝[≠] (-(m + 1 : ℂ)), ∀ j : ℕ, s ≠ -(j + 1 : ℂ) := by
  -- the integers other than `-(m + 1)` form a closed subset of `ℂ`
  have hc := isClosedEmbedding_intCast.isClosedMap _ (isClosed_discrete {n : ℤ | n ≠ -(m + 1)})
  have hm : -(m + 1 : ℂ) ∈ (((↑) : ℤ → ℂ) '' {n : ℤ | n ≠ -(m + 1)})ᶜ := by
    rintro ⟨n, hn, hn'⟩
    exact hn (by exact_mod_cast hn')
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hc.isOpen_compl.mem_nhds hm)]
    with s hne hs j hj
  subst hj
  refine hs ⟨-(j + 1), fun h => hne ?_, by push_cast; rfl⟩
  simp [show j = m by omega]

end EpsilonEridani
