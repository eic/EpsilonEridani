/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Vanishing of functions with `x • f x = 0`

A function into a normed space that is continuous at the origin and whose scalar multiple
`x • f x` vanishes identically is itself zero (`ContinuousAt.eq_zero_of_forall_smul_eq_zero`,
with the multiplicative form `ContinuousAt.eq_zero_of_forall_mul_eq_zero` for `f : 𝕜 → 𝕜`).
Away from the origin the scalar is a unit, so the function vanishes there by Mathlib's
`smul_eq_zero`, and continuity at the origin fixes the remaining value `f 0` as the limit of
the vanishing values. This is a removable-singularity criterion: it promotes an identity that
is only known multiplied by `x` to one that holds at the origin as well.

It is used in the construction of the spherical Bessel functions
(`EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`): differentiating the
three-term recurrence there only yields it multiplied by `x`, and this lemma removes that
factor and extends the recurrence across the origin.
-/

@[expose] public section

open Filter Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If `f` is continuous at `0` and `x • f x = 0` for every `x`, then `f = 0`: a function that
vanishes away from the origin and is continuous there vanishes at the origin as well. -/
theorem ContinuousAt.eq_zero_of_forall_smul_eq_zero {f : 𝕜 → E} (hf : ContinuousAt f 0)
    (h : ∀ x, x • f x = 0) : f = 0 := by
  have heq : f =ᶠ[𝓝[≠] (0:𝕜)] (fun _ => (0 : E)) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (smul_eq_zero.mp (h y)).resolve_left hy
  have h0 : f 0 = 0 :=
    tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.mono_left nhdsWithin_le_nhds)
      tendsto_const_nhds heq
  funext y
  rcases eq_or_ne y 0 with rfl | hy
  · exact h0
  · exact (smul_eq_zero.mp (h y)).resolve_left hy

/-- If `f : 𝕜 → 𝕜` is continuous at `0` and `x * f x = 0` for every `x`, then `f = 0`: the
multiplicative form of `ContinuousAt.eq_zero_of_forall_smul_eq_zero`. -/
theorem ContinuousAt.eq_zero_of_forall_mul_eq_zero {f : 𝕜 → 𝕜} (hf : ContinuousAt f 0)
    (h : ∀ x, x * f x = 0) : f = 0 :=
  hf.eq_zero_of_forall_smul_eq_zero h
