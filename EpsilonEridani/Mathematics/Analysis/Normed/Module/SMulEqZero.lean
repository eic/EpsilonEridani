/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Functions annihilated by the identity

If `x • f x = 0` for every `x`, then `f` vanishes away from the origin; when `f` is continuous at
the origin it vanishes there as well, since the origin is not isolated
(`ContinuousAt.eq_zero_of_forall_smul_eq_zero`). This is how an identity obtained
after multiplying by the variable is extended across `x = 0`.
-/

public section

open Filter Topology

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A function `f` with `x • f x = 0` for every `x` that is continuous at the origin is zero
everywhere. -/
theorem ContinuousAt.eq_zero_of_forall_smul_eq_zero {f : 𝕜 → E} (hf : ContinuousAt f 0)
    (h : ∀ x, x • f x = 0) : f = 0 := by
  have hne : ∀ x ≠ 0, f x = 0 := fun x hx => (smul_eq_zero.mp (h x)).resolve_left hx
  funext x
  rcases eq_or_ne x 0 with rfl | hx
  · have hev : ∀ᶠ y in 𝓝[≠] (0 : 𝕜), (0 : E) = f y :=
      eventually_nhdsWithin_of_forall fun y hy => (hne y hy).symm
    exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' hev)
  · exact hne x hx
