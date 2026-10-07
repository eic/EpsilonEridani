/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Continuous functions annihilated by the identity

If `x • f x = 0` for every `x`, then `f` vanishes away from the origin; when `f` is continuous it
vanishes at the origin as well, since the origin is not isolated
(`EpsilonEridani.eq_zero_of_forall_smul_eq_zero`). This is how an identity obtained after
multiplying by the variable is extended across `x = 0`.
-/

public section

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace EpsilonEridani

/-- A continuous function `f` with `x • f x = 0` for every `x` is zero. -/
theorem eq_zero_of_forall_smul_eq_zero {f : 𝕜 → E} (hf : Continuous f)
    (h : ∀ x, x • f x = 0) : f = 0 :=
  hf.ext_on (dense_compl_singleton 0) continuous_const fun x hx =>
    (smul_eq_zero.mp (h x)).resolve_left hx

end EpsilonEridani
