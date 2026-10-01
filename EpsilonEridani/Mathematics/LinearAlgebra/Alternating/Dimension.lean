/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Alternating maps in more variables than the dimension

An alternating map in more variables than the dimension of its domain is zero. For example,
every alternating map in four variables on a space of dimension less than four vanishes, so a
Levi-Civita contraction `ε_{μναβ}` needs four dimensions.

## Main results

- `AlternatingMap.eq_zero_of_finrank_lt_card`: an alternating map in more variables than the
  dimension of its domain is zero.
-/

@[expose] public section

namespace AlternatingMap

variable {K M N ι : Type*} [Ring K] [IsDomain K] [StrongRankCondition K] [AddCommGroup M]
  [Module K M] [AddCommGroup N] [Module K N] [Module.IsTorsionFree K N] [Fintype ι]

/-- An alternating map in more variables than the dimension of its domain is zero. -/
theorem eq_zero_of_finrank_lt_card [Module.Finite K M] (f : M [⋀^ι]→ₗ[K] N)
    (h : Module.finrank K M < Fintype.card ι) : f = 0 := by
  ext v
  exact f.map_linearDependent v fun hv => (hv.fintype_card_le_finrank.trans_lt h).false

end AlternatingMap
