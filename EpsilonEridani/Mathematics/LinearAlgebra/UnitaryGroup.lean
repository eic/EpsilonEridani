/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.RCLike.Basic

/-!
# Unitary matrices with a single row and column

A matrix indexed by a type with exactly one element is unitary iff its only entry is unitary; over
an `RCLike` field, iff that entry has norm one.

## Main results

* `Matrix.mem_unitaryGroup_iff_apply_default_mem_unitary`: a one-by-one matrix over a commutative
  star ring is unitary iff its entry is unitary.
* `Matrix.mem_unitaryGroup_iff_norm_apply_default_eq_one`: a one-by-one matrix over an `RCLike`
  field is unitary iff its entry has norm one.
-/

public section

namespace Matrix

variable {n α 𝕜 : Type*} [Fintype n] [DecidableEq n]

/-- A matrix with a single row and column is unitary iff its entry is unitary. -/
theorem mem_unitaryGroup_iff_apply_default_mem_unitary [CommRing α] [StarRing α] [Unique n]
    (S : Matrix n n α) : S ∈ unitaryGroup n α ↔ S default default ∈ unitary α := by
  rw [mem_unitaryGroup_iff', Unitary.mem_iff_star_mul_self]
  -- With one row and column, `(Sᴴ S) i j = star S₀₀ * S₀₀`.
  have hS (i j : n) : (star S * S) i j = star (S default default) * S default default := by
    rw [Subsingleton.elim i default, Subsingleton.elim j default, mul_apply, Fintype.sum_unique,
      star_apply]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← hS default default, h, one_apply_eq]
  · ext i j
    rw [hS, h, Subsingleton.elim i j, one_apply_eq]

/-- A matrix with a single row and column over an `RCLike` field is unitary iff its entry has norm
one. -/
theorem mem_unitaryGroup_iff_norm_apply_default_eq_one [RCLike 𝕜] [Unique n] (S : Matrix n n 𝕜) :
    S ∈ unitaryGroup n 𝕜 ↔ ‖S default default‖ = 1 := by
  rw [mem_unitaryGroup_iff_apply_default_mem_unitary, Unitary.mem_iff_star_mul_self,
    RCLike.star_def, RCLike.conj_mul, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]
  norm_cast

end Matrix
