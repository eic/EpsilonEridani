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

A matrix indexed by a type with exactly one element is unitary iff its only entry has norm one.

## Main results

* `Matrix.mem_unitaryGroup_iff_norm_apply_default_eq_one`: a one-by-one matrix over an `RCLike`
  field is unitary iff its entry has norm one.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- A matrix with a single row and column is unitary iff its entry has norm one. -/
theorem mem_unitaryGroup_iff_norm_apply_default_eq_one [Unique n] (S : Matrix n n 𝕜) :
    S ∈ unitaryGroup n 𝕜 ↔ ‖S default default‖ = 1 := by
  rw [mem_unitaryGroup_iff']
  -- With one row and column, `(Sᴴ S) i j = ‖S₀₀‖²`.
  have hS (i j : n) : (star S * S) i j = ((‖S default default‖ ^ 2 : ℝ) : 𝕜) := by
    rw [Subsingleton.elim i default, Subsingleton.elim j default, mul_apply, Fintype.sum_unique,
      star_apply, RCLike.star_def, RCLike.conj_mul, RCLike.ofReal_pow]
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← RCLike.ofReal_inj (K := 𝕜),
    RCLike.ofReal_one, ← hS default default, ← one_apply_eq (α := 𝕜) (default : n)]
  refine ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
  ext i j
  rw [hS, Subsingleton.elim i default, Subsingleton.elim j default, ← h, hS]

end Matrix
