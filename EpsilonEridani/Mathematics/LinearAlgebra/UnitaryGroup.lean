/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Analysis.RCLike.Basic

/-!
# Unitary scalars and one-by-one unitary matrices

An element of an `RCLike` field is unitary iff it has norm one, and a matrix indexed by a type with
exactly one element is unitary iff its only entry is unitary. Together, a one-by-one matrix over an
`RCLike` field is unitary iff its entry has norm one.

## Main results

* `RCLike.mem_unitary_iff_norm_eq_one`: an element of an `RCLike` field is unitary iff it has norm
  one.
* `Matrix.mem_unitary_iff_apply_default_mem_unitary`: a one-by-one matrix over a star semiring is
  unitary iff its entry is unitary.
* `Matrix.mem_unitary_iff_norm_apply_default_eq_one`: a one-by-one matrix over an `RCLike` field
  is unitary iff its entry has norm one.
-/

public section

namespace RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- An element of an `RCLike` field is unitary iff it has norm one. -/
@[simp]
theorem mem_unitary_iff_norm_eq_one {x : 𝕜} : x ∈ unitary 𝕜 ↔ ‖x‖ = 1 := by
  rw [Unitary.mem_iff_star_mul_self, star_def, conj_mul,
    ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]
  norm_cast

end RCLike

namespace Matrix

variable {n R 𝕜 : Type*} [Fintype n] [DecidableEq n]

/-- A matrix with a single row and column is unitary iff its entry is unitary. -/
@[simp]
theorem mem_unitary_iff_apply_default_mem_unitary [Semiring R] [StarRing R] [Unique n]
    (S : Matrix n n R) : S ∈ unitary (Matrix n n R) ↔ S default default ∈ unitary R := by
  -- With one row and column, `S` is the diagonal matrix of its constant entry.
  have hS : S = diagonal (Function.const n (S default default)) := by
    ext i j
    rw [Subsingleton.elim i default, Subsingleton.elim j default, diagonal_apply_eq,
      Function.const_apply]
  rw [hS, diagonal_mem_unitary, Pi.const_mem_unitary_iff, diagonal_apply_eq, Function.const_apply]

/-- A matrix with a single row and column over an `RCLike` field is unitary iff its entry has norm
one. -/
theorem mem_unitary_iff_norm_apply_default_eq_one [RCLike 𝕜] [Unique n] (S : Matrix n n 𝕜) :
    S ∈ unitary (Matrix n n 𝕜) ↔ ‖S default default‖ = 1 :=
  (mem_unitary_iff_apply_default_mem_unitary S).trans RCLike.mem_unitary_iff_norm_eq_one

end Matrix
