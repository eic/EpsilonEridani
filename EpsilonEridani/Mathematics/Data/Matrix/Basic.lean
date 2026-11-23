/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Data.Matrix.Basic

/-!
# Powers of a matrix with an unmixed row

If the off-diagonal entries of row `i` of a square matrix `A` vanish, then row `i` of every power
`A ^ k` is `A i i ^ k` on the diagonal and zero elsewhere
(`Matrix.pow_apply_of_row_apply_eq_zero_of_ne`). This is the algebraic input to the entrywise
computation of the matrix exponential of such a matrix.
-/

public section

namespace Matrix

variable {m R : Type*} [Fintype m] [DecidableEq m] [Semiring R]

/-- If the off-diagonal entries of row `i` of `A` vanish, row `i` of `A ^ k` is `A i i ^ k` on
the diagonal and zero elsewhere. -/
theorem pow_apply_of_row_apply_eq_zero_of_ne {A : Matrix m m R} {i : m}
    (h : ∀ j, j ≠ i → A i j = 0) (k : ℕ) (j : m) :
    (A ^ k) i j = if i = j then A i i ^ k else 0 := by
  induction k generalizing j with
  | zero => rw [pow_zero, pow_zero, Matrix.one_apply]
  | succ k ih =>
    -- only the diagonal entry of row `i` of `A` contributes to row `i` of `A * A ^ k`
    have hrow (l : m) (_ : l ∈ Finset.univ) (hl : l ≠ i) : A i l * (A ^ k) l j = 0 := by
      rw [h l hl, zero_mul]
    have hmul : (A * A ^ k) i j = A i i * (A ^ k) i j :=
      Matrix.mul_apply.trans (Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hrow)
    rw [pow_succ' A k, hmul, ih, mul_ite, mul_zero, pow_succ' (A i i) k]

end Matrix
