/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Row and column norms of the identity matrix

Every row and every column of the identity matrix `1 : Matrix n n α` over a seminormed ring with
`‖1‖ = 1` has unit squared norm, `∑ j, ‖(1 : Matrix n n α) i j‖ ^ 2 = 1`. These discharge the
unit-norm row and column conditions that characterise a unitary matrix entrywise, in the case of
the identity.

## Main results

- `Matrix.sum_row_norm_sq_one_eq_one`: each row of `1` has unit squared norm.
- `Matrix.sum_col_norm_sq_one_eq_one`: each column of `1` has unit squared norm.
-/

public section

namespace Matrix

variable {n α : Type*} [Fintype n] [DecidableEq n] [SeminormedRing α] [NormOneClass α]

/-- Each row of the identity matrix has unit squared norm. -/
@[simp]
theorem sum_row_norm_sq_one_eq_one (i : n) : ∑ j, ‖(1 : Matrix n n α) i j‖ ^ 2 = 1 := by
  simp [one_apply, apply_ite (fun z : α => ‖z‖ ^ 2)]

/-- Each column of the identity matrix has unit squared norm. -/
@[simp]
theorem sum_col_norm_sq_one_eq_one (j : n) : ∑ i, ‖(1 : Matrix n n α) i j‖ ^ 2 = 1 := by
  simp [one_apply, apply_ite (fun z : α => ‖z‖ ^ 2)]

end Matrix
