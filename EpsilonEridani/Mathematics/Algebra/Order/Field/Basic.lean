/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# Extensions of linearly ordered fields

A quotient `x / y` with `|x| < |y|` lies in `(-1, 1)` (`div_mem_Ioo_neg_one_one_of_abs_lt_abs`), the
domain on which `Real.artanh` inverts `Real.tanh`.
-/

public section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- If `|x| < |y|`, then `x / y ∈ (-1, 1)`. -/
theorem div_mem_Ioo_neg_one_one_of_abs_lt_abs {x y : α} (h : |x| < |y|) :
    x / y ∈ Set.Ioo (-1) 1 := by
  rw [Set.mem_Ioo, ← abs_lt, abs_div, div_lt_one ((abs_nonneg x).trans_lt h)]
  exact h
