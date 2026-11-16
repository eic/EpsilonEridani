/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Order.Group.Abs

/-!
# Extensions of the absolute value in a linearly ordered additive group

For `0 < a` and `-c < b ≤ c`, `|a - b| < a + c` (`abs_sub_lt_add_of_pos_of_neg_lt_of_le`). It is
the bound that places a null four-vector of energy `a` along an axis and a four-vector of energy
`c` and momentum `b` against it inside the forward cone of their sum along that axis.
-/

public section

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- `|a - b| < a + c` for `0 < a` and `-c < b ≤ c`. -/
theorem abs_sub_lt_add_of_pos_of_neg_lt_of_le {a b c : α} (ha : 0 < a) (hb : -c < b)
    (hbc : b ≤ c) : |a - b| < a + c := by
  refine abs_sub_lt_iff.2 ⟨?_, ?_⟩
  · rw [sub_eq_add_neg]
    exact add_lt_add_right (neg_lt.1 hb) a
  · calc b - a < b := sub_lt_self b ha
      _ ≤ c := hbc
      _ < a + c := lt_add_of_pos_left c ha
