/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Tactic.Linarith

/-!
# Extensions of the absolute value in a linearly ordered field

For `0 < a` and `-c < b ≤ c`, `|a - b| < a + c` (`abs_sub_lt_add_of_pos_of_neg_lt_of_le`). It is
the bound that places a real photon of energy `a` and a target of energy `c` and momentum `b`
against it inside the forward light cone along the beam axis.
-/

public section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

/-- `|a - b| < a + c` for `0 < a` and `-c < b ≤ c`. -/
theorem abs_sub_lt_add_of_pos_of_neg_lt_of_le {a b c : α} (ha : 0 < a) (hb : -c < b)
    (hbc : b ≤ c) : |a - b| < a + c := by
  rw [abs_lt]
  constructor <;> linarith
