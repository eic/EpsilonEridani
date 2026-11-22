/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic

/-!
# Positivity of the cast pair count

For `m ≥ 2` the number `m (m - 1)` of ordered pairs of distinct elements of an `m`-element set
is positive after the cast into any strictly ordered ring, with the subtraction taken in the
ring (`Nat.cast_mul_cast_sub_one_pos`).
-/

public section

namespace Nat

/-- For `m ≥ 2` the number `m (m - 1)` of ordered pairs of distinct elements of an `m`-element
set is positive, with the subtraction taken in a strictly ordered ring. -/
theorem cast_mul_cast_sub_one_pos {R : Type*} [Ring R] [PartialOrder R]
    [IsStrictOrderedRing R] {m : ℕ} (h : 1 < m) : (0 : R) < m * (m - 1) := by
  have h1 : (1 : R) < m := Nat.one_lt_cast.2 h
  exact mul_pos (zero_lt_one.trans h1) (sub_pos.2 h1)

end Nat
