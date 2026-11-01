/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import TauCeti.Algebra.BigOperators.Finset.OffDiagonal

/-!
# Off-diagonal sums of a constant

Continues `TauCeti.Algebra.BigOperators.Finset.OffDiagonal`, which treats the off-diagonal sum
`∑ j ∈ s, ∑ k ∈ s.erase j` over the ordered pairs `(j, k)` of distinct elements of a `Finset s`.
The off-diagonal sum of a constant is the number `#s * (#s - 1)` of such pairs times the constant
(`Finset.sum_sum_erase_const`); in a not-necessarily-associative ring this is `M (M - 1)` times
the constant with the subtraction in the ring, where `M = #s` (`Finset.sum_sum_erase_const'`).
When `M ≥ 2` the pair count `M (M - 1)` is positive in any strictly ordered ring
(`Nat.cast_mul_cast_sub_one_pos`).
-/

public section

namespace Finset

/-- The sum of a constant over the ordered pairs of distinct indices of a `Finset` is the
number `#s * (#s - 1)` of such pairs times the constant. -/
theorem sum_sum_erase_const {ι : Type*} [DecidableEq ι] {M : Type*}
    [AddCommMonoid M] (s : Finset ι) (c : M) :
    ∑ j ∈ s, ∑ _ ∈ s.erase j, c = (#s * (#s - 1)) • c := by
  calc ∑ j ∈ s, ∑ _ ∈ s.erase j, c
      = ∑ j ∈ s, (#s - 1 : ℕ) • c := sum_congr rfl fun j hj => by
        rw [sum_const, card_erase_of_mem hj]
    _ = (#s * (#s - 1)) • c := by
        rw [sum_nsmul_assoc, sum_const, Nat.nsmul_eq_mul]

/-- In a not-necessarily-associative ring, the sum of a constant over the ordered pairs of
distinct indices of a `Finset` is `M (M - 1)` times the constant, with the subtraction in the
ring, where `M = #s`. -/
theorem sum_sum_erase_const' {ι : Type*} [DecidableEq ι] {R : Type*}
    [NonAssocRing R] (s : Finset ι) (c : R) :
    ∑ j ∈ s, ∑ _ ∈ s.erase j, c = #s * (#s - 1) * c := by
  rw [sum_sum_erase_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos #s with h | h
  · simp [h]
  · rw [Nat.cast_mul, Nat.cast_pred h]

end Finset

/-- For `m ≥ 2` the number `m (m - 1)` of ordered pairs of distinct elements of an `m`-element
set is positive, with the subtraction taken in a strictly ordered ring. -/
theorem Nat.cast_mul_cast_sub_one_pos {R : Type*} [Ring R] [PartialOrder R]
    [IsStrictOrderedRing R] {m : ℕ} (h : 1 < m) : (0 : R) < m * (m - 1) := by
  have h1 : (1 : R) < m := Nat.one_lt_cast.2 h
  exact mul_pos (zero_lt_one.trans h1) (sub_pos.2 h1)
