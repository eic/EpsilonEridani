/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sums over ordered pairs of distinct indices

Extensions of `Mathlib.Algebra.BigOperators.Ring.Finset`: the sum of a constant over the
ordered pairs `(j, k)` of distinct indices of a `Finset s`, written as the double sum
`∑ j ∈ s, ∑ k ∈ s.erase j`, is the number `#s * (#s - 1)` of such pairs times the constant
(`sum_sum_erase_const`); in a not-necessarily-associative ring this is `M (M - 1)` times the
constant with the subtraction in the ring, where `M = #s` (`sum_sum_erase_const'`).
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
