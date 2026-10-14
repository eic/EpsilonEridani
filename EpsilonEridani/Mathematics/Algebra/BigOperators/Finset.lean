/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card

/-!
# Sums over ordered pairs of distinct indices

Extensions of `Mathlib.Algebra.BigOperators.Group.Finset.Basic`: the sum of a constant over the
ordered pairs `(j, k)` of distinct indices of a `Fintype`, written as the double sum
`∑ j, ∑ k ∈ univ.erase j`, is the number of such pairs times the constant
(`sum_univ_sum_erase_const`); in a commutative ring this is `M (M - 1)` times the constant with
the subtraction in the ring, where `M = Fintype.card ι` (`sum_univ_sum_erase_const'`).
-/

public section

open Finset

namespace EpsilonEridani

/-- The sum of a constant over the ordered pairs of distinct indices of a `Fintype` is the
number `Fintype.card ι * (Fintype.card ι - 1)` of such pairs times the constant. -/
theorem sum_univ_sum_erase_const {ι : Type*} [Fintype ι] [DecidableEq ι] {M : Type*}
    [AddCommMonoid M] (c : M) :
    ∑ j : ι, ∑ _ ∈ univ.erase j, c = (Fintype.card ι * (Fintype.card ι - 1)) • c := by
  calc ∑ j : ι, ∑ _ ∈ univ.erase j, c
      = ∑ j : ι, (Fintype.card ι - 1 : ℕ) • c := Finset.sum_congr rfl fun j _ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ j), Finset.card_univ]
    _ = (Fintype.card ι * (Fintype.card ι - 1)) • c := by
        rw [Finset.sum_nsmul_assoc, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul]

/-- In a commutative ring, the sum of a constant over the ordered pairs of distinct indices
of a `Fintype` is `M (M - 1)` times the constant, with the subtraction in the ring, where
`M = Fintype.card ι`. -/
theorem sum_univ_sum_erase_const' {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*}
    [CommRing R] (c : R) :
    ∑ j : ι, ∑ _ ∈ univ.erase j, c = Fintype.card ι * (Fintype.card ι - 1) * c := by
  rw [sum_univ_sum_erase_const, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  · rw [Nat.cast_mul, Nat.cast_pred h]

end EpsilonEridani
