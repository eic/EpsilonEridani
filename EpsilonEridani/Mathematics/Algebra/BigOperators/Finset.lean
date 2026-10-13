/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.Ring

/-!
# Sums over ordered pairs of distinct indices

Extensions of `Mathlib.Algebra.BigOperators.Group.Finset.Basic`: the sum of a constant over the
ordered pairs `(j, k)` of distinct indices of a `Fintype`, written as the double sum
`∑ j, ∑ k ∈ univ.erase j`, is `M (M - 1)` times the constant, where `M = Fintype.card ι`
(`sum_univ_sum_erase_const`).
-/

public section

open Finset

namespace EpsilonEridani

/-- The sum of a constant over the ordered pairs of distinct indices of a `Fintype` is the
number `M (M - 1)` of such pairs times the constant, where `M = Fintype.card ι`. -/
theorem sum_univ_sum_erase_const {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*}
    [CommRing R] (c : R) :
    ∑ j : ι, ∑ _ ∈ univ.erase j, c = Fintype.card ι * (Fintype.card ι - 1) * c := by
  calc ∑ j : ι, ∑ _ ∈ univ.erase j, c
      = ∑ j : ι, ((Fintype.card ι : R) - 1) * c := Finset.sum_congr rfl fun j _ => by
        rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ j), Finset.card_univ,
          nsmul_eq_mul, Nat.cast_pred (Fintype.card_pos_iff.2 ⟨j⟩)]
    _ = Fintype.card ι * (Fintype.card ι - 1) * c := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end EpsilonEridani
