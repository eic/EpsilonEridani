/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.Multiset.Basic

/-!
# Sorting a multiset by a key

`Multiset.sort` sorts a multiset by an antisymmetric total order, which makes the sorted list
independent of the list representing the multiset. Sorting by a key `f : α → β` with values in a
linear order compares elements of `α` only by a total preorder: distinct elements may share a key,
and the order in which they then appear depends on a representative. `Multiset.sortOn f s` fixes
the representative noncomputably, through `Multiset.toList`, and sorts it by increasing key. Sort
by a decreasing key by taking `f` with values in an order dual.

## Main declarations

* `Multiset.sortOn f s`: the elements of `s` as a list sorted by increasing `f`.
* `Multiset.sortOn_eq`: the list `Multiset.sortOn f s` represents `s`.
* `Multiset.pairwise_sortOn`: the keys increase along `Multiset.sortOn f s`.
-/

public section

namespace Multiset

variable {α β : Type*} [LinearOrder β]

/-- The elements of a multiset `s` as a list sorted by increasing key `f`. Elements with equal
keys appear in an unspecified order, so unlike `Multiset.sort` this is noncomputable. -/
noncomputable def sortOn (f : α → β) (s : Multiset α) : List α :=
  s.toList.mergeSort fun a b => decide (f a ≤ f b)

/-- The list `Multiset.sortOn f s` represents the multiset `s`. -/
@[simp]
theorem sortOn_eq (f : α → β) (s : Multiset α) : (s.sortOn f : Multiset α) = s := by
  rw [sortOn, coe_eq_coe.2 (List.mergeSort_perm _ _), coe_toList]

@[simp]
theorem length_sortOn (f : α → β) (s : Multiset α) : (s.sortOn f).length = card s := by
  rw [← coe_card, sortOn_eq]

@[simp]
theorem mem_sortOn {f : α → β} {s : Multiset α} {a : α} : a ∈ s.sortOn f ↔ a ∈ s := by
  rw [← mem_coe, sortOn_eq]

@[simp]
theorem sortOn_zero (f : α → β) : (0 : Multiset α).sortOn f = [] := by
  simp [sortOn]

/-- The keys increase along `Multiset.sortOn f s`. -/
theorem pairwise_sortOn (f : α → β) (s : Multiset α) :
    (s.sortOn f).Pairwise fun a b => f a ≤ f b := by
  refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp
    of_decide_eq_true
  · simp only [decide_eq_true_eq] at hab hbc ⊢
    exact hab.trans hbc
  · simpa using le_total (f a) (f b)

end Multiset
