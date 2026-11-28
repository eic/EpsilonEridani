/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Data.Multiset.AddSub

/-!
# Differences of multisets of equal cardinality

A multiset `s` that differs from a multiset `t` of at most its cardinality contains an element,
counted with multiplicity, that `t` lacks: `s - t` is nonempty
(`Multiset.exists_mem_sub_of_card_le_of_ne`). Applied in both directions to two different
multisets of the same cardinality, this is the form in which an exchange argument compares two
sub-multisets of a fixed size.
-/

public section

namespace Multiset

variable {α : Type*} [DecidableEq α]

/-- A multiset `s` different from a multiset `t` of at most its cardinality has an element,
counted with multiplicity, that `t` lacks. -/
theorem exists_mem_sub_of_card_le_of_ne {s t : Multiset α} (h : card t ≤ card s) (hne : s ≠ t) :
    ∃ a, a ∈ s - t :=
  exists_mem_of_ne_zero fun h₀ => hne <|
    eq_of_le_of_card_le (by simpa [h₀] using Multiset.le_sub_add (s := s) (t := t)) h

end Multiset
