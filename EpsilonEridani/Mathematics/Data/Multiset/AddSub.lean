/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Data.Multiset.AddSub

/-!
# Differences of multisets of equal cardinality

Two different multisets `s` and `t` of the same cardinality each contain an element, counted with
multiplicity, that the other lacks: `s - t` is nonempty
(`Multiset.exists_mem_sub_of_card_eq`). This is the form in which an exchange argument compares
two sub-multisets of a fixed size.
-/

public section

namespace Multiset

variable {α : Type*} [DecidableEq α]

/-- Two different multisets of the same cardinality: the first has an element, counted with
multiplicity, that the second lacks. -/
theorem exists_mem_sub_of_card_eq {s t : Multiset α} (h : card s = card t) (hne : s ≠ t) :
    ∃ a, a ∈ s - t :=
  exists_mem_of_ne_zero fun h₀ => hne <|
    eq_of_le_of_card_le (by simpa [h₀] using Multiset.le_sub_add (s := s) (t := t)) h.ge

end Multiset
