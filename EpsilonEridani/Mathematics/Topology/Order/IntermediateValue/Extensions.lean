/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Topology.Order.IntermediateValue

/-!
# Extensions for preconnected sets in linear orders

Mathlib proves that a preconnected set in an order-closed linear order is order-connected
(`IsPreconnected.ordConnected`) and that a neighbourhood of a point contains a closed interval
that is itself a neighbourhood of the point (`exists_Icc_mem_subset_of_mem_nhds`). This file
combines the two:

* `IsOpen.exists_Icc_subset`: an open preconnected set containing two points contains a closed
  interval whose interior contains both.

This is the shape in which uniqueness theorems for ordinary differential equations stated on a
compact interval, such as `ODE_solution_unique_of_mem_Icc`, are applied on an open connected
domain.
-/

@[expose] public section

open Set

namespace EpsilonEridani

variable {α : Type*} [TopologicalSpace α] [LinearOrder α] [OrderTopology α] [DenselyOrdered α]
  [NoMinOrder α] [NoMaxOrder α]

/-- An open preconnected set containing two points contains a closed interval whose interior
contains both. -/
theorem _root_.IsOpen.exists_Icc_subset {s : Set α} {x y : α} (hs : IsOpen s)
    (hs' : IsPreconnected s) (hx : x ∈ s) (hy : y ∈ s) :
    ∃ a b : α, Icc a b ⊆ s ∧ x ∈ Ioo a b ∧ y ∈ Ioo a b := by
  obtain ⟨a₁, b₁, -, hn₁, hsub₁⟩ := exists_Icc_mem_subset_of_mem_nhds (hs.mem_nhds hx)
  obtain ⟨a₂, b₂, -, hn₂, hsub₂⟩ := exists_Icc_mem_subset_of_mem_nhds (hs.mem_nhds hy)
  rw [← mem_interior_iff_mem_nhds, interior_Icc] at hn₁ hn₂
  have hmin : min a₁ a₂ ∈ s := by
    rcases min_choice a₁ a₂ with h | h <;> rw [h]
    exacts [hsub₁ (left_mem_Icc.2 (hn₁.1.trans hn₁.2).le),
      hsub₂ (left_mem_Icc.2 (hn₂.1.trans hn₂.2).le)]
  have hmax : max b₁ b₂ ∈ s := by
    rcases max_choice b₁ b₂ with h | h <;> rw [h]
    exacts [hsub₁ (right_mem_Icc.2 (hn₁.1.trans hn₁.2).le),
      hsub₂ (right_mem_Icc.2 (hn₂.1.trans hn₂.2).le)]
  exact ⟨_, _, hs'.ordConnected.out hmin hmax,
    ⟨(min_le_left _ _).trans_lt hn₁.1, hn₁.2.trans_le (le_max_left _ _)⟩,
    ⟨(min_le_right _ _).trans_lt hn₂.1, hn₂.2.trans_le (le_max_right _ _)⟩⟩

end EpsilonEridani
