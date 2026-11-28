/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Data.Multiset.AddSub
public import EpsilonEridani.Mathematics.Data.Multiset.Sort
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Basic.Real.Basic

/-!
# The most energetic particles of a final state

The `k` most energetic particles `leadingParticles E k s` of a final state `s : Multiset V`, as
measured by an energy function `E : V → ℝ`, are the first `k` of its particles sorted by decreasing
energy (`Multiset.sortOn` with values in the order dual `ℝᵒᵈ`). Particles of equal energy at the
boundary of the leading set are chosen in an unspecified way, so the leading set is characterised
only up to such ties:

* it is a sub-multiset of `s` (`leadingParticles_le`) of `min k (card s)` particles
  (`card_leadingParticles`), so a final state of at most `k` particles is its own leading set
  (`leadingParticles_of_card_le`);
* every leading particle is at least as energetic as every particle outside it
  (`le_of_mem_leadingParticles`);
* it is determined uniquely when the energies separate it strictly from the rest
  (`leadingParticles_eq_of_lt`).

Observables built from the leading particles, such as the invariant mass of the two leading
particles, are the subject of `EpsilonEridani.QFT.Jets.Observable.Counterexamples`.
-/

public section

namespace EpsilonEridani.QFT.Jets

variable {V : Type*}

/-- The `k` most energetic particles of a final state, as measured by an energy function `E`: the
first `k` of its particles sorted by decreasing energy. A final state of at most `k` particles is
its own leading set (`leadingParticles_of_card_le`); between particles of equal energy at the
boundary of the leading set the choice is unspecified, and it is determined whenever the energies
separate the leading particles strictly from the rest (`leadingParticles_eq_of_lt`). -/
noncomputable def leadingParticles (E : V → ℝ) (k : ℕ) (s : Multiset V) : Multiset V :=
  ((s.sortOn fun p => OrderDual.toDual (E p)).take k : List V)

theorem leadingParticles_def (E : V → ℝ) (k : ℕ) (s : Multiset V) :
    leadingParticles E k s = ((s.sortOn fun p => OrderDual.toDual (E p)).take k : List V) :=
  (rfl)

/-- The leading particles of a final state are a sub-multiset of it. -/
theorem leadingParticles_le (E : V → ℝ) (k : ℕ) (s : Multiset V) :
    leadingParticles E k s ≤ s := by
  conv_rhs => rw [← Multiset.sortOn_eq (fun p => OrderDual.toDual (E p)) s]
  exact Multiset.coe_le.2 (List.take_sublist k _).subperm

/-- There are `k` leading particles, or all of them if the final state has fewer than `k`. -/
@[simp]
theorem card_leadingParticles (E : V → ℝ) (k : ℕ) (s : Multiset V) :
    Multiset.card (leadingParticles E k s) = min k (Multiset.card s) := by
  simp [leadingParticles_def]

/-- A final state of at most `k` particles is its own set of `k` leading particles. -/
theorem leadingParticles_of_card_le {E : V → ℝ} {k : ℕ} {s : Multiset V}
    (h : Multiset.card s ≤ k) : leadingParticles E k s = s :=
  Multiset.eq_of_le_of_card_le (leadingParticles_le E k s) (by simp [h])

/-- The empty final state has no leading particles. -/
@[simp]
theorem leadingParticles_zero_right (E : V → ℝ) (k : ℕ) : leadingParticles E k 0 = 0 :=
  leadingParticles_of_card_le (by simp)

/-- No particle is among the `0` most energetic ones. -/
@[simp]
theorem leadingParticles_zero_left (E : V → ℝ) (s : Multiset V) : leadingParticles E 0 s = 0 :=
  Multiset.card_eq_zero.1 (by simp)

section DecidableEq

variable [DecidableEq V]

/-- The particles outside the leading set are the remaining particles in order of decreasing
energy. -/
private theorem sub_leadingParticles (E : V → ℝ) (k : ℕ) (s : Multiset V) :
    s - leadingParticles E k s = ((s.sortOn fun p => OrderDual.toDual (E p)).drop k : List V) := by
  have h := congrArg ((↑) : List V → Multiset V)
    (List.take_append_drop k (s.sortOn fun p => OrderDual.toDual (E p)))
  rw [← Multiset.coe_add, Multiset.sortOn_eq] at h
  rw [leadingParticles_def]
  conv_lhs => arg 1; rw [← h]
  exact add_tsub_cancel_left _ _

/-- Every leading particle is at least as energetic as every particle outside the leading set. -/
theorem le_of_mem_leadingParticles {E : V → ℝ} {k : ℕ} {s : Multiset V} {a b : V}
    (ha : a ∈ leadingParticles E k s) (hb : b ∈ s - leadingParticles E k s) : E b ≤ E a := by
  rw [sub_leadingParticles, Multiset.mem_coe] at hb
  rw [leadingParticles_def, Multiset.mem_coe] at ha
  have := Multiset.pairwise_sortOn (fun p => OrderDual.toDual (E p)) s
  rw [← List.take_append_drop k (s.sortOn _), List.pairwise_append] at this
  exact OrderDual.toDual_le_toDual.1 (this.2.2 a ha b hb)

/-- The leading particles are determined when the energies separate them strictly: a sub-multiset
`t` of `k` particles of `s`, each strictly more energetic than every particle of `s - t`, is the
set of `k` leading particles of `s`. -/
theorem leadingParticles_eq_of_lt {E : V → ℝ} {k : ℕ} {s t : Multiset V} (ht : t ≤ s)
    (hk : Multiset.card t = k) (hlt : ∀ a ∈ t, ∀ b ∈ s - t, E b < E a) :
    leadingParticles E k s = t := by
  set u := leadingParticles E k s with hu
  have hcard : Multiset.card u = Multiset.card t := by
    rw [hu, card_leadingParticles, ← hk, min_eq_left (Multiset.card_le_card ht)]
  by_contra hne
  -- Each of `u` and `t` has a member the other lacks.
  obtain ⟨a, ha⟩ := Multiset.exists_mem_sub_of_card_eq_of_ne hcard hne
  obtain ⟨b, hb⟩ := Multiset.exists_mem_sub_of_card_eq_of_ne hcard.symm (Ne.symm hne)
  -- `a` is leading and `b` is not, so `E b ≤ E a`; `b ∈ t` and `a ∉ t`, so `E a < E b`.
  have hba : E b ≤ E a :=
    le_of_mem_leadingParticles (Multiset.mem_of_le (Multiset.sub_le_self _ _) ha)
    (Multiset.mem_of_le (tsub_le_tsub_right ht u) hb)
  have hab : E a < E b := hlt b (Multiset.mem_of_le (Multiset.sub_le_self _ _) hb) a
    (Multiset.mem_of_le (tsub_le_tsub_right (leadingParticles_le E k s) t) ha)
  exact hab.not_ge hba

end DecidableEq

end EpsilonEridani.QFT.Jets
