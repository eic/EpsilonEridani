/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Mathematics.KroneckerDelta.Contraction
public import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Contraction of the generalized Kronecker delta over an arbitrary finite type

Extensions of `Physlib.Mathematics.KroneckerDelta.Contraction`. Its iterated contraction
identities `sum_generalizedKroneckerDelta_self`, `sum_generalizedKroneckerDelta_cons` and
`sum_generalizedKroneckerDelta_cons₂` are stated over the index type `Fin 4`. The same
identities hold over any finite index type `α`, with `Fintype.card α` in place of `4`, by the
same induction on the one-step contraction `generalizedKroneckerDelta_sum_snoc`: contracting
`k` index pairs multiplies by the falling product `(card α - m) (card α - m - 1) ⋯` where `m`
is the number of free pairs. When the index type has exactly `k` elements, the full contraction
is `k!`.

This module mirrors the Physlib module it extends so that it can move there without renaming.
-/

@[expose] public section

open KroneckerDelta

open Matrix

section Generalized

variable {α : Type} [DecidableEq α] [Fintype α]

/-- Split a sum over `(k+1)`-tuples into the initial `k`-tuple and the last entry. -/
private lemma sum_over_snoc {X : Type*} [Fintype X] {M : Type*} [AddCommMonoid M] {k : ℕ}
    (F : (Fin (k + 1) → X) → M) :
    ∑ h : Fin (k + 1) → X, F h = ∑ h' : Fin k → X, ∑ c : X, F (Fin.snoc h' c) := by
  rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ => X)) F, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- **Full contraction over an arbitrary finite type.** Summing `δ^{h}_{h}` over all `k`-tuples
`h` of indices gives the falling product `card α · (card α - 1) ⋯ (card α - k + 1)`. This is
`sum_generalizedKroneckerDelta_self` with `Fintype.card α` in place of `4`. -/
lemma sum_generalizedKroneckerDelta_self_card (k : ℕ) :
    ∑ h : Fin k → α, generalizedKroneckerDelta h h
      = ∏ j ∈ Finset.range k, ((Fintype.card α : ℤ) - j) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, Fintype.sum_unique]
    exact Matrix.det_fin_zero
  | succ k ih =>
    rw [sum_over_snoc]
    have hstep : ∀ h' : Fin k → α, ∑ c : α,
        generalizedKroneckerDelta (Fin.snoc h' c) (Fin.snoc h' c)
          = ((Fintype.card α : ℤ) - k) * generalizedKroneckerDelta h' h' :=
      fun h' => generalizedKroneckerDelta_sum_snoc h' h'
    rw [Finset.sum_congr rfl fun h' _ => hstep h', ← Finset.mul_sum, ih,
      Finset.prod_range_succ]
    ring

/-- **Single contraction over an arbitrary finite type.** Contracting the last `k` of `k+1`
index pairs leaves one free pair `σ, τ`, with the falling product
`(card α - 1) (card α - 2) ⋯`. This is `sum_generalizedKroneckerDelta_cons` with
`Fintype.card α` in place of `4`. -/
lemma sum_generalizedKroneckerDelta_cons_card (σ τ : α) (k : ℕ) :
    ∑ h : Fin k → α,
        generalizedKroneckerDelta (Fin.cons σ h) (Fin.cons τ h)
      = (∏ j ∈ Finset.range k, ((Fintype.card α : ℤ) - 1 - j))
        * ((kroneckerDelta σ τ : ℕ) : ℤ) := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, one_mul, Fintype.sum_unique]
    exact Matrix.det_fin_one _
  | succ k ih =>
    rw [sum_over_snoc]
    have hstep : ∀ h' : Fin k → α, ∑ c : α,
        generalizedKroneckerDelta (Fin.cons σ (Fin.snoc h' c)) (Fin.cons τ (Fin.snoc h' c))
          = ((Fintype.card α : ℤ) - 1 - k)
            * generalizedKroneckerDelta (Fin.cons σ h') (Fin.cons τ h') := by
      intro h'
      rw [Finset.sum_congr rfl fun c _ => by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons],
        generalizedKroneckerDelta_sum_snoc (Fin.cons σ h') (Fin.cons τ h')]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun h' _ => hstep h', ← Finset.mul_sum, ih,
      Finset.prod_range_succ]
    ring

/-- **Double contraction over an arbitrary finite type.** Contracting the last `k` of `k+2`
index pairs leaves two free pairs, with value a `2×2` generalized Kronecker delta times the
falling product `(card α - 2) (card α - 3) ⋯`. This is `sum_generalizedKroneckerDelta_cons₂`
with `Fintype.card α` in place of `4`. -/
lemma sum_generalizedKroneckerDelta_cons₂_card (ρ σ τ ω : α) (k : ℕ) :
    ∑ h : Fin k → α,
        generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ h)) (Fin.cons τ (Fin.cons ω h))
      = (∏ j ∈ Finset.range k, ((Fintype.card α : ℤ) - 2 - j))
        * generalizedKroneckerDelta ![ρ, σ] ![τ, ω] := by
  induction k with
  | zero =>
    rw [Finset.prod_range_zero, one_mul, Fintype.sum_unique]
    have e1 : ∀ d : Fin 0 → α, (Fin.cons ρ (Fin.cons σ d) : Fin 2 → α) = ![ρ, σ] := by
      intro d; funext i; fin_cases i <;> rfl
    have e2 : ∀ d : Fin 0 → α, (Fin.cons τ (Fin.cons ω d) : Fin 2 → α) = ![τ, ω] := by
      intro d; funext i; fin_cases i <;> rfl
    rw [e1, e2]
  | succ k ih =>
    rw [sum_over_snoc]
    have hstep : ∀ h' : Fin k → α, ∑ c : α,
        generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ (Fin.snoc h' c)))
          (Fin.cons τ (Fin.cons ω (Fin.snoc h' c)))
          = ((Fintype.card α : ℤ) - 2 - k)
            * generalizedKroneckerDelta (Fin.cons ρ (Fin.cons σ h'))
              (Fin.cons τ (Fin.cons ω h')) := by
      intro h'
      rw [Finset.sum_congr rfl fun c _ => by
        rw [Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons,
          Fin.cons_snoc_eq_snoc_cons, Fin.cons_snoc_eq_snoc_cons],
        generalizedKroneckerDelta_sum_snoc (Fin.cons ρ (Fin.cons σ h'))
          (Fin.cons τ (Fin.cons ω h'))]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun h' _ => hstep h', ← Finset.mul_sum, ih,
      Finset.prod_range_succ]
    ring

/-- When the index type has exactly `k` elements, the full contraction is `k!`. -/
lemma sum_generalizedKroneckerDelta_self_eq_factorial {k : ℕ} (hk : Fintype.card α = k) :
    ∑ h : Fin k → α, generalizedKroneckerDelta h h = (k.factorial : ℤ) := by
  rw [sum_generalizedKroneckerDelta_self_card, hk, ← Nat.descFactorial_self,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  refine Finset.prod_congr rfl fun j hj => ?_
  have := Finset.mem_range.mp hj
  omega

end Generalized
