/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Products of lists of functions on `Fin n` in a group

Two identities for the product of a list `List.ofFn f` in a (not necessarily commutative) group:
a telescoping product of factors `aᵢ Aᵢ aᵢ₊₁⁻¹`, and the inverse of a product as the product of
the inverses in reversed order.

## Main results

- `List.prod_ofFn_mul_mul_inv`: a product `∏ᵢ aᵢ Aᵢ (aᵢ₊₁)⁻¹` telescopes to
  `a₀ (∏ᵢ Aᵢ) (a (Fin.last k))⁻¹`.
- `List.prod_ofFn_inv_rev`: the product of the `(f i.rev)⁻¹` is the inverse of the product of
  the `f i`.
-/

public section

namespace List

/-- Telescoping of a product `∏ᵢ aᵢ Aᵢ (aᵢ₊₁)⁻¹` in a group: every `aᵢ` but the first and the
last cancels against its inverse, leaving the product of the `Aᵢ` sandwiched between `a 0` and
`(a (Fin.last k))⁻¹`. -/
lemma prod_ofFn_mul_mul_inv {G : Type*} [Group G] :
    ∀ {k : ℕ} (a : Fin (k + 1) → G) (A : Fin k → G),
      (List.ofFn fun i => a i.castSucc * A i * (a i.succ)⁻¹).prod =
        a 0 * (List.ofFn A).prod * (a (Fin.last k))⁻¹
  | 0, a, A => by simp
  | k + 1, a, A => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    simp only [← Fin.succ_castSucc]
    rw [prod_ofFn_mul_mul_inv (fun j => a j.succ) (fun j => A j.succ)]
    simp only [Fin.succ_zero_eq_one, Fin.succ_last, Fin.castSucc_zero, mul_assoc,
      inv_mul_cancel_left]

/-- The inverse of a product in a group is the product of the inverses in reversed order,
stated for the list `List.ofFn f`. -/
lemma prod_ofFn_inv_rev {G : Type*} [Group G] :
    ∀ {n : ℕ} (f : Fin n → G), (List.ofFn fun i => (f i.rev)⁻¹).prod = (List.ofFn f).prod⁻¹
  | 0, f => by simp
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ', List.prod_concat, _root_.mul_inv_rev]
    simp only [Fin.rev_zero, Fin.rev_succ]
    rw [← prod_ofFn_inv_rev (fun i => f i.castSucc)]

end List
