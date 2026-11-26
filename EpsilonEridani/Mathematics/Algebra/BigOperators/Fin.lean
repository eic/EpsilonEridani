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
the inverses in reversed order. The latter rests on the structure-free fact that reindexing
`List.ofFn f` by `Fin.rev` reverses the list.

Both are needed for traced products of Wilson lines. The telescoping identity turns a chain of
gauge-transformed factors `Ωᵢ Aᵢ Ωᵢ₊₁⁻¹` into the single two-sided factor `Ω₀ (∏ᵢ Aᵢ) Ωₖ⁻¹`, a
conjugation of the product of the `Aᵢ` when the two ends coincide, as they do for the cyclic
Wilson-line trace; this gives the gauge invariance of the Wilson-line correlators. The reversal
identity identifies the product of the inverses at reversed indices with the inverse of the
product, which for unitary factors is its Hermitian conjugate, and gives their invariance under
reversal of the order of the arguments.

## Main results

- `List.prod_ofFn_mul_mul_inv`: a product `∏ᵢ aᵢ Aᵢ (aᵢ₊₁)⁻¹` telescopes to
  `a₀ (∏ᵢ Aᵢ) (a (Fin.last k))⁻¹`.
- `List.ofFn_rev`: reindexing `List.ofFn f` by `Fin.rev` reverses the list.
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

/-- Reindexing `List.ofFn` by `Fin.rev` reverses the list. -/
lemma ofFn_rev {α : Type*} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun i => f i.rev) = (List.ofFn f).reverse :=
  List.ext_getElem (by simp) fun i h₁ h₂ => by
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    ext
    simp only [Fin.val_rev]
    omega

/-- The inverse of a product in a group is the product of the inverses in reversed order,
stated for the list `List.ofFn f`. -/
lemma prod_ofFn_inv_rev {G : Type*} [Group G] {n : ℕ} (f : Fin n → G) :
    (List.ofFn fun i => (f i.rev)⁻¹).prod = (List.ofFn f).prod⁻¹ := by
  rw [List.prod_inv_reverse, List.map_ofFn, ← List.ofFn_rev, Function.comp_def]

end List
