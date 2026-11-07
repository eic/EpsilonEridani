/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Products from lists

`Mathlib.Algebra.BigOperators.Group.List.Basic` proves the basic identities for `List.prod` in
a group. This file sits at the path mirroring that module and extends it with the telescoping
identity for a product of conjugations. Everything here is general algebra, mentioning no type
of this repository, so the file is kept in the upstream `List` namespace with the upstream
module as its first import: it is PhyslibAlpha-eligible, and the whole file can move once it
has landed upstream.

## Main results

- `List.prod_ofFn_mul_mul_inv`: a product `∏ᵢ aᵢ Aᵢ (aᵢ₊₁)⁻¹` telescopes to
  `a₀ (∏ᵢ Aᵢ) (a (Fin.last k))⁻¹`.
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

end List
