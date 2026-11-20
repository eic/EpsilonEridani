/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Group.Units.Basic

/-!
# Solving `uⁿ a = c` for a unit `u`

Mathlib's `Units.eq_inv_mul_iff_mul_eq` solves `u a = c` as `a = u⁻¹ c` for a unit `u` of a
monoid. This file gives the version for a power `uⁿ`, with the inverse written as the power
`(u⁻¹)ⁿ` of the coerced inverse, the form in which `u⁻ⁿ` appears in a ring.

## Main statements

* `Units.eq_inv_pow_mul_iff_pow_mul_eq`: `a = (u⁻¹)ⁿ c ↔ uⁿ a = c`.
-/

@[expose] public section

namespace Units

variable {α : Type*} [Monoid α]

/-- For a unit `u`, `a = (u⁻¹)ⁿ c` exactly when `uⁿ a = c`. -/
theorem eq_inv_pow_mul_iff_pow_mul_eq (u : αˣ) (n : ℕ) {a c : α} :
    a = (↑u⁻¹ : α) ^ n * c ↔ (u : α) ^ n * a = c := by
  rw [← val_pow_eq_pow_val, ← val_pow_eq_pow_val, inv_pow]
  exact eq_inv_mul_iff_mul_eq (u ^ n)

end Units
