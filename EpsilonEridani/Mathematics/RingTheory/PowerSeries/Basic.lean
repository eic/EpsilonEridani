/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficients of a product with a power series divisible by a power of `X`

When `β` is divisible by `X ^ k`, its coefficients of `X⁰, …, X^{k-1}` vanish, so the Cauchy
product formula for the coefficient of `X ^ (n + k)` in `f * β` only involves the coefficients
of `β` from `X ^ k` on.

## Main statements

* `PowerSeries.coeff_add_mul_of_X_pow_dvd`:
  `[X^{n+k}] (f * β) = ∑_{i+j=n} [X^i] f [X^{j+k}] β` when `X ^ k ∣ β`.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [CommSemiring R]

/-- The coefficient of `X ^ (n + k)` in `f * β`, for `β` divisible by `X ^ k`, as a Cauchy
product `∑_{i+j=n} [X^i] f [X^{j+k}] β`: the coefficients of `X⁰, …, X^{k-1}` of `β` vanish. -/
theorem coeff_add_mul_of_X_pow_dvd {k : ℕ} {β : R⟦X⟧} (hβ : X ^ k ∣ β) (f : R⟦X⟧) (n : ℕ) :
    coeff (n + k) (f * β) =
      ∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff (p.2 + k) β := by
  obtain ⟨γ, rfl⟩ := hβ
  rw [mul_left_comm, coeff_X_pow_mul, coeff_mul]
  simp only [coeff_X_pow_mul]

end PowerSeries
