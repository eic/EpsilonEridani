/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Coefficients of a product with a power series divisible by a power of `X`

When `g` is divisible by `X ^ k`, its coefficients of `X⁰, …, X^{k-1}` vanish, so the Cauchy
product formula for the coefficient of `X ^ (n + k)` in `f * g` only involves the coefficients
of `g` from `X ^ k` on.

## Main statements

* `PowerSeries.coeff_mul_of_X_pow_dvd`:
  `[X^{n+k}] (f * g) = ∑_{i+j=n} [X^i] f [X^{j+k}] g` when `X ^ k ∣ g`.
-/

@[expose] public section

namespace PowerSeries

variable {R : Type*} [Semiring R]

/-- The coefficient of `X ^ (n + k)` in `f * g`, for `g` divisible by `X ^ k`, as a Cauchy
product `∑_{i+j=n} [X^i] f [X^{j+k}] g`: the coefficients of `X⁰, …, X^{k-1}` of `g` vanish. -/
theorem coeff_mul_of_X_pow_dvd {k : ℕ} {g : R⟦X⟧} (hg : X ^ k ∣ g) (f : R⟦X⟧) (n : ℕ) :
    coeff (n + k) (f * g) =
      ∑ p ∈ Finset.antidiagonal n, coeff p.1 f * coeff (p.2 + k) g := by
  obtain ⟨γ, rfl⟩ := hg
  rw [← mul_assoc, (commute_X_pow f k).eq, mul_assoc, coeff_X_pow_mul, coeff_mul]
  simp only [coeff_X_pow_mul]

end PowerSeries
