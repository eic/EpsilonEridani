/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Probability.Distributions.Beta

/-!
# The real Beta density

Mathlib characterises the `ℝ≥0∞`-valued Beta density `ProbabilityTheory.betaPDF` on the open unit
interval (`ProbabilityTheory.betaPDF_of_pos_lt_one`). This file records the same characterisation
for the real-valued density `ProbabilityTheory.betaPDFReal`, and its complexified form as the
integrand of Euler's beta integral `Complex.betaIntegral`:

* `EpsilonEridani.betaPDFReal_of_mem_Ioo`: `x ^ (a - 1) (1 - x) ^ (b - 1) / Β(a, b)` on `(0, 1)`.
* `EpsilonEridani.betaPDFReal_of_notMem_Ioo`: `0` off `(0, 1)`.
* `EpsilonEridani.cpow_mul_betaPDFReal_of_mem_Ioo`: `x ^ (N - 1)` times the density is
  `1 / Β(a, b)` times the integrand of `Complex.betaIntegral (N + a - 1) b`.
-/

@[expose] public section

open Set

namespace EpsilonEridani

/-- The real Beta density on the open unit interval. -/
lemma betaPDFReal_of_mem_Ioo (a b : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ProbabilityTheory.betaPDFReal a b x =
      1 / ProbabilityTheory.beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  rw [ProbabilityTheory.betaPDFReal, ite_eq_left (mem_Ioo.mp hx)]

/-- The real Beta density vanishes off the open unit interval. -/
lemma betaPDFReal_of_notMem_Ioo (a b : ℝ) {x : ℝ} (hx : x ∉ Ioo (0 : ℝ) 1) :
    ProbabilityTheory.betaPDFReal a b x = 0 := by
  rw [ProbabilityTheory.betaPDFReal, ite_eq_right (by simpa only [mem_Ioo] using hx)]

/-- On the open unit interval, `x ^ (N - 1)` times the Beta density is the normalising constant
`1 / Β(a, b)` times the integrand of Euler's beta integral `Complex.betaIntegral (N + a - 1) b`. -/
lemma cpow_mul_betaPDFReal_of_mem_Ioo (a b : ℝ) (N : ℂ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (x : ℂ) ^ (N - 1) * (ProbabilityTheory.betaPDFReal a b x : ℂ) =
      ((1 / ProbabilityTheory.beta a b : ℝ) : ℂ) *
        ((x : ℂ) ^ (N + a - 1 - 1) * (1 - (x : ℂ)) ^ ((b : ℂ) - 1)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  rw [betaPDFReal_of_mem_Ioo a b hx, Complex.ofReal_mul, Complex.ofReal_mul,
    Complex.ofReal_cpow hx.1.le, Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le), Complex.ofReal_sub,
    Complex.ofReal_one,
    show N + a - 1 - 1 = (N - 1) + ((a : ℂ) - 1) by ring, Complex.cpow_add _ _ hx0]
  push_cast
  ring

end EpsilonEridani
