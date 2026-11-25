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
for the real-valued density `ProbabilityTheory.betaPDFReal`:

* `EpsilonEridani.betaPDFReal_of_mem_Ioo`: `x ^ (a - 1) (1 - x) ^ (b - 1) / Β(a, b)` on `(0, 1)`;
  `EpsilonEridani.betaPDFReal_eqOn_Ioo`: the same as an equality of functions on `(0, 1)`, with
  the kernel `x ^ (a - 1) (1 - x) ^ (b - 1)` grouped, the form in which integral transforms of
  the density reduce to those of the kernel.
* `EpsilonEridani.ofReal_beta`: the normalising constant `Β(a, b)`, cast to `ℂ`, is
  `Γ(a) Γ(b) / Γ(a + b)` with the complex Gamma function.
-/

@[expose] public section

open Set

namespace EpsilonEridani

/-- The real Beta density on the open unit interval. -/
lemma betaPDFReal_of_mem_Ioo (a b : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ProbabilityTheory.betaPDFReal a b x =
      1 / ProbabilityTheory.beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  rw [ProbabilityTheory.betaPDFReal, ite_eq_left (mem_Ioo.mp hx)]

/-- On the open unit interval the real Beta density is `1 / Β(a, b)` times the Beta kernel
`x ^ (a - 1) (1 - x) ^ (b - 1)`. -/
lemma betaPDFReal_eqOn_Ioo (a b : ℝ) :
    EqOn (ProbabilityTheory.betaPDFReal a b)
      (fun x => 1 / ProbabilityTheory.beta a b * (x ^ (a - 1) * (1 - x) ^ (b - 1))) (Ioo 0 1) :=
  fun x hx => by rw [betaPDFReal_of_mem_Ioo a b hx, mul_assoc]

/-- The normalising constant of the Beta distribution, cast to `ℂ`, is the complex Gamma ratio
`Γ(a) Γ(b) / Γ(a + b)`. -/
lemma ofReal_beta (a b : ℝ) :
    (ProbabilityTheory.beta a b : ℂ) =
      Complex.Gamma a * Complex.Gamma b / Complex.Gamma (a + b) := by
  rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ProbabilityTheory.beta, Complex.ofReal_div, Complex.ofReal_mul]

end EpsilonEridani
