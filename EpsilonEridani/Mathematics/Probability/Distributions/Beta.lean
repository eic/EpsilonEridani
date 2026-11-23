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

* `EpsilonEridani.betaPDFReal_of_mem_Ioo`: `x ^ (a - 1) (1 - x) ^ (b - 1) / Β(a, b)` on `(0, 1)`.
-/

@[expose] public section

open Set

namespace EpsilonEridani

/-- The real Beta density on the open unit interval. -/
lemma betaPDFReal_of_mem_Ioo (a b : ℝ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    ProbabilityTheory.betaPDFReal a b x =
      1 / ProbabilityTheory.beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1) := by
  rw [ProbabilityTheory.betaPDFReal, ite_eq_left (mem_Ioo.mp hx)]

end EpsilonEridani
