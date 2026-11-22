/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# The trace of a unitary matrix

The trace of a unitary `n × n` matrix has norm at most `n`. The bound is attained by the
identity.

This is the bound behind the statement that a normalised trace `(1 / n) Re Tr U` of a unitary
matrix lies in `[-1, 1]`, which is how the colour-dipole operator of a Wilson-line
configuration is bounded.

## Main results

- `Matrix.norm_trace_le_card_of_mem_unitaryGroup`: `‖Tr U‖ ≤ n` for unitary `U`.
-/

public section

namespace Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- The trace of a unitary matrix has norm at most the dimension. -/
theorem norm_trace_le_card_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) : ‖U.trace‖ ≤ Fintype.card n :=
  calc ‖U.trace‖ ≤ ∑ i, ‖U i i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : n, (1 : ℝ) := Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hU i i
    _ = Fintype.card n := by simp

end Matrix
