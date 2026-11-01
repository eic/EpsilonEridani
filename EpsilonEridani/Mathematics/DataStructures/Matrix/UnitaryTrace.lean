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
matrix lies in `[-1, 1]`, which is how the dipole and the higher Wilson-line correlators of a
configuration are bounded. Those correlators are real parts of traces, and the real part of a
trace is unchanged under conjugate transposition, which is how their symmetries under reversal
are proved.

## Main results

- `Matrix.norm_trace_le_card_of_mem_unitaryGroup`: `‖Tr U‖ ≤ n` for unitary `U`.
- `Matrix.abs_inv_card_mul_re_trace_le_one_of_mem_unitaryGroup`: `|(1 / n) Re Tr U| ≤ 1` for
  unitary `U`.
- `Matrix.re_trace_conjTranspose`: `Re Tr Aᴴ = Re Tr A`.
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

/-- The real part of the normalised trace `(1 / n) Tr U` of a unitary `n × n` matrix lies in
`[-1, 1]`. For `n = 0` the normalised trace is `0`. -/
theorem abs_inv_card_mul_re_trace_le_one_of_mem_unitaryGroup {U : Matrix n n 𝕜}
    (hU : U ∈ unitaryGroup n 𝕜) :
    |(Fintype.card n : ℝ)⁻¹ * RCLike.re U.trace| ≤ 1 := by
  rcases isEmpty_or_nonempty n with h | h
  · simp
  · rw [abs_mul, abs_inv, Nat.abs_cast, inv_mul_le_iff₀ (by exact_mod_cast Fintype.card_pos),
      mul_one]
    exact (RCLike.abs_re_le_norm _).trans (norm_trace_le_card_of_mem_unitaryGroup hU)

omit [DecidableEq n] in
/-- The real part of the trace of a matrix is unchanged under conjugate transposition. -/
theorem re_trace_conjTranspose (A : Matrix n n 𝕜) : RCLike.re Aᴴ.trace = RCLike.re A.trace := by
  rw [trace_conjTranspose, RCLike.star_def, RCLike.conj_re]

end Matrix
