/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import TauCeti.Analysis.Matrix.PosSemidef


/-!
# Entrywise bounds for positive-semidefinite matrices

The principal `2 × 2` minors of a positive-semidefinite matrix `M` are nonnegative. This
file records the resulting entrywise bounds on the off-diagonal entries:

* `Matrix.PosSemidef.two_mul_norm_apply_le`: `2 * ‖M i j‖ ≤ re (M i i) + re (M j j)` over any
  `RCLike` field, the arithmetic-mean form of Tau Ceti's scalar Cauchy-Schwarz inequality
  `Matrix.PosSemidef.normSq_le`;
* `Matrix.PosSemidef.sq_apply_le`: `(M i j) ^ 2 ≤ M i i * M j j` for real `M`, the real case of
  `Matrix.PosSemidef.normSq_le`;
* `Matrix.PosSemidef.two_mul_abs_apply_le`: `2 * |M i j| ≤ M i i + M j j` for real `M`, the real
  case of `two_mul_norm_apply_le`.

(Nonnegativity of the diagonal is Mathlib's `Matrix.PosSemidef.diag_nonneg`.)

All three bounds are stated multiplied out, with no division, so that they apply without field
side conditions. This is the form in which positivity constraints are used in hadronic physics; see
`EpsilonEridani/Particles/Parton/PDF/Positivity.lean` for the Soffer bound on the quark
transversity distribution, which is exactly the arithmetic-mean inequality applied to the
parton spin-density matrix.

## Main results

- `Matrix.PosSemidef.two_mul_norm_apply_le`: the entrywise arithmetic-mean bound.
- `Matrix.PosSemidef.sq_apply_le`: the real entrywise geometric-mean bound.
- `Matrix.PosSemidef.two_mul_abs_apply_le`: the real entrywise arithmetic-mean bound.

## Implementation notes

The geometric-mean bound over `RCLike 𝕜` is Tau Ceti's `Matrix.PosSemidef.normSq_le`, of which
`sq_apply_le` is the real case. The arithmetic-mean bound is stated over `RCLike 𝕜` because a
genuinely complex density matrix needs it: the off-diagonal entries of a spin density matrix
carry the vector polarization in their imaginary parts.

These lemmas are stated for a general index type rather than for `Fin n`, and are candidates
for upstreaming to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder

variable {n : Type*}

/-- **Entrywise arithmetic-mean bound for a positive-semidefinite matrix.**
Twice the norm of an entry is bounded by the sum of the real parts of the two diagonal entries
of its row and column: the principal `2 × 2` minor on `{i, j}` is nonnegative, in the
arithmetic-mean form of the scalar Cauchy-Schwarz inequality `Matrix.PosSemidef.normSq_le`. -/
lemma PosSemidef.two_mul_norm_apply_le {𝕜 : Type*} [RCLike 𝕜] {M : Matrix n n 𝕜}
    (hM : M.PosSemidef) (i j : n) :
    2 * ‖M i j‖ ≤ RCLike.re (M i i) + RCLike.re (M j j) := by
  have h := hM.normSq_le i j
  rw [RCLike.normSq_eq_def'] at h
  have hi := (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := i))).1
  have hj := (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := j))).1
  nlinarith [norm_nonneg (M i j), sq_nonneg (RCLike.re (M i i) - RCLike.re (M j j))]

/-- **Entrywise geometric-mean bound for a real positive-semidefinite matrix.**
The square of an entry is bounded by the product of the two diagonal entries of its row and
column: the real form of the scalar Cauchy-Schwarz inequality `Matrix.PosSemidef.normSq_le`. -/
lemma PosSemidef.sq_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    M i j ^ 2 ≤ M i i * M j j := by
  simpa [RCLike.normSq_apply, sq] using hM.normSq_le i j

/-- **Entrywise arithmetic-mean bound for a real positive-semidefinite matrix.**
Twice the absolute value of an entry is bounded by the sum of the two diagonal entries of its
row and column: the real case of `Matrix.PosSemidef.two_mul_norm_apply_le`.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  simpa using hM.two_mul_norm_apply_le i j

end Matrix
