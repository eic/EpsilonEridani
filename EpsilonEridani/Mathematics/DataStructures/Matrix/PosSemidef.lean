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
# Entrywise bounds for real positive-semidefinite matrices

The principal `2 × 2` minors of a real positive-semidefinite matrix `M` are nonnegative. This
file records the resulting entrywise bounds on the off-diagonal entries:

* `Matrix.PosSemidef.sq_apply_le`: `(M i j) ^ 2 ≤ M i i * M j j`, the geometric-mean form of
  the Cauchy-Schwarz inequality (the real case of Tau Ceti's `Matrix.PosSemidef.normSq_le`);
* `Matrix.PosSemidef.two_mul_abs_apply_le`: `2 * |M i j| ≤ M i i + M j j`, its arithmetic-mean
  form.

(Nonnegativity of the diagonal is Mathlib's `Matrix.PosSemidef.diag_nonneg`.)

Both bounds are stated multiplied out, with no division, so that they apply without field side
conditions. This is the form in which
positivity constraints are used in hadronic physics; see
`Physlib/Particles/Parton/PDF/Positivity.lean` for the Soffer bound on the quark transversity
distribution, which is exactly the arithmetic-mean inequality applied to the parton
spin-density matrix.

## Main results

- `Matrix.PosSemidef.sq_apply_le`: the entrywise geometric-mean bound.
- `Matrix.PosSemidef.two_mul_abs_apply_le`: the entrywise arithmetic-mean bound.

## Implementation notes

Everything here is stated over `ℝ`. `Matrix.PosSemidef` is available over more general
star-ordered rings, and the corresponding statements over `RCLike 𝕜` replace `|·|` by `‖·‖`;
that generalisation is not needed for the leading-twist positivity bounds (whose relevant
block is real) and is left to whoever first needs the T-odd, genuinely complex entries.

These lemmas are stated for a general index type rather than for `Fin n`, and are candidates
for upstreaming to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.
-/

@[expose] public section

namespace Matrix

variable {n : Type*}

/-- **Entrywise geometric-mean bound for a real positive-semidefinite matrix.**
The square of an entry is bounded by the product of the two diagonal entries of its row and
column: the real form of the scalar Cauchy-Schwarz inequality `Matrix.PosSemidef.normSq_le`. -/
lemma PosSemidef.sq_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    M i j ^ 2 ≤ M i i * M j j := by
  simpa [RCLike.normSq_apply, sq] using hM.normSq_le i j

/-- **Entrywise arithmetic-mean bound for a real positive-semidefinite matrix.**
Twice the absolute value of an entry is bounded by the sum of the two diagonal entries of its
row and column. Equivalently: the principal `2 × 2` minor on `{i, j}` is nonnegative, in the
arithmetic-mean rather than the geometric-mean form.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  have := hM.sq_apply_le i j
  have := hM.diag_nonneg (i := i)
  have := hM.diag_nonneg (i := j)
  nlinarith [abs_nonneg (M i j), sq_abs (M i j), sq_nonneg (M i i - M j j)]

end Matrix
