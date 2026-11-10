/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Trace identities for matrices

This file extends `Mathlib.LinearAlgebra.Matrix.Trace` with further trace identities, in the
same spirit as that file.

Contracting a matrix `X` with a symmetric matrix `A` sees only the symmetric part of `X`:
`trace (A * Xᵀ) = trace (A * X)`. Taking the trace of a tensor with two lower indices against
a symmetric metric, as in the trace of an energy-momentum tensor, is such a contraction.

## Main results

- `Matrix.IsSymm.trace_mul_transpose`: contracting with a symmetric `A`, `trace (A * X)` only
  sees the symmetric part of `X`.
-/

public section

namespace Matrix

/-- Contracting with a symmetric matrix sees only the symmetric part of a tensor:
`trace (A * Xᵀ) = trace (A * X)` for `A` symmetric. -/
theorem IsSymm.trace_mul_transpose {n R : Type*} [Fintype n] [AddCommMonoid R] [Mul R]
    {A : Matrix n n R} (hA : A.IsSymm) (X : Matrix n n R) : trace (A * Xᵀ) = trace (A * X) := by
  conv_lhs => rw [← hA.eq]
  exact trace_transpose_mul A X

end Matrix
