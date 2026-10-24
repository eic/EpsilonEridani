/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# The determinant of a 4 × 4 matrix

Mathlib expands the determinant of matrices up to `3 × 3` explicitly (`Matrix.det_fin_three`).
This file adds the `4 × 4` case, written as the cofactor expansion along the first row with each
`3 × 3` minor expanded along its first row. On `ℝ⁴` this evaluates the volume form
`Matrix.detRowAlternating`, the Levi-Civita tensor `ε_{μνρσ}`.

## Main results

- `Matrix.det_fin_four`: the determinant of a `4 × 4` matrix in terms of its entries.
- `Matrix.detRowAlternating_fin_four`: the same expansion for `detRowAlternating` applied to four
  rows.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- Determinant of a `4 × 4` matrix, by cofactor expansion along the first row. -/
theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    det A =
      A 0 0 * (A 1 1 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 1 * A 3 3 - A 2 3 * A 3 1)
          + A 1 3 * (A 2 1 * A 3 2 - A 2 2 * A 3 1))
        - A 0 1 * (A 1 0 * (A 2 2 * A 3 3 - A 2 3 * A 3 2) - A 1 2 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
          + A 1 3 * (A 2 0 * A 3 2 - A 2 2 * A 3 0))
        + A 0 2 * (A 1 0 * (A 2 1 * A 3 3 - A 2 3 * A 3 1) - A 1 1 * (A 2 0 * A 3 3 - A 2 3 * A 3 0)
          + A 1 3 * (A 2 0 * A 3 1 - A 2 1 * A 3 0))
        - A 0 3 * (A 1 0 * (A 2 1 * A 3 2 - A 2 2 * A 3 1) - A 1 1 * (A 2 0 * A 3 2 - A 2 2 * A 3 0)
          + A 1 2 * (A 2 0 * A 3 1 - A 2 1 * A 3 0)) := by
  rw [det_succ_row_zero]
  simp (disch := decide) [Fin.sum_univ_succ, det_fin_three, Fin.succAbove_of_castSucc_lt,
    Fin.succAbove_of_le_castSucc]
  ring

/-- The determinant of four rows `v 0, …, v 3`, as the alternating map `detRowAlternating`,
by cofactor expansion along the first row. -/
theorem detRowAlternating_fin_four (v : Fin 4 → Fin 4 → R) :
    detRowAlternating v =
      v 0 0 * (v 1 1 * (v 2 2 * v 3 3 - v 2 3 * v 3 2) - v 1 2 * (v 2 1 * v 3 3 - v 2 3 * v 3 1)
          + v 1 3 * (v 2 1 * v 3 2 - v 2 2 * v 3 1))
        - v 0 1 * (v 1 0 * (v 2 2 * v 3 3 - v 2 3 * v 3 2) - v 1 2 * (v 2 0 * v 3 3 - v 2 3 * v 3 0)
          + v 1 3 * (v 2 0 * v 3 2 - v 2 2 * v 3 0))
        + v 0 2 * (v 1 0 * (v 2 1 * v 3 3 - v 2 3 * v 3 1) - v 1 1 * (v 2 0 * v 3 3 - v 2 3 * v 3 0)
          + v 1 3 * (v 2 0 * v 3 1 - v 2 1 * v 3 0))
        - v 0 3 * (v 1 0 * (v 2 1 * v 3 2 - v 2 2 * v 3 1) - v 1 1 * (v 2 0 * v 3 2 - v 2 2 * v 3 0)
          + v 1 2 * (v 2 0 * v 3 1 - v 2 1 * v 3 0)) :=
  -- `Matrix.det` is defined as `detRowAlternating`, and `Matrix.of` is the identity.
  det_fin_four (of v)

end Matrix
