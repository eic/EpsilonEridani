/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.Determinant.FinFour

/-!
# The determinant of a 4 × 4 matrix

The expansion of the determinant of a `4 × 4` matrix into products of its entries is
`Matrix.det_fin_four`, which comes from the TauCeti dependency
(`TauCeti.LinearAlgebra.Matrix.Determinant.FinFour`) and extends Mathlib's explicit
expansions `Matrix.det_fin_two` and `Matrix.det_fin_three` to four dimensions. This file
restates that expansion for `Matrix.detRowAlternating`: on `ℝ⁴` the latter evaluates the
volume form, the Levi-Civita tensor `ε_{μνρσ}`, and the restatement turns identities between
volumes of four vectors into polynomial identities in their coordinates.

## Main results

- `Matrix.detRowAlternating_fin_four`: the expansion of `Matrix.det_fin_four` restated for
  `detRowAlternating` applied to four rows.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R]

/-- The determinant of four rows `v 0, …, v 3`, as the alternating map `detRowAlternating`:
the expansion of `Matrix.det_fin_four` along the first row, restated for `detRowAlternating`. -/
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
