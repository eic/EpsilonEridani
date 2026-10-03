/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.MinkowskiMatrix

/-!
# Extensions of the Minkowski matrix

The Minkowski matrix `η = diag(1, -1, …, -1)` squares to the identity (`minkowskiMatrix.sq`), so
it is its own inverse. This is what is needed to use `η` as the metric of statements written for
a general metric `g`, in which indices are raised with the matrix inverse `g⁻¹`.
-/

public section

namespace minkowskiMatrix

variable {d : ℕ}

/-- The Minkowski matrix is its own inverse. -/
@[simp]
lemma inv_eq_self : (minkowskiMatrix : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ)⁻¹ = η :=
  Matrix.inv_eq_left_inv sq

end minkowskiMatrix
