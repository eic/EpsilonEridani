/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.PauliMatrices.Basic

/-!
# The spatial Pauli matrices: the sum of their squares

Each Pauli matrix squares to the identity (`PauliMatrix.pauliMatrix_mul_self`), so the three
spatial Pauli matrices `σ1, σ2, σ3`, which are `pauliMatrix (Sum.inr i)` for `i = 0, 1, 2`,
satisfy `σ1 σ1 + σ2 σ2 + σ3 σ3 = 3`. This is the matrix form of the Casimir of the fundamental
representation of `su(2)`: the spin operators `σᵢ / 2` give `s (s + 1) = 3/4` for `s = 1/2`.

## Main results

* `PauliMatrix.sum_pauliMatrix_inr_mul_self`: `σ1 σ1 + σ2 σ2 + σ3 σ3 = 3`.
-/

@[expose] public section

namespace PauliMatrix

/-- The sum of the squares of the three spatial Pauli matrices: `σ1 σ1 + σ2 σ2 + σ3 σ3 = 3`. -/
theorem sum_pauliMatrix_inr_mul_self :
    ∑ i : Fin 3, pauliMatrix (Sum.inr i) * pauliMatrix (Sum.inr i) = (3 : ℂ) • 1 := by
  simp only [pauliMatrix_mul_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

end PauliMatrix
