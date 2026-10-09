/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LieAlgebra.SpecialUnitary
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Extensions of the special unitary Lie algebra

This file extends `EpsilonEridani.Mathematics.LieAlgebra.SpecialUnitary`, a mirror of a pending
Mathlib file that is kept diffable against it, with a constructor for membership in `su n`.

## Main statements

* `LieAlgebra.SpecialUnitary.I_smul_mem_su`: `i` times a Hermitian traceless matrix lies in
  `su n`. This turns a physics generator `T` into the element `i T` of `𝔰𝔲(n)`.
-/

public section

namespace EpsilonEridani.LieAlgebra.SpecialUnitary

open Complex Matrix

variable {n : Type*} [DecidableEq n] [Fintype n]

/-- `i` times a Hermitian traceless matrix is skew-Hermitian and traceless, so it lies in
`su n`. -/
theorem I_smul_mem_su {A : Matrix n n ℂ} (hA : A.IsHermitian) (h : trace A = 0) :
    I • A ∈ su n := by
  rw [mem_su_iff, conjTranspose_smul, hA.eq, trace_smul, h, smul_zero, star_def, conj_I,
    neg_smul]
  exact ⟨rfl, rfl⟩

end EpsilonEridani.LieAlgebra.SpecialUnitary

end
