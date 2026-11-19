/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed

/-!
# Derivatives of the matrix exponential along a scalar path

This file extends `Mathlib.Analysis.Normed.Algebra.MatrixExponential` with the derivative of
`u ↦ exp (u • A)` for a matrix `A`, stated for `Matrix m m 𝕂` with its product topology.

Mathlib computes such derivatives in a normed algebra (`hasDerivAt_exp_smul_const'`), and
matrices carry no norm instance. As in `Matrix.exp_add_of_commute`, the `L∞` operator norm
(`Matrix.Norms.Operator`) is installed locally inside the proofs only, so that no matrix norm
appears in any statement.

## Main results

- `Matrix.hasDerivAt_exp_smul_const'`: `d/du exp (u • A) = A * exp (u • A)`.
- `Matrix.hasDerivAt_exp_smul_const_mulVec`: along a differentiable scalar path `f`,
  `d/ds (exp (f s • A) *ᵥ v) = f' • (A *ᵥ (exp (f s • A) *ᵥ v))`. This is the solution of the
  linear system `x' = f' • A *ᵥ x` with initial value `exp (f t₀ • A) *ᵥ v`.
-/

public section

namespace Matrix

variable {𝕜 𝕂 m : Type*} [NontriviallyNormedField 𝕜] [RCLike 𝕂] [NormedAlgebra 𝕜 𝕂]
  [Fintype m] [DecidableEq m]

/-- The derivative of `u ↦ exp (u • A)` is `A * exp (u • A)`: the matrix version of
`hasDerivAt_exp_smul_const'`. -/
theorem hasDerivAt_exp_smul_const' (A : Matrix m m 𝕂) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => NormedSpace.exp (u • A)) (A * NormedSpace.exp (t • A)) t :=
  open scoped Norms.Operator in _root_.hasDerivAt_exp_smul_const' A t

/-- The matrix exponential along a differentiable scalar path `f`, applied to a fixed vector `v`,
has derivative `f' • (A *ᵥ (exp (f t • A) *ᵥ v))`. -/
theorem hasDerivAt_exp_smul_const_mulVec {f : 𝕜 → 𝕂} {f' : 𝕂} {t : 𝕜}
    (hf : HasDerivAt f f' t) (A : Matrix m m 𝕂) (v : m → 𝕂) :
    HasDerivAt (fun s => NormedSpace.exp (f s • A) *ᵥ v)
      (f' • (A *ᵥ (NormedSpace.exp (f t • A) *ᵥ v))) t := by
  have h : HasDerivAt (fun u : 𝕂 => NormedSpace.exp (u • A) *ᵥ v)
      ((A * NormedSpace.exp (f t • A)) *ᵥ v) (f t) := by
    open scoped Norms.Operator in
    -- applying a matrix to `v` is a bounded linear map for the operator norm
    let L : Matrix m m 𝕂 →L[𝕂] (m → 𝕂) :=
      LinearMap.mkContinuous
        { toFun := fun M => M *ᵥ v
          map_add' := fun A B => add_mulVec A B v
          map_smul' := fun c A => smul_mulVec c A v } ‖v‖
        fun M => (linfty_opNorm_mulVec M v).trans_eq (mul_comm _ _)
    exact HasFDerivAt.comp_hasDerivAt (f t) L.hasFDerivAt (hasDerivAt_exp_smul_const' A (f t))
  simpa only [Function.comp_def, ← mulVec_mulVec] using HasDerivAt.scomp t h hf

end Matrix
