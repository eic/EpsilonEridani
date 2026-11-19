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
matrices carry no global norm instance. `HasDerivAt` itself needs only a topological vector space
as codomain, so the statements below are about the product topology on `Matrix m m 𝕂`, the one
`NormedSpace.exp` uses on matrices. As in `Matrix.exp_add_of_commute`, the `L∞` operator norm
(`Matrix.Norms.Operator`) is installed locally inside the proofs only; it induces the product
topology, and no matrix norm appears in any statement.

## Main results

- `Matrix.hasDerivAt_exp_smul_const'`: `d/du exp (u • A) = A * exp (u • A)`.
- `Matrix.hasDerivAt_exp_smul_const_comp`: along a scalar path `f` with derivative `f'` at `t`,
  `d/ds exp (f s • A) = f' • (A * exp (f t • A))` at `t`.
- `Matrix.hasDerivAt_exp_smul_const_mulVec`: the same applied to a fixed vector `v`,
  `d/ds (exp (f s • A) *ᵥ v) = f' • (A *ᵥ (exp (f t • A) *ᵥ v))` at `t`. So
  `x s = exp (f s • A) *ᵥ v` satisfies `x' = f' • (A *ᵥ x)` wherever `f` is differentiable.
-/

public section

namespace Matrix

variable {𝕜 𝕂 m : Type*} [NontriviallyNormedField 𝕜] [RCLike 𝕂] [NormedAlgebra 𝕜 𝕂]
  [Fintype m] [DecidableEq m]

/-- The derivative of `u ↦ exp (u • A)` is `A * exp (u • A)`: the matrix version of
`_root_.hasDerivAt_exp_smul_const'`. -/
theorem hasDerivAt_exp_smul_const' (A : Matrix m m 𝕂) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => NormedSpace.exp (u • A)) (A * NormedSpace.exp (t • A)) t :=
  open scoped Norms.Operator in _root_.hasDerivAt_exp_smul_const' A t

/-- The matrix exponential along a differentiable scalar path `f`: the derivative of
`s ↦ exp (f s • A)` at `t` is `f' • (A * exp (f t • A))`. -/
theorem hasDerivAt_exp_smul_const_comp {f : 𝕜 → 𝕂} {f' : 𝕂} {t : 𝕜}
    (hf : HasDerivAt f f' t) (A : Matrix m m 𝕂) :
    HasDerivAt (fun s => NormedSpace.exp (f s • A)) (f' • (A * NormedSpace.exp (f t • A))) t :=
  open scoped Norms.Operator in HasDerivAt.scomp t (hasDerivAt_exp_smul_const' A (f t)) hf

/-- The matrix exponential along a differentiable scalar path `f`, applied to a fixed vector `v`,
has derivative `f' • (A *ᵥ (exp (f t • A) *ᵥ v))` at `t`. -/
theorem hasDerivAt_exp_smul_const_mulVec {f : 𝕜 → 𝕂} {f' : 𝕂} {t : 𝕜}
    (hf : HasDerivAt f f' t) (A : Matrix m m 𝕂) (v : m → 𝕂) :
    HasDerivAt (fun s => NormedSpace.exp (f s • A) *ᵥ v)
      (f' • (A *ᵥ (NormedSpace.exp (f t • A) *ᵥ v))) t := by
  open scoped Norms.Operator in
  -- applying a matrix to `v` is a bounded linear map for the operator norm
  let L : Matrix m m 𝕂 →L[𝕜] (m → 𝕂) :=
    LinearMap.mkContinuous
      { toFun := fun M => M *ᵥ v
        map_add' := fun A B => add_mulVec A B v
        map_smul' := fun c A => smul_mulVec c A v } ‖v‖
      fun M => (linfty_opNorm_mulVec M v).trans_eq (mul_comm _ _)
  -- `⇑L ∘ g` is `fun s => g s *ᵥ v` by `rfl`, since `⇑L` unfolds to `(· *ᵥ v)`
  have h : HasDerivAt (fun s => NormedSpace.exp (f s • A) *ᵥ v)
      (L (f' • (A * NormedSpace.exp (f t • A)))) t :=
    HasFDerivAt.comp_hasDerivAt t L.hasFDerivAt (hasDerivAt_exp_smul_const_comp hf A)
  have hL : L (f' • (A * NormedSpace.exp (f t • A))) =
      f' • (A *ᵥ (NormedSpace.exp (f t • A) *ᵥ v)) := by
    rw [mulVec_mulVec, ← smul_mulVec]
    -- `⇑L` is `(· *ᵥ v)` by definition
    rfl
  rwa [hL] at h

end Matrix
