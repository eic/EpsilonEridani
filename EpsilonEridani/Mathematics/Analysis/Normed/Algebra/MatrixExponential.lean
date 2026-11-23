/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.UniformSpace.Matrix
import EpsilonEridani.Mathematics.Data.Matrix.Basic

/-!
# Derivatives of the matrix exponential along a scalar path

This file extends `Mathlib.Analysis.Normed.Algebra.MatrixExponential` with the derivative of
`u ↦ exp (u • A)` for a matrix `A` with entries in a complete normed algebra `𝔸`, stated for
`Matrix m m 𝔸` with its product topology.

Mathlib computes such derivatives in a normed algebra (`hasDerivAt_exp_smul_const'`), and
matrices carry no global norm instance. `HasDerivAt` itself needs only a topological vector space
as codomain, so the statements below are about the product topology on `Matrix m m 𝔸`, the one
`NormedSpace.exp` uses on matrices. As in `Matrix.exp_add_of_commute`, the `L∞` operator norm
(`Matrix.Norms.Operator`) is installed locally inside the proofs only; it induces the product
topology, and no matrix norm appears in any statement.

## Main results

- `Matrix.hasDerivAt_exp_smul_const'`: `d/du exp (u • A) = A * exp (u • A)`.
- `HasDerivAt.matrix_exp_smul_const'`: along a scalar path `f` with derivative `f'` at `t`,
  `d/ds exp (f s • A) = f' • (A * exp (f t • A))` at `t`.
- `HasDerivAt.matrix_exp_smul_const_mulVec'`: the same applied to a fixed vector `v`,
  `d/ds (exp (f s • A) *ᵥ v) = f' • (A *ᵥ (exp (f t • A) *ᵥ v))` at `t`. So
  `x s = exp (f s • A) *ᵥ v` satisfies `x' = f' • (A *ᵥ x)` wherever `f` is differentiable.
- `Matrix.exp_smul_apply_of_row_apply_eq_zero_of_ne`: if the off-diagonal entries of row `i` of
  `A` vanish, row `i` of `exp (u • A)` is `exp (u • A i i)` on the diagonal and zero elsewhere.
-/

public section

variable {𝕜 𝕂 𝔸 m : Type*} [NontriviallyNormedField 𝕜] [RCLike 𝕂] [NormedAlgebra 𝕜 𝕂]
  [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸] [Fintype m] [DecidableEq m]

namespace Matrix

-- The `CompleteSpace (Matrix m m 𝔸)` argument of the general lemma is passed explicitly.
-- Under the scoped operator norm, typeclass synthesis cannot match the `CompleteSpace`
-- instance of the product uniformity against the operator-norm uniformity baked into the
-- lemma's binder: the two uniformities agree only beyond instance transparency. Mathlib's
-- `Matrix.exp_add_of_commute` bridges the same diamond with
-- `set_option backward.isDefEq.respectTransparency false`, which this repository forbids;
-- an explicit argument instead leaves the check to the elaborator's definitional equality.
-- A local `letI : CompleteSpace (Matrix m m 𝔸)` does not help: synthesis rejects it for the same
-- reason. The three `_` are exactly the `RCLike 𝕂`, `NormedRing` and `NormedAlgebra 𝕂` instances.
/-- The derivative of `u ↦ exp (u • A)` is `A * exp (u • A)`: the matrix version of
`_root_.hasDerivAt_exp_smul_const'`. -/
theorem hasDerivAt_exp_smul_const' (A : Matrix m m 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => NormedSpace.exp (u • A)) (A * NormedSpace.exp (t • A)) t :=
  open scoped Norms.Operator in
  @_root_.hasDerivAt_exp_smul_const' 𝕂 (Matrix m m 𝔸) _ _ _
    (inferInstance : CompleteSpace (Matrix m m 𝔸)) A t

end Matrix

open Matrix

variable [NormedAlgebra 𝕜 𝔸] [IsScalarTower 𝕜 𝕂 𝔸]

/-- The matrix exponential along a differentiable scalar path `f`: the derivative of
`s ↦ exp (f s • A)` at `t` is `f' • (A * exp (f t • A))`. -/
theorem HasDerivAt.matrix_exp_smul_const' {f : 𝕜 → 𝕂} {f' : 𝕂} {t : 𝕜}
    (hf : HasDerivAt f f' t) (A : Matrix m m 𝔸) :
    HasDerivAt (fun s => NormedSpace.exp (f s • A)) (f' • (A * NormedSpace.exp (f t • A))) t :=
  open scoped Norms.Operator in HasDerivAt.scomp t (Matrix.hasDerivAt_exp_smul_const' A (f t)) hf

/-- The matrix exponential along a differentiable scalar path `f`, applied to a fixed vector `v`,
has derivative `f' • (A *ᵥ (exp (f t • A) *ᵥ v))` at `t`. -/
theorem HasDerivAt.matrix_exp_smul_const_mulVec' {f : 𝕜 → 𝕂} {f' : 𝕂} {t : 𝕜}
    (hf : HasDerivAt f f' t) (A : Matrix m m 𝔸) (v : m → 𝔸) :
    HasDerivAt (fun s => NormedSpace.exp (f s • A) *ᵥ v)
      (f' • (A *ᵥ (NormedSpace.exp (f t • A) *ᵥ v))) t := by
  open scoped Norms.Operator in
  -- applying a matrix to `v` is a bounded linear map for the operator norm
  let L := LinearMap.mkContinuous ((mulVecBilin 𝕜 𝕜).flip v : Matrix m m 𝔸 →ₗ[𝕜] m → 𝔸) ‖v‖
    fun M => by
      rw [LinearMap.flip_apply, mulVecBilin_apply, mul_comm]
      exact linfty_opNorm_mulVec M v
  have hL (M : Matrix m m 𝔸) : L M = M *ᵥ v := by
    simp only [L, LinearMap.mkContinuous_apply, LinearMap.flip_apply, mulVecBilin_apply]
  have h := L.hasFDerivAt.comp_hasDerivAt t (hf.matrix_exp_smul_const' A)
  simpa only [Function.comp_def, hL, mulVec_mulVec, ← smul_mulVec] using h

namespace Matrix

/-- **The exponential of an unmixed row.** If the off-diagonal entries of row `i` of `A` vanish,
row `i` of `exp (u • A)` is `exp (u • A i i)` on the diagonal and zero elsewhere. -/
theorem exp_smul_apply_of_row_apply_eq_zero_of_ne {A : Matrix m m 𝔸} {i : m}
    (h : ∀ j, j ≠ i → A i j = 0) (u : 𝕂) (j : m) :
    NormedSpace.exp (u • A) i j = if i = j then NormedSpace.exp (u • A i i) else 0 := by
  -- row `i` of `u • A` is unmixed, so row `i` of each of its powers is that of the scalar
  -- diagonal matrix `u • A i i` (`Matrix.pow_apply_of_row_apply_eq_zero_of_ne`)
  have hrow (l : m) (hl : l ≠ i) : (u • A) i l = 0 := by
    rw [Matrix.smul_apply, h l hl, smul_zero]
  -- so the exponential series agree entrywise. This is TauCeti's
  -- `Matrix.exp_apply_eq_of_forall_pow_apply_eq`, whose module cannot be imported together with
  -- `Physlib.Mathematics.ForMathlib.DataStructures.Matrix.LieTrace`: both declare `Matrix.det_exp`.
  have hs : HasSum (fun k : ℕ => (k.factorial⁻¹ : 𝕂) • ((u • A) ^ k) i j)
      (NormedSpace.exp (u • A) i j) := by
    -- As in `Matrix.hasDerivAt_exp_smul_const'`, the `CompleteSpace` instance is passed
    -- explicitly; the five `_` are exactly the `NontriviallyNormedField 𝕂`, `CharZero 𝕂`,
    -- `ContinuousSMul ℚ 𝕂`, `NormedRing` and `NormedAlgebra 𝕂` instances. `Pi.hasSum` then reads
    -- off the entries: it treats `Matrix m m 𝔸` as `m → m → 𝔸` and the operator-norm topology as
    -- the product topology, which holds definitionally because
    -- `Matrix.linftyOpNormedAddCommGroup` is built from `Pi.normedAddCommGroup`.
    open scoped Norms.Operator in
    exact Pi.hasSum.1 (Pi.hasSum.1 (@NormedSpace.exp_series_hasSum_exp' 𝕂 (Matrix m m 𝔸)
      _ _ _ _ _ (inferInstance : CompleteSpace (Matrix m m 𝔸)) (u • A)) i) j
  simp only [pow_apply_of_row_apply_eq_zero_of_ne hrow, Matrix.smul_apply, smul_ite,
    smul_zero] at hs
  refine hs.unique ?_
  split_ifs
  · exact NormedSpace.exp_series_hasSum_exp' _
  · exact hasSum_zero

end Matrix
