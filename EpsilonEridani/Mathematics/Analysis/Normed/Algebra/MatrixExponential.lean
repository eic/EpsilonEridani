/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.UniformSpace.Matrix

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
  set a := A i i
  -- entry `(i, j)` of `exp (s • A)` solves the scalar equation `g' = a * g`, since row `i` of `A`
  -- is `a` on the diagonal
  have hg (s : 𝕂) : HasDerivAt (fun s : 𝕂 => NormedSpace.exp (s • A) i j)
      (a * NormedSpace.exp (s • A) i j) s := by
    have hv := hasDerivAt_pi.1
      ((hasDerivAt_id s).matrix_exp_smul_const_mulVec' A (Pi.single j 1)) i
    rw [mulVec_mulVec] at hv
    simp only [id, one_smul, mulVec_single_one, col_apply] at hv
    rwa [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [h k hk, zero_mul])
      (fun hi => absurd (Finset.mem_univ i) hi)] at hv
  -- so `exp (s • -a) * g s` has derivative zero, `a` commuting with its own exponential
  have hc (s : 𝕂) : HasDerivAt
      (fun s : 𝕂 => NormedSpace.exp (s • -a) * NormedSpace.exp (s • A) i j) 0 s := by
    have hcomm : Commute a (NormedSpace.exp (s • -a)) :=
      ((Commute.refl a).neg_right.smul_right s).exp_right
    convert (_root_.hasDerivAt_exp_smul_const' (-a) s).mul (hg s) using 1
    rw [neg_mul, neg_mul, hcomm.eq, mul_assoc, neg_add_cancel]
  have hconst := is_const_of_deriv_eq_zero (fun s => (hc s).differentiableAt)
    (fun s => (hc s).deriv) u 0
  simp only [zero_smul, NormedSpace.exp_zero, one_mul, Matrix.one_apply] at hconst
  -- `exp (u • a)` inverts `exp (u • -a)`; `NormedSpace.exp_add_of_commute` is stated over `ℚ`
  let : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ 𝕂 𝔸
  have hinv : NormedSpace.exp (u • a) * NormedSpace.exp (u • -a) = 1 := by
    rw [smul_neg, ← NormedSpace.exp_add_of_commute ((Commute.refl (u • a)).neg_right),
      add_neg_cancel, NormedSpace.exp_zero]
  rw [← one_mul (NormedSpace.exp (u • A) i j), ← hinv, mul_assoc, hconst, mul_ite, mul_one,
    mul_zero]

end Matrix
