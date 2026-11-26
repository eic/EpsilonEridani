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
# Derivatives and unmixed rows of the matrix exponential

This file extends `Mathlib.Analysis.Normed.Algebra.MatrixExponential` with two facts about the
exponential of a matrix `A` with entries in a complete normed algebra `𝔸`:

* its derivative along a scalar path, `u ↦ exp (u • A)`, together with the derivative of a
  matrix path applied to a fixed vector. These say that `exp (u • A)` solves the linear
  system `x' = A x`, in matrix form and applied to an initial vector;
* its entries on a row `i` whose off-diagonal entries vanish: such a row of `exp A` is
  `exp (A i i)` on the diagonal and zero elsewhere. This is the closed form of a component of a
  linear system that mixes with no other component, e.g. a non-singlet channel of DGLAP
  evolution in moment space, inside a system whose other components mix.

Mathlib computes the derivative in a normed algebra (`hasDerivAt_exp_smul_const'`), and
matrices carry no global norm instance. `HasDerivAt` itself needs only a topological vector space
as codomain, so the statements below are about the product topology on `Matrix m m 𝔸`, the one
`NormedSpace.exp` uses on matrices. As in `Matrix.exp_add_of_commute`, the `L∞` operator norm
(`Matrix.Norms.Operator`) is installed locally inside the proofs only; it induces the product
topology, and no matrix norm appears in any statement.

## Main results

- `Matrix.hasDerivAt_exp_smul_const'`: `d/du exp (u • A) = A * exp (u • A)`.
- `HasDerivAt.matrix_exp_smul_const'`: along a scalar path `f` with derivative `f'` at `t`,
  `d/ds exp (f s • A) = f' • (A * exp (f t • A))` at `t`.
- `HasDerivAt.mulVec_const`: a differentiable matrix path `M` applied to a fixed vector `v` has
  derivative `M' *ᵥ v`.
- `Matrix.exp_apply_of_row_apply_eq_zero_of_ne`: if the off-diagonal entries of row `i` of `A`
  vanish, row `i` of `exp A` is `exp (A i i)` on the diagonal and zero elsewhere.
-/

public section

/-! The two private helpers below take the `CompleteSpace` instance of a general normed algebra
as an explicit argument. Under the scoped operator norm, typeclass synthesis cannot match the
`CompleteSpace` instance of the product uniformity on `Matrix m m 𝔸` against the operator-norm
uniformity of the normed algebra structure: the two uniformities agree only beyond instance
transparency, so a local `letI : CompleteSpace (Matrix m m 𝔸)` is rejected for the same reason.
An explicit argument instead leaves the check to the elaborator's definitional equality. -/

/-- `_root_.hasDerivAt_exp_smul_const'` with the completeness of the algebra passed explicitly. -/
private theorem hasDerivAt_exp_smul_const_of_completeSpace {𝕂 A : Type*} [RCLike 𝕂]
    [NormedRing A] [NormedAlgebra 𝕂 A] (hA : CompleteSpace A) (x : A) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => NormedSpace.exp (u • x)) (x * NormedSpace.exp (t • x)) t := by
  have := hA
  exact _root_.hasDerivAt_exp_smul_const' x t

/-- `NormedSpace.exp_series_hasSum_exp'` over `ℚ`, with the completeness of the algebra passed
explicitly. -/
private theorem exp_series_hasSum_exp_of_completeSpace {A : Type*} [NormedRing A]
    [NormedAlgebra ℚ A] (hA : CompleteSpace A) (x : A) :
    HasSum (fun n => (n.factorial⁻¹ : ℚ) • x ^ n) (NormedSpace.exp x) := by
  have := hA
  exact NormedSpace.exp_series_hasSum_exp' x

variable {𝕜 𝕂 𝔸 m : Type*} [NontriviallyNormedField 𝕜] [Fintype m]

section RCLike

variable [DecidableEq m] [RCLike 𝕂] [NormedAlgebra 𝕜 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

namespace Matrix

/-- The derivative of `u ↦ exp (u • A)` is `A * exp (u • A)`: the matrix version of
`_root_.hasDerivAt_exp_smul_const'`. -/
theorem hasDerivAt_exp_smul_const' (A : Matrix m m 𝔸) (t : 𝕂) :
    HasDerivAt (fun u : 𝕂 => NormedSpace.exp (u • A)) (A * NormedSpace.exp (t • A)) t :=
  open scoped Norms.Operator in
  hasDerivAt_exp_smul_const_of_completeSpace (inferInstance : CompleteSpace (Matrix m m 𝔸)) A t

end Matrix

variable [NormedAlgebra 𝕜 𝔸] [IsScalarTower 𝕜 𝕂 𝔸]

/-- The matrix exponential along a differentiable scalar path `f`: the derivative of
`s ↦ exp (f s • A)` at `t` is `f' • (A * exp (f t • A))`. -/
theorem HasDerivAt.matrix_exp_smul_const' {f : 𝕜 → 𝕂} {f' : 𝕂} {t : 𝕜}
    (hf : HasDerivAt f f' t) (A : Matrix m m 𝔸) :
    HasDerivAt (fun s => NormedSpace.exp (f s • A)) (f' • (A * NormedSpace.exp (f t • A))) t :=
  open scoped Matrix.Norms.Operator in
  HasDerivAt.scomp t (Matrix.hasDerivAt_exp_smul_const' A (f t)) hf

end RCLike

open Matrix

/-- A differentiable matrix path applied to a fixed vector: the derivative of `s ↦ M s *ᵥ v` at
`t` is `M' *ᵥ v`. -/
theorem HasDerivAt.mulVec_const [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] {M : 𝕜 → Matrix m m 𝔸}
    {M' : Matrix m m 𝔸} {t : 𝕜} (hM : HasDerivAt M M' t) (v : m → 𝔸) :
    HasDerivAt (fun s => M s *ᵥ v) (M' *ᵥ v) t := by
  open scoped Norms.Operator in
  -- applying a matrix to `v` is a bounded linear map for the operator norm
  let L := LinearMap.mkContinuous ((mulVecBilin 𝕜 𝕜).flip v : Matrix m m 𝔸 →ₗ[𝕜] m → 𝔸) ‖v‖
    fun M => by
      rw [LinearMap.flip_apply, mulVecBilin_apply, mul_comm]
      exact linfty_opNorm_mulVec M v
  exact L.hasFDerivAt.comp_hasDerivAt t hM

namespace Matrix

variable [DecidableEq m] [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-- **The exponential of an unmixed row.** If the off-diagonal entries of row `i` of `A` vanish,
row `i` of `exp A` is `exp (A i i)` on the diagonal and zero elsewhere. -/
theorem exp_apply_of_row_apply_eq_zero_of_ne {A : Matrix m m 𝔸} {i : m}
    (h : ∀ j, j ≠ i → A i j = 0) (j : m) :
    NormedSpace.exp A i j = if i = j then NormedSpace.exp (A i i) else 0 := by
  -- the exponential series of `A`, read off at entry `(i, j)`; the entry map is continuous for
  -- the operator-norm topology, which is the product topology
  have hs : HasSum (fun k : ℕ => (k.factorial⁻¹ : ℚ) • (A ^ k) i j) (NormedSpace.exp A i j) := by
    open scoped Norms.Operator in
    exact (exp_series_hasSum_exp_of_completeSpace
      (inferInstance : CompleteSpace (Matrix m m 𝔸)) A).map
        (entryLinearMap ℚ 𝔸 i j).toAddMonoidHom (continuous_id.matrix_elem i j)
  -- row `i` of each power of `A` is that of the scalar diagonal matrix `A i i`
  simp only [pow_apply_of_row_apply_eq_zero_of_ne h, smul_ite, smul_zero] at hs
  refine hs.unique ?_
  split_ifs
  · exact NormedSpace.exp_series_hasSum_exp' _
  · exact hasSum_zero

end Matrix
