/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Mathematics.Modules.CrossProductMatrix
public import EpsilonEridani.QFT.QCD.SU2Generators
public import EpsilonEridani.Mathematics.DataStructures.Matrix.PosSemidef

/-!
# The spin density matrix of a spin-one target

The spin state of a target of spin `s` is a positive semidefinite, unit-trace density matrix `ρ`
on the `2s + 1`-dimensional spin space. Given spin matrices `S₀, S₁, S₂` on that space, the
*vector polarization* and the *tensor polarization* of `ρ` are the expectation values

* `Pₖ = tr (ρ Sₖ)`,
* `Pᵢⱼ = tr (ρ Σᵢⱼ)`, where `Σᵢⱼ = (3/2) (Sᵢ Sⱼ + Sⱼ Sᵢ) - δᵢⱼ ∑ₖ Sₖ Sₖ`

is the symmetric traceless rank-two *spin tensor operator*. For an irreducible spin the Casimir
`∑ₖ Sₖ Sₖ` is `s (s + 1)`, so `Σᵢⱼ` is the usual `(3/2) {Sᵢ, Sⱼ} - s (s + 1) δᵢⱼ`; for spin one
`P₂₂ = tr (ρ (3 S₂² - 2))` is the tensor polarization `P_zz = n₊ + n₋ - 2 n₀` along the
quantization axis, in terms of the populations `n_m` of the magnetic substates. For hermitian
spin matrices and a hermitian `ρ` both polarizations are real (`vectorPolarization_im`,
`tensorPolarization_im`).

This file develops the two spins that matter for light nuclei.

* **Spin one** (the deuteron), in the Cartesian basis, where `(Sₖ)ₐᵦ = -i εₖₐᵦ`
  (`spinOneMatrix`): `Sₖ` is `i` times the hat matrix `Matrix.crossProductMatrix` of the `k`-th
  basis vector, the generator of rotations about the `k`-th axis acting on three-vectors.
  The matrices `1`, `Sₖ`, `Σᵢⱼ` span all `3 × 3` matrices, and the three families are mutually
  orthogonal for the trace form: every `ρ` is
  `ρ = (tr ρ / 3) 1 + (1/2) ∑ₖ Pₖ Sₖ + (1/9) ∑ᵢⱼ Pᵢⱼ Σᵢⱼ`
  (`spinOneMatrix_decomposition`), and the three pieces are the trace part, the antisymmetric
  part `(ρ - ρᵀ) / 2` and the symmetric traceless part `(ρ + ρᵀ) / 2 - (tr ρ / 3) 1` of `ρ`. In
  the language of representations these are the components of degree zero, one and two of a
  spin-one density matrix (scalar, vector polarization, tensor polarization); this file
  identifies them concretely and does not develop the rotation action.
* **Spin one half** (the nucleon), with `Sₖ = σₖ / 2` (`spinHalfMatrix`), the fundamental
  `su(2)` generators `EpsilonEridani.QFT.QCD.RepresentationColor.su2GenEntry` as matrices. Here
  the spin tensor operator vanishes identically (`spinTensorOperator_spinHalfMatrix`), because
  `{σᵢ, σⱼ} = 2 δᵢⱼ`: a spin-one-half target carries no tensor polarization
  (`tensorPolarization_spinHalfMatrix`). This is the structural reason why the tensor structure
  functions of a spin-one target have no spin-one-half analogue.

Positive semidefiniteness of a unit-trace `ρ` bounds the spin-one polarizations:
`-2 ≤ Pᵢᵢ ≤ 1` and `3 |Pₖ| ≤ 2 + Pₖₖ` (so `|Pₖ| ≤ 1`). Both bounds on `Pₖₖ` are attained by
pure states: the state of zero spin projection along axis `k`, which has vanishing vector
polarization and the extreme tensor polarization `Pₖₖ = -2`, and a state of zero spin
projection along a perpendicular axis, which has `Pₖₖ = 1`.

## Main definitions

* `EpsilonEridani.Spin.spinTensorOperator`: the spin tensor operator `Σᵢⱼ` built from spin
  matrices.
* `EpsilonEridani.Spin.vectorPolarization`, `EpsilonEridani.Spin.tensorPolarization`: `Pₖ`, `Pᵢⱼ`.
* `EpsilonEridani.Spin.spinOneMatrix`, `EpsilonEridani.Spin.spinHalfMatrix`: the spin matrices
  of spin one and spin one half.

## Main results

* `EpsilonEridani.Spin.spinOneMatrix_commutator_zero_one` (and its cyclic partners) and
  `EpsilonEridani.Spin.sum_spinOneMatrix_mul_self`: `spinOneMatrix` is a spin-one
  representation.
* `EpsilonEridani.Spin.spinOneMatrix_decomposition`: completeness of the decomposition.
* `EpsilonEridani.Spin.trace_spinOneMatrix_mul_spinOneMatrix`,
  `EpsilonEridani.Spin.trace_spinOneMatrix_mul_spinTensorOperator_spinOneMatrix`,
  `EpsilonEridani.Spin.trace_spinTensorOperator_mul_spinTensorOperator_spinOneMatrix`: its
  orthogonality.
* `EpsilonEridani.Spin.tensorPolarization_spinHalfMatrix`: a spin-one-half state has no tensor
  polarization.
* `EpsilonEridani.Spin.neg_two_le_re_tensorPolarization_spinOneMatrix`,
  `EpsilonEridani.Spin.re_tensorPolarization_spinOneMatrix_le_one`,
  `EpsilonEridani.Spin.three_mul_norm_vectorPolarization_spinOneMatrix_le`: the positivity
  bounds.

## References

* P. Hoodbhoy, R. L. Jaffe and A. Manohar, *Novel effects in deep inelastic scattering from
  spin-one hadrons*, Nucl. Phys. B312 (1989) 571.
* E. Leader, *Spin in Particle Physics*, Cambridge University Press (2001), §3.1.
* A. Airapetian et al. (HERMES), *First measurement of the tensor structure function `b₁` of the
  deuteron*, Phys. Rev. Lett. 95 (2005) 242001 (the convention `P_zz = n₊ + n₋ - 2 n₀`).
-/

public section

noncomputable section

namespace EpsilonEridani.Spin

open Matrix Complex
open EpsilonEridani.QFT.QCD.RepresentationColor

/-! ### The spin tensor operator and the polarizations -/

section General

variable {n : Type*} [Fintype n]

/-- The **spin tensor operator** `Σᵢⱼ = (3/2) (Sᵢ Sⱼ + Sⱼ Sᵢ) - δᵢⱼ ∑ₖ Sₖ Sₖ` of a triple of
spin matrices `S`: the symmetric traceless rank-two combination of the spin matrices. For an
irreducible spin `s`, where `∑ₖ Sₖ Sₖ = s (s + 1)`, it is `(3/2) {Sᵢ, Sⱼ} - s (s + 1) δᵢⱼ`. -/
def spinTensorOperator (S : Fin 3 → Matrix n n ℂ) (i j : Fin 3) : Matrix n n ℂ :=
  (3 / 2 : ℂ) • (S i * S j + S j * S i) - if i = j then ∑ k, S k * S k else 0

/-- The **vector polarization** `Pₖ = tr (ρ Sₖ)` of a spin density matrix `ρ`: the expectation
value of the spin component `Sₖ`. This is the conventional polarization vector for spin one; for
a general spin `s` the conventional polarization vector is `Pₖ / s`. -/
def vectorPolarization (S : Fin 3 → Matrix n n ℂ) (ρ : Matrix n n ℂ) (k : Fin 3) : ℂ :=
  (ρ * S k).trace

/-- The **tensor polarization** `Pᵢⱼ = tr (ρ Σᵢⱼ)` of a spin density matrix `ρ`: the expectation
value of the spin tensor operator `Σᵢⱼ`. -/
def tensorPolarization (S : Fin 3 → Matrix n n ℂ) (ρ : Matrix n n ℂ) (i j : Fin 3) : ℂ :=
  (ρ * spinTensorOperator S i j).trace

variable (S : Fin 3 → Matrix n n ℂ)

lemma spinTensorOperator_def (i j : Fin 3) :
    spinTensorOperator S i j =
      (3 / 2 : ℂ) • (S i * S j + S j * S i) - if i = j then ∑ k, S k * S k else 0 := (rfl)

lemma vectorPolarization_def (ρ : Matrix n n ℂ) (k : Fin 3) :
    vectorPolarization S ρ k = (ρ * S k).trace := (rfl)

lemma tensorPolarization_def (ρ : Matrix n n ℂ) (i j : Fin 3) :
    tensorPolarization S ρ i j = (ρ * spinTensorOperator S i j).trace := (rfl)

/-- The spin tensor operator is symmetric in its two indices. -/
lemma spinTensorOperator_comm (i j : Fin 3) :
    spinTensorOperator S i j = spinTensorOperator S j i := by
  simp only [spinTensorOperator_def, add_comm (S i * S j), eq_comm (a := i)]

/-- The spin tensor operator is traceless as a rank-two tensor: `∑ᵢ Σᵢᵢ = 0`. -/
@[simp]
lemma sum_spinTensorOperator_self : ∑ i, spinTensorOperator S i i = 0 := by
  simp only [spinTensorOperator_def, ite_true, Finset.sum_sub_distrib, ← Finset.smul_sum,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  module

/-- The tensor polarization is symmetric in its two indices. -/
lemma tensorPolarization_comm (ρ : Matrix n n ℂ) (i j : Fin 3) :
    tensorPolarization S ρ i j = tensorPolarization S ρ j i := by
  rw [tensorPolarization_def, spinTensorOperator_comm, tensorPolarization_def]

/-- The tensor polarization is traceless: `∑ᵢ Pᵢᵢ = 0`. -/
@[simp]
lemma sum_tensorPolarization_self (ρ : Matrix n n ℂ) : ∑ i, tensorPolarization S ρ i i = 0 := by
  simp only [tensorPolarization_def, ← trace_sum, ← Matrix.mul_sum, sum_spinTensorOperator_self,
    Matrix.mul_zero, trace_zero]

variable {S}

/-- The spin tensor operator of hermitian spin matrices is hermitian. -/
lemma isHermitian_spinTensorOperator (hS : ∀ k, (S k).IsHermitian) (i j : Fin 3) :
    (spinTensorOperator S i j).IsHermitian := by
  have hsq : (∑ k, S k * S k).IsHermitian := by
    simp only [IsHermitian, conjTranspose_sum, conjTranspose_mul, (hS _).eq]
  have hanti : (S i * S j + S j * S i).IsHermitian := by
    simp only [IsHermitian, conjTranspose_add, conjTranspose_mul, (hS _).eq, add_comm]
  rw [spinTensorOperator_def]
  refine IsHermitian.sub ?_ (by split_ifs <;> simp [hsq])
  rw [IsHermitian, conjTranspose_smul, hanti.eq, star_div₀, star_ofNat, star_ofNat]

/-- The vector polarization of a hermitian `ρ` for hermitian spin matrices is real. -/
lemma vectorPolarization_im (hS : ∀ k, (S k).IsHermitian) {ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (k : Fin 3) : (vectorPolarization S ρ k).im = 0 := by
  rw [vectorPolarization_def, ← conj_eq_iff_im, ← star_def, ← trace_conjTranspose,
    conjTranspose_mul, hρ.eq, (hS k).eq, trace_mul_comm]

/-- The tensor polarization of a hermitian `ρ` for hermitian spin matrices is real. -/
lemma tensorPolarization_im (hS : ∀ k, (S k).IsHermitian) {ρ : Matrix n n ℂ}
    (hρ : ρ.IsHermitian) (i j : Fin 3) : (tensorPolarization S ρ i j).im = 0 := by
  rw [tensorPolarization_def, ← conj_eq_iff_im, ← star_def, ← trace_conjTranspose,
    conjTranspose_mul, hρ.eq, (isHermitian_spinTensorOperator hS i j).eq, trace_mul_comm]

end General

/-! ### Spin one -/

/-- The **spin-one matrices** in the Cartesian basis, `(Sₖ)ₐᵦ = -i εₖₐᵦ`: `i` times the hat
matrix `[eₖ]ₓ` of the `k`-th basis vector, the generator of rotations about the `k`-th axis acting
on three-vectors, which is the spin-one representation. -/
def spinOneMatrix (k : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  I • (crossProductMatrix (Pi.single k 1)).map (↑)

lemma spinOneMatrix_def (k : Fin 3) :
    spinOneMatrix k = I • (crossProductMatrix (Pi.single k 1)).map (↑) := (rfl)

/-- The entries of the spin-one matrices are `(Sₖ)ₐᵦ = -i εₖₐᵦ`, with `ε` the Levi-Civita
symbol `epsilon3`. -/
lemma spinOneMatrix_apply (k a b : Fin 3) : spinOneMatrix k a b = -I * epsilon3 k a b := by
  fin_cases k <;> fin_cases a <;> fin_cases b <;>
    simp [spinOneMatrix_def, crossProductMatrix, epsilon3]

/-- The spin-one matrices are antisymmetric: `Sₖᵀ = -Sₖ`. -/
@[simp]
lemma transpose_spinOneMatrix (k : Fin 3) : (spinOneMatrix k)ᵀ = -spinOneMatrix k := by
  rw [spinOneMatrix_def, transpose_smul, ← transpose_map, crossProductMatrix_transpose,
    Matrix.map_neg _ ofReal_neg, smul_neg]

/-- The product of two spin-one matrices: `(Sᵢ Sⱼ)ₐᵦ = δᵢⱼ δₐᵦ - δᵢᵦ δⱼₐ`, the contraction
identity `εᵢₐₖ εⱼᵦₖ = δᵢⱼ δₐᵦ - δᵢᵦ δₐⱼ`. -/
lemma spinOneMatrix_mul_spinOneMatrix_apply (i j a b : Fin 3) :
    (spinOneMatrix i * spinOneMatrix j) a b =
      (if i = j ∧ a = b then 1 else 0) - (if i = b ∧ j = a then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, spinOneMatrix_apply, epsilon3]

/-- The entries of a spin-one matrix are antisymmetric: `(Sₖ)ᵦₐ = -(Sₖ)ₐᵦ`. -/
lemma spinOneMatrix_apply_swap (k a b : Fin 3) : spinOneMatrix k b a = -spinOneMatrix k a b := by
  rw [← transpose_apply (spinOneMatrix k), transpose_spinOneMatrix, neg_apply]

/-- The diagonal entries of a spin-one matrix vanish. -/
@[simp]
lemma spinOneMatrix_apply_self (k a : Fin 3) : spinOneMatrix k a a = 0 :=
  CharZero.eq_neg_self_iff.mp (spinOneMatrix_apply_swap k a a)

/-- The spin-one matrices are hermitian. -/
lemma isHermitian_spinOneMatrix (k : Fin 3) : (spinOneMatrix k).IsHermitian := by
  ext a b
  fin_cases k <;> fin_cases a <;> fin_cases b <;> simp [spinOneMatrix_apply, epsilon3]

/-- The spin-one matrices obey the angular-momentum algebra: `[S₀, S₁] = i S₂`. -/
lemma spinOneMatrix_commutator_zero_one :
    spinOneMatrix 0 * spinOneMatrix 1 - spinOneMatrix 1 * spinOneMatrix 0 =
      I • spinOneMatrix 2 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, spinOneMatrix_apply, epsilon3]

/-- The spin-one matrices obey the angular-momentum algebra: `[S₁, S₂] = i S₀`. -/
lemma spinOneMatrix_commutator_one_two :
    spinOneMatrix 1 * spinOneMatrix 2 - spinOneMatrix 2 * spinOneMatrix 1 =
      I • spinOneMatrix 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, spinOneMatrix_apply, epsilon3]

/-- The spin-one matrices obey the angular-momentum algebra: `[S₂, S₀] = i S₁`. -/
lemma spinOneMatrix_commutator_two_zero :
    spinOneMatrix 2 * spinOneMatrix 0 - spinOneMatrix 0 * spinOneMatrix 2 =
      I • spinOneMatrix 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, spinOneMatrix_apply, epsilon3]

/-- The Casimir of the spin-one matrices is `s (s + 1) = 2`. -/
lemma sum_spinOneMatrix_mul_self : ∑ k, spinOneMatrix k * spinOneMatrix k = (2 : ℂ) • 1 := by
  ext a b
  simp only [Matrix.sum_apply, spinOneMatrix_mul_spinOneMatrix_apply, Fin.sum_univ_three,
    Matrix.smul_apply, Matrix.one_apply]
  fin_cases a <;> fin_cases b <;> norm_num

/-- The spin-one matrices are traceless. -/
@[simp]
lemma trace_spinOneMatrix (k : Fin 3) : (spinOneMatrix k).trace = 0 := by
  simp [trace_fin_three]

/-- The spin-one matrices are orthogonal for the trace form: `tr (Sᵢ Sⱼ) = 2 δᵢⱼ`. -/
lemma trace_spinOneMatrix_mul_spinOneMatrix (i j : Fin 3) :
    (spinOneMatrix i * spinOneMatrix j).trace = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [trace_fin_three, spinOneMatrix_mul_spinOneMatrix_apply]

/-- The entries of the spin-one tensor operator:
`(Σᵢⱼ)ₐᵦ = δᵢⱼ δₐᵦ - (3/2) (δᵢₐ δⱼᵦ + δᵢᵦ δⱼₐ)`. -/
lemma spinTensorOperator_spinOneMatrix_apply (i j a b : Fin 3) :
    spinTensorOperator spinOneMatrix i j a b =
      (if i = j ∧ a = b then 1 else 0) -
        (3 / 2 : ℂ) * ((if i = a ∧ j = b then 1 else 0) + (if i = b ∧ j = a then 1 else 0)) := by
  rw [spinTensorOperator_def, sum_spinOneMatrix_mul_self]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [spinOneMatrix_mul_spinOneMatrix_apply]

/-- The spin-one tensor operator is traceless. -/
@[simp]
lemma trace_spinTensorOperator_spinOneMatrix (i j : Fin 3) :
    (spinTensorOperator spinOneMatrix i j).trace = 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [trace_fin_three, spinTensorOperator_spinOneMatrix_apply]

/-- The vector polarization of a spin-one state along the first axis:
`P₀ = i (ρ₁₂ - ρ₂₁)`. -/
lemma vectorPolarization_spinOneMatrix_zero (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    vectorPolarization spinOneMatrix ρ 0 = I * (ρ 1 2 - ρ 2 1) := by
  simp only [vectorPolarization_def, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    spinOneMatrix_apply, epsilon3, Fin.isValue, cons_val', cons_val_fin_one, cons_val_zero,
    cons_val_one, cons_val, ofReal_zero, ofReal_one, ofReal_neg, neg_mul, mul_neg, neg_neg,
    neg_zero, mul_zero, mul_one, zero_add, add_zero]
  ring

/-- The vector polarization of a spin-one state along the second axis:
`P₁ = i (ρ₂₀ - ρ₀₂)`. -/
lemma vectorPolarization_spinOneMatrix_one (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    vectorPolarization spinOneMatrix ρ 1 = I * (ρ 2 0 - ρ 0 2) := by
  simp only [vectorPolarization_def, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    spinOneMatrix_apply, epsilon3, Fin.isValue, cons_val', cons_val_fin_one, cons_val_zero,
    cons_val_one, cons_val, ofReal_zero, ofReal_one, ofReal_neg, neg_mul, mul_neg, neg_neg,
    neg_zero, mul_zero, mul_one, zero_add, add_zero]
  ring

/-- The vector polarization of a spin-one state along the third axis:
`P₂ = i (ρ₀₁ - ρ₁₀)`. -/
lemma vectorPolarization_spinOneMatrix_two (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    vectorPolarization spinOneMatrix ρ 2 = I * (ρ 0 1 - ρ 1 0) := by
  simp only [vectorPolarization_def, trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
    spinOneMatrix_apply, epsilon3, Fin.isValue, cons_val', cons_val_fin_one, cons_val_zero,
    cons_val_one, cons_val, ofReal_zero, ofReal_one, ofReal_neg, neg_mul, mul_neg, neg_neg,
    neg_zero, mul_zero, mul_one, zero_add, add_zero]
  ring

/-- The trace of a `3 × 3` matrix against a spin-one tensor operator:
`tr (M Σᵢⱼ) = δᵢⱼ tr M - (3/2) (Mᵢⱼ + Mⱼᵢ)`. -/
lemma trace_mul_spinTensorOperator_spinOneMatrix (M : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    (M * spinTensorOperator spinOneMatrix i j).trace =
      (if i = j then M.trace else 0) - (3 / 2 : ℂ) * (M i j + M j i) := by
  fin_cases i <;> fin_cases j <;>
    simp only [trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three,
      spinTensorOperator_spinOneMatrix_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Fin.isValue, Fin.reduceEq, true_and, and_true, and_false, false_and, ↓reduceIte, mul_ite,
      mul_one, mul_zero, add_zero, zero_add, sub_zero, zero_sub, sub_self, mul_neg] <;>
    ring

/-- The tensor polarization of a spin-one state in terms of the entries of its density matrix:
`Pᵢⱼ = δᵢⱼ tr ρ - (3/2) (ρᵢⱼ + ρⱼᵢ)`. -/
lemma tensorPolarization_spinOneMatrix (ρ : Matrix (Fin 3) (Fin 3) ℂ) (i j : Fin 3) :
    tensorPolarization spinOneMatrix ρ i j =
      (if i = j then ρ.trace else 0) - (3 / 2 : ℂ) * (ρ i j + ρ j i) :=
  trace_mul_spinTensorOperator_spinOneMatrix ρ i j

/-- The diagonal tensor polarization of a spin-one state: `Pᵢᵢ = tr ρ - 3 ρᵢᵢ`. -/
lemma tensorPolarization_spinOneMatrix_self (ρ : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3) :
    tensorPolarization spinOneMatrix ρ i i = ρ.trace - 3 * ρ i i := by
  rw [tensorPolarization_spinOneMatrix, ite_eq_left rfl]
  ring

/-- The spin-one matrices are orthogonal to the spin-one tensor operators for the trace form. -/
@[simp]
lemma trace_spinOneMatrix_mul_spinTensorOperator_spinOneMatrix (k i j : Fin 3) :
    (spinOneMatrix k * spinTensorOperator spinOneMatrix i j).trace = 0 := by
  rw [trace_mul_spinTensorOperator_spinOneMatrix, spinOneMatrix_apply_swap, trace_spinOneMatrix,
    ite_self, neg_add_cancel, mul_zero, sub_zero]

/-- The Gram matrix of the spin-one tensor operators for the trace form:
`tr (Σᵢⱼ Σₖₗ) = (9/2) (δᵢₖ δⱼₗ + δᵢₗ δⱼₖ) - 3 δᵢⱼ δₖₗ`. -/
lemma trace_spinTensorOperator_mul_spinTensorOperator_spinOneMatrix (i j k l : Fin 3) :
    (spinTensorOperator spinOneMatrix i j * spinTensorOperator spinOneMatrix k l).trace =
      (9 / 2 : ℂ) * ((if i = k ∧ j = l then 1 else 0) + (if i = l ∧ j = k then 1 else 0)) -
        3 * (if i = j ∧ k = l then 1 else 0) := by
  rw [trace_mul_spinTensorOperator_spinOneMatrix, trace_spinTensorOperator_spinOneMatrix,
    spinTensorOperator_spinOneMatrix_apply, spinTensorOperator_spinOneMatrix_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;> norm_num

private lemma mul_mul_neg_I (x y : ℂ) : I * x * (-I * y) = x * y := by
  linear_combination (-(x * y)) * I_sq

/-- The vector-polarization part of a spin-one density matrix is twice its antisymmetric part:
`∑ₖ Pₖ Sₖ = ρ - ρᵀ`. -/
lemma sum_vectorPolarization_smul_spinOneMatrix (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ k, vectorPolarization spinOneMatrix ρ k • spinOneMatrix k = ρ - ρᵀ := by
  ext a b
  simp only [Matrix.sum_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
    vectorPolarization_spinOneMatrix_zero, vectorPolarization_spinOneMatrix_one,
    vectorPolarization_spinOneMatrix_two, Matrix.sub_apply, Matrix.transpose_apply,
    spinOneMatrix_apply, mul_mul_neg_I]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.isValue, epsilon3, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, cons_val',
      cons_val_zero, cons_val_one, cons_val, cons_val_fin_one, ofReal_zero, ofReal_one, ofReal_neg,
      mul_zero, mul_one, mul_neg, add_zero, zero_add, neg_sub, sub_self]

/-- The tensor-polarization part of a spin-one density matrix is nine times its symmetric
traceless part: `∑ᵢⱼ Pᵢⱼ Σᵢⱼ = (9/2) (ρ + ρᵀ) - 3 (tr ρ) 1`. -/
lemma sum_tensorPolarization_smul_spinTensorOperator_spinOneMatrix
    (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    ∑ i, ∑ j, tensorPolarization spinOneMatrix ρ i j • spinTensorOperator spinOneMatrix i j =
      (9 / 2 : ℂ) • (ρ + ρᵀ) - (3 * ρ.trace) • 1 := by
  ext a b
  simp only [Matrix.sum_apply, Fin.sum_univ_three, Matrix.smul_apply, smul_eq_mul,
    tensorPolarization_spinOneMatrix, spinTensorOperator_spinOneMatrix_apply, Matrix.sub_apply,
    Matrix.add_apply, Matrix.transpose_apply, Matrix.one_apply, trace_fin_three]
  fin_cases a <;> fin_cases b <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, and_self,
      and_true, and_false, ↓reduceIte, mul_one, mul_zero, add_zero, zero_add, sub_zero, zero_sub,
      sub_self, mul_neg, neg_mul, neg_neg] <;>
    ring

/-- **Completeness of the spin-one decomposition.** Every `3 × 3` matrix, in particular every
spin-one density matrix, is recovered from its trace, its vector polarization and its tensor
polarization:
`ρ = (tr ρ / 3) 1 + (1/2) ∑ₖ Pₖ Sₖ + (1/9) ∑ᵢⱼ Pᵢⱼ Σᵢⱼ`.
The three terms are the trace part, the antisymmetric part and the symmetric traceless part of
`ρ` (`sum_vectorPolarization_smul_spinOneMatrix`,
`sum_tensorPolarization_smul_spinTensorOperator_spinOneMatrix`). -/
theorem spinOneMatrix_decomposition (ρ : Matrix (Fin 3) (Fin 3) ℂ) :
    ρ = (ρ.trace / 3) • 1 +
      (1 / 2 : ℂ) • ∑ k, vectorPolarization spinOneMatrix ρ k • spinOneMatrix k +
      (1 / 9 : ℂ) • ∑ i, ∑ j,
        tensorPolarization spinOneMatrix ρ i j • spinTensorOperator spinOneMatrix i j := by
  rw [sum_vectorPolarization_smul_spinOneMatrix,
    sum_tensorPolarization_smul_spinTensorOperator_spinOneMatrix]
  module

/-! ### Positivity bounds for spin one -/

section Bounds

open scoped ComplexOrder

variable {ρ : Matrix (Fin 3) (Fin 3) ℂ}

/-- The tensor polarization of a spin-one state is at most one: `Pᵢᵢ ≤ 1`. -/
theorem re_tensorPolarization_spinOneMatrix_le_one (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (i : Fin 3) : (tensorPolarization spinOneMatrix ρ i i).re ≤ 1 := by
  have := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := i))).1
  simp only [tensorPolarization_spinOneMatrix_self, htr, sub_re, one_re, mul_re, re_ofNat,
    im_ofNat, zero_mul, sub_zero]
  linarith

/-- The tensor polarization of a spin-one state is at least minus two: `-2 ≤ Pᵢᵢ`. -/
theorem neg_two_le_re_tensorPolarization_spinOneMatrix (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (i : Fin 3) : -2 ≤ (tensorPolarization spinOneMatrix ρ i i).re := by
  have h0 := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := 0))).1
  have h1 := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := 1))).1
  have h2 := (Complex.nonneg_iff.mp (hρ.diag_nonneg (i := 2))).1
  have : (ρ 0 0).re + (ρ 1 1).re + (ρ 2 2).re = 1 := by
    simpa [trace_fin_three] using congrArg re htr
  simp only [tensorPolarization_spinOneMatrix_self, htr, sub_re, one_re, mul_re, re_ofNat,
    im_ofNat, zero_mul, sub_zero]
  fin_cases i
  · simp only [Fin.zero_eta]
    linarith
  · simp only [Fin.mk_one]
    linarith
  · simp only [Fin.reduceFinMk]
    linarith

/-- **The vector polarization of a spin-one state is bounded by its tensor polarization**:
`3 |Pₖ| ≤ 2 + Pₖₖ`. Since `Pₖₖ ≤ 1`, this gives `|Pₖ| ≤ 1`; and a state with the extreme
tensor polarization `Pₖₖ = -2` has no vector polarization along `k`. -/
theorem three_mul_norm_vectorPolarization_spinOneMatrix_le (hρ : ρ.PosSemidef)
    (htr : ρ.trace = 1) (k : Fin 3) :
    3 * ‖vectorPolarization spinOneMatrix ρ k‖ ≤
      2 + (tensorPolarization spinOneMatrix ρ k k).re := by
  have key (a b : Fin 3) : ‖I * (ρ a b - ρ b a)‖ ≤ (ρ a a).re + (ρ b b).re := by
    rw [norm_mul, norm_I, one_mul]
    have hab := hρ.two_mul_norm_apply_le a b
    have hba := hρ.two_mul_norm_apply_le b a
    simp only [RCLike.re_to_complex] at hab hba
    linarith [norm_sub_le (ρ a b) (ρ b a)]
  have : (ρ 0 0).re + (ρ 1 1).re + (ρ 2 2).re = 1 := by
    simpa [trace_fin_three] using congrArg re htr
  simp only [tensorPolarization_spinOneMatrix_self, htr, sub_re, one_re, mul_re, re_ofNat,
    im_ofNat, zero_mul, sub_zero]
  fin_cases k
  · have := key 1 2
    simp only [Fin.zero_eta, vectorPolarization_spinOneMatrix_zero]
    linarith
  · have := key 2 0
    simp only [Fin.mk_one, vectorPolarization_spinOneMatrix_one]
    linarith
  · have := key 0 1
    simp only [Fin.reduceFinMk, vectorPolarization_spinOneMatrix_two]
    linarith

/-- The pure state of zero spin projection along axis `k`, the projector onto the `k`-th
Cartesian basis vector, has no vector polarization. -/
@[simp]
lemma vectorPolarization_spinOneMatrix_single_same (k l : Fin 3) :
    vectorPolarization spinOneMatrix (single k k 1) l = 0 := by
  simp [vectorPolarization_def, trace_single_mul]

/-- The pure state of zero spin projection along axis `k` has the extreme tensor polarization
`Pₖₖ = -2`, so the bound `neg_two_le_re_tensorPolarization_spinOneMatrix` is sharp. -/
lemma tensorPolarization_spinOneMatrix_single_same (k : Fin 3) :
    tensorPolarization spinOneMatrix (single k k 1) k k = -2 := by
  rw [tensorPolarization_spinOneMatrix_self, trace_single_eq_same, single_apply_same]
  norm_num

/-- The pure state of zero spin projection along an axis `l` perpendicular to `k` has tensor
polarization `Pₖₖ = 1`, so the bound `re_tensorPolarization_spinOneMatrix_le_one` is sharp. -/
lemma tensorPolarization_spinOneMatrix_single_of_ne {k l : Fin 3} (h : l ≠ k) :
    tensorPolarization spinOneMatrix (single l l 1) k k = 1 := by
  rw [tensorPolarization_spinOneMatrix_self, trace_single_eq_same]
  simp [h]

end Bounds

/-! ### Spin one half -/

/-- The **spin-one-half matrices** `Sₖ = σₖ / 2`. -/
def spinHalfMatrix (k : Fin 3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • PauliMatrix.pauliMatrix (Sum.inr k)

lemma spinHalfMatrix_def (k : Fin 3) :
    spinHalfMatrix k = (1 / 2 : ℂ) • PauliMatrix.pauliMatrix (Sum.inr k) := (rfl)

/-- The entries of the spin-one-half matrices are those of the fundamental `su(2)` generators
`su2GenEntry`. -/
lemma spinHalfMatrix_apply (k : Fin 3) (a b : Fin 2) : spinHalfMatrix k a b = su2GenEntry k a b :=
  (rfl)

/-- The Casimir of the spin-one-half matrices is `s (s + 1) = 3/4`: the matrix form of the
fundamental `su(2)` Casimir `su2FundamentalStatement`. -/
lemma sum_spinHalfMatrix_mul_self :
    ∑ k, spinHalfMatrix k * spinHalfMatrix k = (3 / 4 : ℂ) • 1 := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.mul_apply, spinHalfMatrix_apply, su2FundamentalStatement a b,
    su2DeltaFund, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> norm_num

/-- **The spin tensor operator vanishes for spin one half**: `(3/2) {Sᵢ, Sⱼ} = (3/4) δᵢⱼ`, which
is exactly the Casimir term. -/
@[simp]
theorem spinTensorOperator_spinHalfMatrix (i j : Fin 3) :
    spinTensorOperator spinHalfMatrix i j = 0 := by
  have h : spinHalfMatrix i * spinHalfMatrix j + spinHalfMatrix j * spinHalfMatrix i =
      (1 / 4 : ℂ) • (PauliMatrix.pauliMatrix (Sum.inr i) * PauliMatrix.pauliMatrix (Sum.inr j) +
        PauliMatrix.pauliMatrix (Sum.inr j) * PauliMatrix.pauliMatrix (Sum.inr i)) := by
    simp only [spinHalfMatrix_def, smul_mul_smul_comm, ← smul_add]
    norm_num
  rw [spinTensorOperator_def, h, PauliMatrix.pauliMatrix_anticommutator,
    sum_spinHalfMatrix_mul_self]
  by_cases hij : i = j
  · subst hij
    rw [KroneckerDelta.eq_one_of_same, ite_eq_left rfl]
    module
  · rw [KroneckerDelta.eq_zero_of_ne hij, ite_eq_right hij]
    simp

/-- **A spin-one-half target has no tensor polarization.** -/
@[simp]
theorem tensorPolarization_spinHalfMatrix (ρ : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 3) :
    tensorPolarization spinHalfMatrix ρ i j = 0 := by
  rw [tensorPolarization_def, spinTensorOperator_spinHalfMatrix, Matrix.mul_zero, trace_zero]

end EpsilonEridani.Spin
