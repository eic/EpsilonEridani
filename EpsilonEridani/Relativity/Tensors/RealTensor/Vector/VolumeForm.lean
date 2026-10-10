/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic

/-!
# The volume form of four-dimensional Minkowski space

The Levi-Civita tensor of `3 + 1`-dimensional Minkowski space as an alternating four-form on
Lorentz vectors: `volumeForm ![a, b, c, d]` is the determinant of the matrix whose columns are the
components of `a`, `b`, `c`, `d` in the standard basis `e₀, e₁, e₂, e₃`, so that
`volumeForm ![e₀, e₁, e₂, e₃] = 1`. In index notation it is `ε_{μνρσ} a^μ b^ν c^ρ d^σ` with
`ε_{0123} = 1`; with the `(+, -, -, -)` metric this is `ε^{0123} = -1`, the convention of
Peskin–Schroeder, so the form is the negative of the contraction of
`realLorentzTensor.leviCivita` (which has `ε⁰¹²³ = 1`) with four vectors. Every alternating
four-form on Minkowski space is a multiple of this one (`AlternatingMap.eq_smul_volumeForm`), so
statements about contractions of the Levi-Civita tensor that are even in `ε` do not depend on
the convention.

The parity-odd tensor structures of scattering, and the transverse antisymmetric tensor of a
light-cone basis, are contractions of this form with two momenta
(`AlternatingMap.bilinMap`).

## Main definitions

* `Lorentz.Vector.volumeForm`: the volume form `ε` of four-dimensional Minkowski space.

## Main statements

* `Lorentz.Vector.volumeForm_apply`: `ε ![a, b, c, d]` as the determinant of the component matrix.
* `Lorentz.Vector.volumeForm_eq_det_fin_three`: its Laplace expansion along the time components.
* `Lorentz.Vector.volumeForm_basis`: `ε(e₀, e₁, e₂, e₃) = 1`.
* `AlternatingMap.eq_smul_volumeForm`: every alternating four-form on Minkowski space is a multiple
  of the volume form.

## References

* M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory*, Westview Press
  (1995), for the sign convention `ε^{0123} = -1`.
-/

public section

namespace Lorentz.Vector

/-- The standard basis of four-dimensional Minkowski space indexed by `Fin 4`, with `e₀` the
time direction and `e₁, e₂, e₃` the spatial directions. -/
noncomputable abbrev basisFin4 : Module.Basis (Fin 4) ℝ (Vector 3) :=
  basis.reindex finSumFinEquiv

/-- The volume form `ε` of four-dimensional Minkowski space: the determinant of the components in
the standard basis, normalised by `ε(e₀, e₁, e₂, e₃) = 1`. -/
noncomputable def volumeForm : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ :=
  basisFin4.det

/-- The volume form as the determinant of the matrix of components, `(v j)^i` in row `i` and
column `j`. -/
theorem volumeForm_apply (v : Fin 4 → Vector 3) :
    volumeForm v = Matrix.det (Matrix.of fun i j =>
      v j (![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2] i)) := by
  -- The index of `Fin 1 ⊕ Fin 3` labelling the `i`-th standard basis vector.
  have h : ⇑(finSumFinEquiv (m := 1) (n := 3)).symm =
      ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2] := by
    ext i
    fin_cases i <;> rfl
  rw [volumeForm, Module.Basis.det_apply]
  congr 1
  ext i j
  simp only [Module.Basis.toMatrix_apply, Module.Basis.repr_reindex_apply, basis_repr_apply,
    Matrix.of_apply, h]

/-- The Laplace expansion of the volume form along the time components: `ε(x, y, z, w)` is the
alternating sum of the time components times the `3 × 3` determinants of the spatial components
of the other three vectors. -/
theorem volumeForm_eq_det_fin_three (x y z w : Vector 3) :
    volumeForm ![x, y, z, w] =
      x (Sum.inl 0) * Matrix.det !![y (Sum.inr 0), z (Sum.inr 0), w (Sum.inr 0);
          y (Sum.inr 1), z (Sum.inr 1), w (Sum.inr 1);
          y (Sum.inr 2), z (Sum.inr 2), w (Sum.inr 2)]
      - y (Sum.inl 0) * Matrix.det !![x (Sum.inr 0), z (Sum.inr 0), w (Sum.inr 0);
          x (Sum.inr 1), z (Sum.inr 1), w (Sum.inr 1);
          x (Sum.inr 2), z (Sum.inr 2), w (Sum.inr 2)]
      + z (Sum.inl 0) * Matrix.det !![x (Sum.inr 0), y (Sum.inr 0), w (Sum.inr 0);
          x (Sum.inr 1), y (Sum.inr 1), w (Sum.inr 1);
          x (Sum.inr 2), y (Sum.inr 2), w (Sum.inr 2)]
      - w (Sum.inl 0) * Matrix.det !![x (Sum.inr 0), y (Sum.inr 0), z (Sum.inr 0);
          x (Sum.inr 1), y (Sum.inr 1), z (Sum.inr 1);
          x (Sum.inr 2), y (Sum.inr 2), z (Sum.inr 2)] := by
  -- The index bookkeeping of the Laplace expansion, tabulated on `Fin 4`.
  have hsuccAbove : ∀ (j : Fin 4) (k : Fin 3),
      Fin.succAbove j k = ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]] j k := by
    decide
  have hsucc : ∀ k : Fin 3, Fin.succ k = ![1, 2, 3] k := by decide
  have hsign : ∀ j : Fin 4, (-1 : ℝ) ^ (j : ℕ) = ![1, -1, 1, -1] j := by
    intro j
    fin_cases j <;> norm_num
  rw [volumeForm_apply, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply, hsuccAbove, hsucc,
    hsign, Matrix.cons_val]
  ring

theorem volumeForm_basis : volumeForm basisFin4 = 1 :=
  basisFin4.det_self

/-- Every alternating four-form on four-dimensional Minkowski space is the multiple of the volume
form by its value `ε(e₀, e₁, e₂, e₃)` on the standard basis. -/
theorem _root_.AlternatingMap.eq_smul_volumeForm (ε : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ) :
    ε = ε basisFin4 • volumeForm :=
  ε.eq_smul_basis_det basisFin4

end Lorentz.Vector
