/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.Alternating.BilinMap
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import Mathlib.LinearAlgebra.Determinant
public import PhyslibAlpha.Mathematics.LeviCivita.Basic

/-!
# The volume form of four-dimensional Minkowski space

The Levi-Civita tensor of `3 + 1`-dimensional Minkowski space as an alternating four-form on
Lorentz vectors, `minkowskiVolumeForm ![a, b, c, d] = ε_{μνρσ} a^μ b^ν c^ρ d^σ`.

The sign convention is that of Physlib's Levi-Civita tensor `realLorentzTensor.leviCivita`
(`Physlib.Relativity.Tensors.LeviCivita.Basic`), whose contravariant components are
`ε^{μνρσ} = leviCivitaSymbol (μ, ν, ρ, σ)`, so `ε^{0123} = +1`. This is also the convention of
Peskin–Schroeder, and the one in which the `γ₅` trace identity
`trace_γ5_mul_γ_mul_γ_mul_γ_mul_γ` reads `tr(γ₅ γ^μ γ^ν γ^ρ γ^σ) = -4i ε^{μνρσ}`. Lowering all
four indices with the `(+, -, -, -)` metric multiplies by `det η = -1`, so the covariant components
contracted here are `ε_{μνρσ} = -leviCivitaSymbol (μ, ν, ρ, σ)`
(`minkowskiVolumeForm_minkowskiBasisFin4_comp`), and `ε_{0123} = -1`
(`minkowskiVolumeForm_minkowskiBasisFin4`): `minkowskiVolumeForm` is minus the determinant of the
components in the standard basis `e₀, e₁, e₂, e₃`.

The integer Levi-Civita symbols of
`EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita` use the opposite convention:
`realLorentzTensor.leviCivita4UpInt`, documented there as the contravariant symbol, is
`-leviCivitaSymbol`, i.e. `ε^{0123} = -1`, while the covariant components of `minkowskiVolumeForm`
are `-leviCivita4Int`, as
`EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita.VolumeForm` proves
(`EpsilonEridani.minkowskiVolumeForm_minkowskiBasisFin4_eq_neg_leviCivita4Int`).

Every alternating four-form on Minkowski space is a multiple of this one
(`AlternatingMap.eq_smul_minkowskiVolumeForm`), so statements about contractions of the
Levi-Civita tensor that are even in `ε` do not depend on the convention.

The parity-odd tensor structures of scattering, and the transverse antisymmetric tensor of a
light-cone basis, are contractions of this form with two vectors (`AlternatingMap.bilinMap`).
The contraction with two vectors `a`, `b`, with its second remaining index raised by the Minkowski
metric, is the linear map `minkowskiVolumeFormRaise a b`, characterised by
`⟪minkowskiVolumeFormRaise a b u, v⟫ₘ = ε(u, v, a, b)`
(`minkowskiProduct_minkowskiVolumeFormRaise`); it is `AlternatingMap.bilinMapRaise`, the same
construction as the raised transverse antisymmetric tensor of a light-cone basis. Applying it
twice is a polynomial identity in Minkowski products
(`minkowskiVolumeFormRaise_minkowskiVolumeFormRaise`), the one-index contraction of two
Levi-Civita tensors.

## Main definitions

* `EpsilonEridani.minkowskiVolumeForm`: the volume form `ε` of four-dimensional Minkowski space,
  with `ε^{0123} = +1`.
* `EpsilonEridani.minkowskiVolumeFormRaise`: the linear map `u ↦ ε_ν{}^μ{}_{ρσ} u^ν a^ρ b^σ`.

## Main statements

* `EpsilonEridani.minkowskiVolumeForm_apply`: `ε ![a, b, c, d]` as minus the determinant of the
  component matrix.
* `EpsilonEridani.minkowskiVolumeForm_eq_sum_timeComponent_mul_det`: its Laplace expansion along
  the time components.
* `EpsilonEridani.minkowskiVolumeForm_minkowskiBasisFin4_comp`: the components
  `ε_{μνρσ} = -leviCivitaSymbol`.
* `EpsilonEridani.minkowskiVolumeForm_minkowskiBasisFin4`: `ε(e₀, e₁, e₂, e₃) = -1`.
* `AlternatingMap.eq_smul_minkowskiVolumeForm`: every alternating four-form on Minkowski space is a
  multiple of the volume form.
* `EpsilonEridani.minkowskiProduct_minkowskiVolumeFormRaise`: the characteristic property
  `⟪minkowskiVolumeFormRaise a b u, v⟫ₘ = ε(u, v, a, b)`.
* `EpsilonEridani.eq_minkowskiVolumeFormRaise_iff`: `minkowskiVolumeFormRaise a b u` is the unique
  vector with this property.
* `EpsilonEridani.minkowskiVolumeFormRaise_apply_left_eq_zero`,
  `EpsilonEridani.minkowskiVolumeFormRaise_apply_right_eq_zero`,
  `EpsilonEridani.minkowskiVolumeFormRaise_self`, `EpsilonEridani.minkowskiVolumeFormRaise_swap`:
  it kills `a` and `b`, vanishes for `a = b`, and is antisymmetric in `a` and `b`.
* `EpsilonEridani.minkowskiVolumeFormRaise_apply`: its components `η^{μμ} ε(u, e_μ, a, b)`.
* `EpsilonEridani.minkowskiVolumeFormRaise_minkowskiVolumeFormRaise`: the square of
  `minkowskiVolumeFormRaise a b`.

## References

* M. E. Peskin and D. V. Schroeder, *An Introduction to Quantum Field Theory*, Westview Press
  (1995), Notations and Conventions, for the sign convention `ε^{0123} = +1`.
-/

public section

namespace EpsilonEridani

open Lorentz Vector
open scoped Lorentz.Vector

/-- The volume form `ε` of four-dimensional Minkowski space, `ε(a, b, c, d) = ε_{μνρσ} a^μ b^ν c^ρ
d^σ` with `ε^{0123} = +1`, hence `ε_{0123} = -1`: minus the determinant of the components in the
standard basis. -/
noncomputable def minkowskiVolumeForm : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ :=
  -minkowskiBasisFin4.det

/-- The volume form as minus the determinant of the matrix of components, `(v j)^i` in row `i` and
column `j`. -/
theorem minkowskiVolumeForm_apply (v : Fin 4 → Vector 3) :
    minkowskiVolumeForm v = -Matrix.det (Matrix.of fun i j => v j (finSumFinEquiv.symm i)) := by
  rw [minkowskiVolumeForm, _root_.neg_apply, Module.Basis.det_apply, neg_inj]
  refine congrArg Matrix.det ?_
  ext i j
  simp [Module.Basis.toMatrix_apply]

/-- The Laplace expansion of the volume form along the time components: `ε(x, y, z, w)` is minus
the alternating sum of the time components times the `3 × 3` determinants of the spatial
components of the other three vectors. -/
theorem minkowskiVolumeForm_eq_sum_timeComponent_mul_det (x y z w : Vector 3) :
    minkowskiVolumeForm ![x, y, z, w] =
      -x (Sum.inl 0) * Matrix.det !![y (Sum.inr 0), z (Sum.inr 0), w (Sum.inr 0);
          y (Sum.inr 1), z (Sum.inr 1), w (Sum.inr 1);
          y (Sum.inr 2), z (Sum.inr 2), w (Sum.inr 2)]
      + y (Sum.inl 0) * Matrix.det !![x (Sum.inr 0), z (Sum.inr 0), w (Sum.inr 0);
          x (Sum.inr 1), z (Sum.inr 1), w (Sum.inr 1);
          x (Sum.inr 2), z (Sum.inr 2), w (Sum.inr 2)]
      - z (Sum.inl 0) * Matrix.det !![x (Sum.inr 0), y (Sum.inr 0), w (Sum.inr 0);
          x (Sum.inr 1), y (Sum.inr 1), w (Sum.inr 1);
          x (Sum.inr 2), y (Sum.inr 2), w (Sum.inr 2)]
      + w (Sum.inl 0) * Matrix.det !![x (Sum.inr 0), y (Sum.inr 0), z (Sum.inr 0);
          x (Sum.inr 1), y (Sum.inr 1), z (Sum.inr 1);
          x (Sum.inr 2), y (Sum.inr 2), z (Sum.inr 2)] := by
  -- The index bookkeeping of the Laplace expansion, tabulated on `Fin 4`.
  have h : ⇑(finSumFinEquiv (m := 1) (n := 3)).symm =
      ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2] := by
    ext i
    fin_cases i <;> rfl
  have hsuccAbove : ∀ (j : Fin 4) (k : Fin 3),
      Fin.succAbove j k = ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]] j k := by
    decide
  have hsucc : ∀ k : Fin 3, Fin.succ k = ![1, 2, 3] k := by decide
  have hsign : ∀ j : Fin 4, (-1 : ℝ) ^ (j : ℕ) = ![1, -1, 1, -1] j := by
    intro j
    fin_cases j <;> norm_num
  rw [minkowskiVolumeForm_apply, h, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply, hsuccAbove, hsucc,
    hsign, Matrix.cons_val]
  ring

/-- The components of the volume form in the standard basis: `ε_{μνρσ} = -leviCivitaSymbol (μ, ν,
ρ, σ)`, the covariant form of Physlib's `realLorentzTensor.leviCivita`, whose contravariant
components are `leviCivitaSymbol` (`realLorentzTensor.leviCivita_basis_repr_eq_leviCivitaSymbol`).
-/
theorem minkowskiVolumeForm_minkowskiBasisFin4_comp (g : Fin 4 → Fin 4) :
    minkowskiVolumeForm (fun i => minkowskiBasisFin4 (g i)) = -(leviCivitaSymbol g : ℝ) := by
  rw [minkowskiVolumeForm, _root_.neg_apply, Module.Basis.det_apply, neg_inj,
    cast_leviCivitaSymbol, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Module.Basis.toMatrix_apply, Finsupp.single_apply, eq_comm]

/-- The normalisation of the volume form: `ε(e₀, e₁, e₂, e₃) = ε_{0123} = -1`. -/
@[simp]
theorem minkowskiVolumeForm_minkowskiBasisFin4 : minkowskiVolumeForm minkowskiBasisFin4 = -1 := by
  rw [minkowskiVolumeForm, _root_.neg_apply, minkowskiBasisFin4.det_self]

/-- Every alternating four-form on four-dimensional Minkowski space is the multiple of the volume
form by minus its value `ε(e₀, e₁, e₂, e₃)` on the standard basis. -/
theorem _root_.AlternatingMap.eq_smul_minkowskiVolumeForm (ε : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ) :
    ε = -ε minkowskiBasisFin4 • minkowskiVolumeForm := by
  nth_rewrite 1 [ε.eq_smul_basis_det minkowskiBasisFin4]
  ext v
  simp [minkowskiVolumeForm]

/-! ### The volume form contracted with three vectors -/

/-- The contraction `u ↦ ε_ν{}^μ{}_{ρσ} u^ν a^ρ b^σ` of the volume form with `a` and `b`, with its
second index raised by the Minkowski metric: the bilinear form `(u, v) ↦ ε(u, v, a, b)` turned into
the endomorphism `E` with `⟪E u, v⟫ₘ = ε(u, v, a, b)`
(`minkowskiProduct_minkowskiVolumeFormRaise`). -/
noncomputable def minkowskiVolumeFormRaise (a b : Vector 3) : Vector 3 →ₗ[ℝ] Vector 3 :=
  minkowskiVolumeForm.bilinMapRaise ![a, b] nondegenerate_toBilinForm_minkowskiProduct

/-- Unfolding lemma for `minkowskiVolumeFormRaise`, whose body is not exposed. -/
theorem minkowskiVolumeFormRaise_def (a b : Vector 3) :
    minkowskiVolumeFormRaise a b =
      minkowskiVolumeForm.bilinMapRaise ![a, b] nondegenerate_toBilinForm_minkowskiProduct :=
  (rfl)

/-- The characteristic property of `minkowskiVolumeFormRaise a b`:
`⟪minkowskiVolumeFormRaise a b u, v⟫ₘ = ε(u, v, a, b)`. -/
@[simp]
theorem minkowskiProduct_minkowskiVolumeFormRaise (a b u v : Vector 3) :
    ⟪minkowskiVolumeFormRaise a b u, v⟫ₘ = minkowskiVolumeForm ![u, v, a, b] := by
  rw [minkowskiVolumeFormRaise_def, AlternatingMap.minkowskiProduct_bilinMapRaise,
    AlternatingMap.bilinMap_apply]

/-- `minkowskiVolumeFormRaise a b u` is the unique vector `w` with `⟪w, v⟫ₘ = ε(u, v, a, b)` for
all `v`. -/
theorem eq_minkowskiVolumeFormRaise_iff {a b u w : Vector 3} :
    w = minkowskiVolumeFormRaise a b u ↔ ∀ v, ⟪w, v⟫ₘ = minkowskiVolumeForm ![u, v, a, b] := by
  rw [minkowskiVolumeFormRaise_def]
  refine (minkowskiVolumeForm.eq_bilinMapRaise_iff _
    nondegenerate_toBilinForm_minkowskiProduct).trans (forall_congr' fun v => ?_)
  simp only [ContinuousLinearMap.toBilinForm_apply, AlternatingMap.bilinMap_apply]

/-! The next three lemmas have the same discrimination-tree keys as the more general
`minkowskiProduct_minkowskiVolumeFormRaise`, which would otherwise rewrite first to a value of
`minkowskiVolumeForm` that `simp` cannot see to be zero; their higher priority makes `simp` close
these pairings directly. -/

/-- `⟪minkowskiVolumeFormRaise a b u, u⟫ₘ = ε(u, u, a, b) = 0`. -/
@[simp high]
theorem minkowskiProduct_minkowskiVolumeFormRaise_self (a b u : Vector 3) :
    ⟪minkowskiVolumeFormRaise a b u, u⟫ₘ = 0 := by
  rw [minkowskiProduct_minkowskiVolumeFormRaise, ← AlternatingMap.bilinMap_apply]
  exact minkowskiVolumeForm.bilinMap_apply_self ![a, b] u

/-- `⟪minkowskiVolumeFormRaise a b u, a⟫ₘ = ε(u, a, a, b) = 0`. -/
@[simp high]
theorem minkowskiProduct_minkowskiVolumeFormRaise_left_eq_zero (a b u : Vector 3) :
    ⟪minkowskiVolumeFormRaise a b u, a⟫ₘ = 0 := by
  rw [minkowskiProduct_minkowskiVolumeFormRaise, ← AlternatingMap.bilinMap_apply]
  exact minkowskiVolumeForm.bilinMap_apply_right_eq_zero ![a, b] 0 u

/-- `⟪minkowskiVolumeFormRaise a b u, b⟫ₘ = ε(u, b, a, b) = 0`. -/
@[simp high]
theorem minkowskiProduct_minkowskiVolumeFormRaise_right_eq_zero (a b u : Vector 3) :
    ⟪minkowskiVolumeFormRaise a b u, b⟫ₘ = 0 := by
  rw [minkowskiProduct_minkowskiVolumeFormRaise, ← AlternatingMap.bilinMap_apply]
  exact minkowskiVolumeForm.bilinMap_apply_right_eq_zero ![a, b] 1 u

/-- `minkowskiVolumeFormRaise a b` kills `a`. -/
@[simp]
theorem minkowskiVolumeFormRaise_apply_left_eq_zero (a b : Vector 3) :
    minkowskiVolumeFormRaise a b a = 0 := by
  rw [minkowskiVolumeFormRaise_def]
  exact minkowskiVolumeForm.bilinMapRaise_apply_eq_zero ![a, b] _ 0

/-- `minkowskiVolumeFormRaise a b` kills `b`. -/
@[simp]
theorem minkowskiVolumeFormRaise_apply_right_eq_zero (a b : Vector 3) :
    minkowskiVolumeFormRaise a b b = 0 := by
  rw [minkowskiVolumeFormRaise_def]
  exact minkowskiVolumeForm.bilinMapRaise_apply_eq_zero ![a, b] _ 1

/-- The contraction of the volume form with the same vector twice vanishes. -/
@[simp]
theorem minkowskiVolumeFormRaise_self (a : Vector 3) : minkowskiVolumeFormRaise a a = 0 := by
  rw [minkowskiVolumeFormRaise_def]
  exact minkowskiVolumeForm.bilinMapRaise_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

/-- `minkowskiVolumeFormRaise a b` is antisymmetric in `a` and `b`. -/
theorem minkowskiVolumeFormRaise_swap (a b : Vector 3) :
    minkowskiVolumeFormRaise a b = -minkowskiVolumeFormRaise b a := by
  have h : ![a, b] = ![b, a] ∘ Equiv.swap 0 1 := (Matrix.cons_cons_comp_swap_zero_one b a ![]).symm
  rw [minkowskiVolumeFormRaise_def, minkowskiVolumeFormRaise_def, h]
  exact minkowskiVolumeForm.bilinMapRaise_comp_swap _ _ (by decide)

/-- The components of `minkowskiVolumeFormRaise a b u`:
`(minkowskiVolumeFormRaise a b u)^μ = η^{μμ} ε(u, e_μ, a, b)`. -/
theorem minkowskiVolumeFormRaise_apply (a b u : Vector 3) (μ : Fin 1 ⊕ Fin 3) :
    minkowskiVolumeFormRaise a b u μ =
      minkowskiMatrix μ μ * minkowskiVolumeForm ![u, basis μ, a, b] := by
  rw [minkowskiVolumeFormRaise_def, AlternatingMap.bilinMapRaise_minkowskiProduct_apply]

/-! The explicit components of `minkowskiVolumeFormRaise a b u`: up to sign, the `μ`-th component
is the `3 × 3` minor of the component matrix of `(u, a, b)` with row `μ` deleted. -/

/-- The time component of `minkowskiVolumeFormRaise a b u`: the minor with the time row deleted. -/
theorem minkowskiVolumeFormRaise_apply_inl (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inl 0) =
      u (Sum.inr 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        + u (Sum.inr 2) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0)) := by
  simp only [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val, basis_apply,
    minkowskiMatrix.inl_0_inl_0, reduceCtorEq, ↓reduceIte, Fin.isValue]
  ring

/-- The first spatial component of `minkowskiVolumeFormRaise a b u`: the minor with row `1`
deleted. -/
theorem minkowskiVolumeFormRaise_apply_inr_zero (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inr 0) =
      u (Sum.inl 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0)) := by
  simp only [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val, basis_apply,
    minkowskiMatrix.inr_i_inr_i, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, zero_ne_one, ↓reduceIte,
    Fin.isValue]
  ring

/-- The second spatial component of `minkowskiVolumeFormRaise a b u`: minus the minor with row `2`
deleted. -/
theorem minkowskiVolumeFormRaise_apply_inr_one (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inr 1) =
      -(u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0))) := by
  simp only [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val, basis_apply,
    minkowskiMatrix.inr_i_inr_i, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, one_ne_zero, ↓reduceIte,
    Fin.isValue]
  ring

/-- The third spatial component of `minkowskiVolumeFormRaise a b u`: the minor with row `3`
deleted. -/
theorem minkowskiVolumeFormRaise_apply_inr_two (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inr 2) =
      u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0))
        + u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0)) := by
  simp only [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.cons_val, basis_apply,
    minkowskiMatrix.inr_i_inr_i, Sum.inr.injEq, reduceCtorEq, Fin.reduceEq, ↓reduceIte, Fin.isValue]
  ring

/-- The square of `minkowskiVolumeFormRaise a b` for arbitrary `a`, `b`: the contraction of two
Levi-Civita tensors over one index, as a polynomial identity in Minkowski products. -/
theorem minkowskiVolumeFormRaise_minkowskiVolumeFormRaise (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b (minkowskiVolumeFormRaise a b u) =
      (⟪a, a⟫ₘ * ⟪b, b⟫ₘ - ⟪a, b⟫ₘ ^ 2) • u - (⟪a, a⟫ₘ * ⟪b, u⟫ₘ) • b
        + ⟪a, b⟫ₘ • (⟪a, u⟫ₘ • b + ⟪b, u⟫ₘ • a) - (⟪b, b⟫ₘ * ⟪a, u⟫ₘ) • a := by
  ext μ
  rcases μ with i | j
  · fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, minkowskiVolumeFormRaise_apply_inl,
      minkowskiVolumeFormRaise_apply_inr_zero, minkowskiVolumeFormRaise_apply_inr_one,
      minkowskiVolumeFormRaise_apply_inr_two, minkowskiProduct_toCoord, Fin.sum_univ_three,
      apply_add, apply_sub, apply_smul]
    ring
  · fin_cases j <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
        minkowskiVolumeFormRaise_apply_inl, minkowskiVolumeFormRaise_apply_inr_zero,
        minkowskiVolumeFormRaise_apply_inr_one, minkowskiVolumeFormRaise_apply_inr_two,
        minkowskiProduct_toCoord, Fin.sum_univ_three, apply_add, apply_sub, apply_smul] <;>
      ring

end EpsilonEridani
