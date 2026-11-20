/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.Alternating.BilinMap
public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.Nondegenerate
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import Mathlib.LinearAlgebra.Determinant
public import Physlib.Mathematics.LeviCivita.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

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
`-leviCivitaSymbol`, i.e. `ε^{0123} = -1`. Numerically, the covariant components of
`minkowskiVolumeForm` are the values of `leviCivita4UpInt`; the bridge is
`EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivitaVolumeForm`.

Every alternating four-form on Minkowski space is a multiple of this one
(`AlternatingMap.eq_smul_minkowskiVolumeForm`), so statements about contractions of the
Levi-Civita tensor that are even in `ε` do not depend on the convention.

The parity-odd tensor structures of scattering, and the transverse antisymmetric tensor of a
light-cone basis, are contractions of this form with two vectors (`AlternatingMap.bilinMap`).
The contraction with two vectors `a`, `b`, with its second remaining index raised by the Minkowski
metric, is the linear map `minkowskiVolumeFormRaise a b`, characterised by
`⟪minkowskiVolumeFormRaise a b u, v⟫ₘ = ε(u, v, a, b)`
(`minkowskiProduct_minkowskiVolumeFormRaise`); it is built with the same combinator,
`LinearMap.BilinForm.symmCompOfNondegenerate`, as the raised transverse antisymmetric tensor of a
light-cone basis. Applying it twice is a polynomial identity in Minkowski products
(`minkowskiVolumeFormRaise_minkowskiVolumeFormRaise`), the one-index contraction of two
Levi-Civita tensors.

## Main definitions

* `EpsilonEridani.minkowskiBasisFin4`: the standard basis `e₀, e₁, e₂, e₃` of Minkowski space
  indexed by `Fin 4`.
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

/-- The standard basis of four-dimensional Minkowski space indexed by `Fin 4`, with `e₀` the
time direction and `e₁, e₂, e₃` the spatial directions. -/
noncomputable def minkowskiBasisFin4 : Module.Basis (Fin 4) ℝ (Vector 3) :=
  basis.reindex finSumFinEquiv

theorem minkowskiBasisFin4_apply (i : Fin 4) :
    minkowskiBasisFin4 i = basis (finSumFinEquiv.symm i) := by
  simp [minkowskiBasisFin4]

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
  simp [Module.Basis.toMatrix_apply, minkowskiBasisFin4, Lorentz.Vector.basis_repr_apply]

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
    leviCivitaSymbol_eq_det]
  -- `leviCivitaSymbol_eq_det` writes the determinant of a bare `Fin 4 → Fin 4 → ℤ` function,
  -- which `rw` cannot match against the `Matrix`-typed argument of `Int.cast_det` (the `Matrix`
  -- type synonym is not unfolded at `rw`'s transparency); the `change` only inserts the
  -- definitionally equal `Matrix.of` wrapper, exposing the matrix to the cast push.
  change _ = ((Matrix.of fun i j => ((KroneckerDelta.kroneckerDelta (g i) j : ℕ) : ℤ)).det : ℝ)
  rw [Int.cast_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Module.Basis.toMatrix_apply, Finsupp.single_apply,
    KroneckerDelta.kroneckerDelta, eq_comm]

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
  LinearMap.BilinForm.symmCompOfNondegenerate (minkowskiVolumeForm.bilinMap ![a, b])
    (minkowskiProduct (d := 3)).toBilinForm nondegenerate_toBilinForm_minkowskiProduct

/-- Unfolding lemma for `minkowskiVolumeFormRaise`, whose body is not exposed. -/
theorem minkowskiVolumeFormRaise_def (a b : Vector 3) :
    minkowskiVolumeFormRaise a b =
      LinearMap.BilinForm.symmCompOfNondegenerate (minkowskiVolumeForm.bilinMap ![a, b])
        (minkowskiProduct (d := 3)).toBilinForm nondegenerate_toBilinForm_minkowskiProduct :=
  (rfl)

/-- The characteristic property of `minkowskiVolumeFormRaise a b`:
`⟪minkowskiVolumeFormRaise a b u, v⟫ₘ = ε(u, v, a, b)`. -/
@[simp]
theorem minkowskiProduct_minkowskiVolumeFormRaise (a b u v : Vector 3) :
    ⟪minkowskiVolumeFormRaise a b u, v⟫ₘ = minkowskiVolumeForm ![u, v, a, b] := by
  have h := LinearMap.BilinForm.symmCompOfNondegenerate_left_apply
    (minkowskiVolumeForm.bilinMap ![a, b]) nondegenerate_toBilinForm_minkowskiProduct v u
  rw [ContinuousLinearMap.toBilinForm_apply, AlternatingMap.bilinMap_apply] at h
  rwa [minkowskiVolumeFormRaise]

/-- `minkowskiVolumeFormRaise a b u` is the unique vector `w` with `⟪w, v⟫ₘ = ε(u, v, a, b)` for
all `v`. -/
theorem eq_minkowskiVolumeFormRaise_iff {a b u w : Vector 3} :
    w = minkowskiVolumeFormRaise a b u ↔ ∀ v, ⟪w, v⟫ₘ = minkowskiVolumeForm ![u, v, a, b] := by
  rw [minkowskiVolumeFormRaise_def]
  refine (LinearMap.BilinForm.eq_symmCompOfNondegenerate_iff _
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
  rw [minkowskiProduct_minkowskiVolumeFormRaise]
  exact minkowskiVolumeForm.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

/-- `⟪minkowskiVolumeFormRaise a b u, a⟫ₘ = ε(u, a, a, b) = 0`. -/
@[simp high]
theorem minkowskiProduct_minkowskiVolumeFormRaise_left_eq_zero (a b u : Vector 3) :
    ⟪minkowskiVolumeFormRaise a b u, a⟫ₘ = 0 := by
  rw [minkowskiProduct_minkowskiVolumeFormRaise]
  exact minkowskiVolumeForm.map_eq_zero_of_eq _ (i := 1) (j := 2) rfl (by decide)

/-- `⟪minkowskiVolumeFormRaise a b u, b⟫ₘ = ε(u, b, a, b) = 0`. -/
@[simp high]
theorem minkowskiProduct_minkowskiVolumeFormRaise_right_eq_zero (a b u : Vector 3) :
    ⟪minkowskiVolumeFormRaise a b u, b⟫ₘ = 0 := by
  rw [minkowskiProduct_minkowskiVolumeFormRaise]
  exact minkowskiVolumeForm.map_eq_zero_of_eq _ (i := 1) (j := 3) rfl (by decide)

/-- `minkowskiVolumeFormRaise a b` kills `a`. -/
@[simp]
theorem minkowskiVolumeFormRaise_apply_left_eq_zero (a b : Vector 3) :
    minkowskiVolumeFormRaise a b a = 0 := by
  refine (eq_minkowskiVolumeFormRaise_iff.2 fun v => ?_).symm
  rw [map_zero, _root_.zero_apply]
  exact (minkowskiVolumeForm.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)).symm

/-- `minkowskiVolumeFormRaise a b` kills `b`. -/
@[simp]
theorem minkowskiVolumeFormRaise_apply_right_eq_zero (a b : Vector 3) :
    minkowskiVolumeFormRaise a b b = 0 := by
  refine (eq_minkowskiVolumeFormRaise_iff.2 fun v => ?_).symm
  rw [map_zero, _root_.zero_apply]
  exact (minkowskiVolumeForm.map_eq_zero_of_eq _ (i := 0) (j := 3) rfl (by decide)).symm

/-- The contraction of the volume form with the same vector twice vanishes. -/
@[simp]
theorem minkowskiVolumeFormRaise_self (a : Vector 3) : minkowskiVolumeFormRaise a a = 0 := by
  ext1 u
  refine (eq_minkowskiVolumeFormRaise_iff.2 fun v => ?_).symm
  rw [LinearMap.zero_apply, map_zero, _root_.zero_apply]
  exact (minkowskiVolumeForm.map_eq_zero_of_eq _ (i := 2) (j := 3) rfl (by decide)).symm

/-- `minkowskiVolumeFormRaise a b` is antisymmetric in `a` and `b`. -/
theorem minkowskiVolumeFormRaise_swap (a b : Vector 3) :
    minkowskiVolumeFormRaise a b = -minkowskiVolumeFormRaise b a := by
  ext1 u
  refine (eq_minkowskiVolumeFormRaise_iff.2 fun v => ?_).symm
  have h : ![u, v, b, a] = ![u, v, a, b] ∘ Equiv.swap 2 3 := by
    funext i
    fin_cases i <;> rfl
  rw [LinearMap.neg_apply, map_neg, _root_.neg_apply,
    minkowskiProduct_minkowskiVolumeFormRaise, h, minkowskiVolumeForm.map_swap _ (by decide),
    neg_neg]

/-- The components of `minkowskiVolumeFormRaise a b u`:
`(minkowskiVolumeFormRaise a b u)^μ = η^{μμ} ε(u, e_μ, a, b)`. -/
theorem minkowskiVolumeFormRaise_apply (a b u : Vector 3) (μ : Fin 1 ⊕ Fin 3) :
    minkowskiVolumeFormRaise a b u μ =
      minkowskiMatrix μ μ * minkowskiVolumeForm ![u, basis μ, a, b] := by
  rw [minkowskiVolumeFormRaise, symmCompOfNondegenerate_minkowskiProduct_apply,
    AlternatingMap.bilinMap_apply]

/-! The explicit components of `minkowskiVolumeFormRaise a b u`: up to sign, the `μ`-th component
is the `3 × 3` minor of the component matrix of `(u, a, b)` with row `μ` deleted. -/

/-- The time component of `minkowskiVolumeFormRaise a b u`: the minor with the time row deleted. -/
theorem minkowskiVolumeFormRaise_apply_inl (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inl 0) =
      u (Sum.inr 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        + u (Sum.inr 2) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0)) := by
  simp [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, basis_apply]
  ring

/-- The first spatial component of `minkowskiVolumeFormRaise a b u`: the minor with row `1`
deleted. -/
theorem minkowskiVolumeFormRaise_apply_inr_zero (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inr 0) =
      u (Sum.inl 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0)) := by
  simp [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, basis_apply]
  ring

/-- The second spatial component of `minkowskiVolumeFormRaise a b u`: minus the minor with row `2`
deleted. -/
theorem minkowskiVolumeFormRaise_apply_inr_one (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inr 1) =
      -(u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0))) := by
  simp [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, basis_apply]
  ring

/-- The third spatial component of `minkowskiVolumeFormRaise a b u`: the minor with row `3`
deleted. -/
theorem minkowskiVolumeFormRaise_apply_inr_two (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b u (Sum.inr 2) =
      u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0))
        + u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0)) := by
  simp [minkowskiVolumeFormRaise_apply, minkowskiVolumeForm_eq_sum_timeComponent_mul_det,
    Matrix.det_fin_three, basis_apply]
  ring

/-- The square of `minkowskiVolumeFormRaise a b` for arbitrary `a`, `b`: the contraction of two
Levi-Civita tensors over one index, as a polynomial identity in Minkowski products. -/
theorem minkowskiVolumeFormRaise_minkowskiVolumeFormRaise (a b u : Vector 3) :
    minkowskiVolumeFormRaise a b (minkowskiVolumeFormRaise a b u) =
      (⟪a, a⟫ₘ * ⟪b, b⟫ₘ - ⟪a, b⟫ₘ ^ 2) • u - (⟪a, a⟫ₘ * ⟪b, u⟫ₘ) • b
        + ⟪a, b⟫ₘ • (⟪a, u⟫ₘ • b + ⟪b, u⟫ₘ • a) - (⟪b, b⟫ₘ * ⟪a, u⟫ₘ) • a := by
  funext μ
  rcases μ with i | j
  · fin_cases i
    simp [minkowskiVolumeFormRaise_apply_inl, minkowskiVolumeFormRaise_apply_inr_zero,
      minkowskiVolumeFormRaise_apply_inr_one, minkowskiVolumeFormRaise_apply_inr_two,
      minkowskiProduct_toCoord, Fin.sum_univ_three]
    ring
  · fin_cases j <;>
      simp [minkowskiVolumeFormRaise_apply_inl, minkowskiVolumeFormRaise_apply_inr_zero,
        minkowskiVolumeFormRaise_apply_inr_one, minkowskiVolumeFormRaise_apply_inr_two,
        minkowskiProduct_toCoord, Fin.sum_univ_three] <;>
      ring

end EpsilonEridani
