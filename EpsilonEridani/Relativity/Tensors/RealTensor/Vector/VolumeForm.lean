/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.Alternating.BilinMap
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import Mathlib.LinearAlgebra.Determinant
public import Physlib.Mathematics.LeviCivita.Basic
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# The volume form of four-dimensional Minkowski space

The Levi-Civita tensor of `3 + 1`-dimensional Minkowski space as an alternating four-form on
Lorentz vectors, `volumeForm ![a, b, c, d] = ε_{μνρσ} a^μ b^ν c^ρ d^σ`.

The sign convention is that of Physlib's Levi-Civita tensor `realLorentzTensor.leviCivita`
(`Physlib.Relativity.Tensors.LeviCivita.Basic`), whose contravariant components are
`ε^{μνρσ} = leviCivitaSymbol (μ, ν, ρ, σ)`, so `ε^{0123} = +1`. This is also the convention of
Peskin–Schroeder, and the one in which the `γ₅` trace identity
`trace_γ5_mul_γ_mul_γ_mul_γ_mul_γ` reads `tr(γ₅ γ^μ γ^ν γ^ρ γ^σ) = -4i ε^{μνρσ}`. Lowering all
four indices with the `(+, -, -, -)` metric multiplies by `det η = -1`, so the covariant components
contracted here are `ε_{μνρσ} = -leviCivitaSymbol (μ, ν, ρ, σ)`
(`volumeForm_minkowskiBasisFin4_comp`), and `ε_{0123} = -1` (`volumeForm_minkowskiBasisFin4`):
`volumeForm` is minus the determinant of the components in the standard basis `e₀, e₁, e₂, e₃`.

The integer Levi-Civita symbols of `EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivita`
use the opposite convention: `realLorentzTensor.leviCivita4UpInt`, documented there as the
contravariant symbol, is `-leviCivitaSymbol`, i.e. `ε^{0123} = -1`. Numerically, the covariant
components of `volumeForm` are the values of `leviCivita4UpInt`; the bridge is
`EpsilonEridani.Relativity.Tensors.RealTensor.Metrics.LeviCivitaVolumeForm`.

Every alternating four-form on Minkowski space is a multiple of this one
(`AlternatingMap.eq_smul_volumeForm`), so statements about contractions of the Levi-Civita tensor
that are even in `ε` do not depend on the convention.

The parity-odd tensor structures of scattering, and the transverse antisymmetric tensor of a
light-cone basis, are contractions of this form with two vectors (`AlternatingMap.bilinMap`).
The contraction with two vectors `a`, `b`, with its second remaining index raised by the Minkowski
metric, is the linear map `volumeFormRaise a b`, characterised by
`⟪volumeFormRaise a b u, v⟫ₘ = ε(u, v, a, b)` (`minkowskiProduct_volumeFormRaise`); it is built
with the same combinator, `LinearMap.BilinForm.symmCompOfNondegenerate`, as the raised transverse
antisymmetric tensor of a light-cone basis. Applying it twice is a polynomial identity in Minkowski
products (`volumeFormRaise_volumeFormRaise`), the one-index contraction of two Levi-Civita
tensors.

## Main definitions

* `EpsilonEridani.minkowskiBasisFin4`: the standard basis `e₀, e₁, e₂, e₃` of Minkowski space
  indexed by `Fin 4`.
* `EpsilonEridani.volumeForm`: the volume form `ε` of four-dimensional Minkowski space, with
  `ε^{0123} = +1`.
* `EpsilonEridani.volumeFormRaise`: the linear map `u ↦ ε_ν{}^μ{}_{ρσ} u^ν a^ρ b^σ`.

## Main statements

* `EpsilonEridani.volumeForm_apply`: `ε ![a, b, c, d]` as minus the determinant of the component
  matrix.
* `EpsilonEridani.volumeForm_eq_sum_timeComponent_mul_det`: its Laplace expansion along the time
  components.
* `EpsilonEridani.volumeForm_minkowskiBasisFin4_comp`: the components
  `ε_{μνρσ} = -leviCivitaSymbol`.
* `EpsilonEridani.volumeForm_minkowskiBasisFin4`: `ε(e₀, e₁, e₂, e₃) = -1`.
* `AlternatingMap.eq_smul_volumeForm`: every alternating four-form on Minkowski space is a multiple
  of the volume form.
* `EpsilonEridani.minkowskiProduct_volumeFormRaise`: the characteristic property
  `⟪volumeFormRaise a b u, v⟫ₘ = ε(u, v, a, b)`.
* `EpsilonEridani.volumeFormRaise_apply`: its components `η^{μμ} ε(u, e_μ, a, b)`.
* `EpsilonEridani.volumeFormRaise_volumeFormRaise`: the square of `volumeFormRaise a b`.

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
noncomputable def volumeForm : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ :=
  -minkowskiBasisFin4.det

/-- The volume form as minus the determinant of the matrix of components, `(v j)^i` in row `i` and
column `j`. -/
theorem volumeForm_apply (v : Fin 4 → Vector 3) :
    volumeForm v = -Matrix.det (Matrix.of fun i j => v j (finSumFinEquiv.symm i)) := by
  rw [volumeForm, _root_.neg_apply, Module.Basis.det_apply, neg_inj]
  congr 1
  ext i j
  simp [Module.Basis.toMatrix_apply, minkowskiBasisFin4, Module.Basis.repr_reindex_apply,
    Lorentz.Vector.basis_repr_apply]

/-- The Laplace expansion of the volume form along the time components: `ε(x, y, z, w)` is minus
the alternating sum of the time components times the `3 × 3` determinants of the spatial
components of the other three vectors. -/
theorem volumeForm_eq_sum_timeComponent_mul_det (x y z w : Vector 3) :
    volumeForm ![x, y, z, w] =
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
  rw [volumeForm_apply, h, Matrix.det_succ_row_zero, Fin.sum_univ_four]
  simp only [Matrix.det_fin_three, Matrix.submatrix_apply, Matrix.of_apply, hsuccAbove, hsucc,
    hsign, Matrix.cons_val]
  ring

/-- The components of the volume form in the standard basis: `ε_{μνρσ} = -leviCivitaSymbol (μ, ν,
ρ, σ)`, the covariant form of Physlib's `realLorentzTensor.leviCivita`, whose contravariant
components are `leviCivitaSymbol` (`realLorentzTensor.leviCivita_basis_repr_eq_leviCivitaSymbol`).
-/
theorem volumeForm_minkowskiBasisFin4_comp (g : Fin 4 → Fin 4) :
    volumeForm (fun i => minkowskiBasisFin4 (g i)) = -(leviCivitaSymbol g : ℝ) := by
  rw [volumeForm, _root_.neg_apply, Module.Basis.det_apply, neg_inj,
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
theorem volumeForm_minkowskiBasisFin4 : volumeForm minkowskiBasisFin4 = -1 := by
  rw [volumeForm, _root_.neg_apply, minkowskiBasisFin4.det_self]

/-- Every alternating four-form on four-dimensional Minkowski space is the multiple of the volume
form by minus its value `ε(e₀, e₁, e₂, e₃)` on the standard basis. -/
theorem _root_.AlternatingMap.eq_smul_volumeForm (ε : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ) :
    ε = -ε minkowskiBasisFin4 • volumeForm := by
  nth_rewrite 1 [ε.eq_smul_basis_det minkowskiBasisFin4]
  ext v
  simp [volumeForm]

/-! ### The volume form contracted with three vectors -/

/-- The contraction `u ↦ ε_ν{}^μ{}_{ρσ} u^ν a^ρ b^σ` of the volume form with `a` and `b`, with its
second index raised by the Minkowski metric: the bilinear form `(u, v) ↦ ε(u, v, a, b)` turned into
the endomorphism `E` with `⟪E u, v⟫ₘ = ε(u, v, a, b)` (`minkowskiProduct_volumeFormRaise`). -/
noncomputable def volumeFormRaise (a b : Vector 3) : Vector 3 →ₗ[ℝ] Vector 3 :=
  LinearMap.BilinForm.symmCompOfNondegenerate (volumeForm.bilinMap ![a, b])
    (minkowskiProduct (d := 3)).toBilinForm nondegenerate_toBilinForm_minkowskiProduct

/-- The characteristic property of `volumeFormRaise a b`: `⟪volumeFormRaise a b u, v⟫ₘ =
ε(u, v, a, b)`. -/
@[simp]
theorem minkowskiProduct_volumeFormRaise (a b u v : Vector 3) :
    ⟪volumeFormRaise a b u, v⟫ₘ = volumeForm ![u, v, a, b] := by
  have h := LinearMap.BilinForm.symmCompOfNondegenerate_left_apply (volumeForm.bilinMap ![a, b])
    nondegenerate_toBilinForm_minkowskiProduct v u
  rw [ContinuousLinearMap.toBilinForm_apply, AlternatingMap.bilinMap_apply] at h
  rwa [volumeFormRaise]

/-- The components of `volumeFormRaise a b u`: `(volumeFormRaise a b u)^μ = η^{μμ} ε(u, e_μ, a, b)`.
-/
theorem volumeFormRaise_apply (a b u : Vector 3) (μ : Fin 1 ⊕ Fin 3) :
    volumeFormRaise a b u μ = minkowskiMatrix μ μ * volumeForm ![u, basis μ, a, b] := by
  rw [volumeFormRaise, symmCompOfNondegenerate_minkowskiProduct_apply,
    AlternatingMap.bilinMap_apply]

/-! The explicit components of `volumeFormRaise a b u`: up to sign, the `μ`-th component is the
`3 × 3` minor of the component matrix of `(u, a, b)` with row `μ` deleted. -/

/-- The time component of `volumeFormRaise a b u`: the minor with the time row deleted. -/
theorem volumeFormRaise_apply_inl (a b u : Vector 3) :
    volumeFormRaise a b u (Sum.inl 0) =
      u (Sum.inr 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        + u (Sum.inr 2) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0)) := by
  simp [volumeFormRaise_apply, volumeForm_eq_sum_timeComponent_mul_det, Matrix.det_fin_three,
    basis_apply]
  ring

/-- The first spatial component of `volumeFormRaise a b u`: the minor with row `1` deleted. -/
theorem volumeFormRaise_apply_inr_zero (a b u : Vector 3) :
    volumeFormRaise a b u (Sum.inr 0) =
      u (Sum.inl 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0)) := by
  simp [volumeFormRaise_apply, volumeForm_eq_sum_timeComponent_mul_det, Matrix.det_fin_three,
    basis_apply]
  ring

/-- The second spatial component of `volumeFormRaise a b u`: minus the minor with row `2` deleted.
-/
theorem volumeFormRaise_apply_inr_one (a b u : Vector 3) :
    volumeFormRaise a b u (Sum.inr 1) =
      -(u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0))) := by
  simp [volumeFormRaise_apply, volumeForm_eq_sum_timeComponent_mul_det, Matrix.det_fin_three,
    basis_apply]
  ring

/-- The third spatial component of `volumeFormRaise a b u`: the minor with row `3` deleted. -/
theorem volumeFormRaise_apply_inr_two (a b u : Vector 3) :
    volumeFormRaise a b u (Sum.inr 2) =
      u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0))
        + u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0)) := by
  simp [volumeFormRaise_apply, volumeForm_eq_sum_timeComponent_mul_det, Matrix.det_fin_three,
    basis_apply]
  ring

/-- The square of `volumeFormRaise a b` for arbitrary `a`, `b`: the contraction of two Levi-Civita
tensors over one index, as a polynomial identity in Minkowski products. -/
theorem volumeFormRaise_volumeFormRaise (a b u : Vector 3) :
    volumeFormRaise a b (volumeFormRaise a b u) =
      (⟪a, a⟫ₘ * ⟪b, b⟫ₘ - ⟪a, b⟫ₘ ^ 2) • u - (⟪a, a⟫ₘ * ⟪b, u⟫ₘ) • b
        + ⟪a, b⟫ₘ • (⟪a, u⟫ₘ • b + ⟪b, u⟫ₘ • a) - (⟪b, b⟫ₘ * ⟪a, u⟫ₘ) • a := by
  funext μ
  rcases μ with i | j
  · fin_cases i
    simp [volumeFormRaise_apply_inl, volumeFormRaise_apply_inr_zero, volumeFormRaise_apply_inr_one,
      volumeFormRaise_apply_inr_two, minkowskiProduct_toCoord, Fin.sum_univ_three]
    ring
  · fin_cases j <;>
      simp [volumeFormRaise_apply_inl, volumeFormRaise_apply_inr_zero,
        volumeFormRaise_apply_inr_one, volumeFormRaise_apply_inr_two, minkowskiProduct_toCoord,
        Fin.sum_univ_three] <;>
      ring

end EpsilonEridani
