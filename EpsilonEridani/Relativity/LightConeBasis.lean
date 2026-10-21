/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# The standard light-cone basis of Minkowski space

The light-cone basis `n± = (e₀ ± eᵢ)/√2` of `d + 1`-dimensional Minkowski space along a spatial
axis `i` is `LightConeBasis.minkowskiAxis i`, a light-cone basis in the sense of
`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`. Its light-cone components
are the combinations `v⁺ = (v⁰ + vⁱ)/√2` and `v⁻ = (v⁰ - vⁱ)/√2` of the time and `i`-th spatial
components of a vector (`minkowskiAxis_plus_apply`, `minkowskiAxis_minus_apply`), and a vector is
transverse exactly when those two components vanish (`mem_transverse_minkowskiAxis_iff`).

The Minkowski product is symmetric
(`EpsilonEridani.isSymm_toBilinForm_minkowskiProduct` in
`Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions`), so the reflexive-form results
of the general theory, in particular the splitting of the scalar product into light-cone
components and the self-adjointness of the transverse projector, apply to it.

For any light-cone basis of Minkowski space the transverse subspace, the range of the transverse
projector (`LightConeBasis.isProj_transverseProj.range`), has dimension `d - 1`
(`finrank_transverse_minkowskiProduct_add_one_eq`), so the transverse projector has rank two in
four dimensions (`finrank_transverse_minkowskiProduct_eq_two`). This is the kinematic frame of
transverse-momentum-dependent and higher-twist factorisation: transverse momenta `k_T` are the
transverse parts of momenta with respect to such a basis.

## Main definitions

* `LightConeBasis.minkowskiAxis i`: the standard light-cone basis `(n₊, n₋)`, `n± = (e₀ ± eᵢ)/√2`,
  of Minkowski space.

## Main statements

* `LightConeBasis.minkowskiAxis_plus_apply`, `LightConeBasis.minkowskiAxis_minus_apply`:
  the light-cone components `v± = (v⁰ ± vⁱ)/√2`.
* `LightConeBasis.mem_transverse_minkowskiAxis_iff`: a vector is transverse to the standard
  light-cone basis along axis `i` iff its time and `i`-th spatial components vanish.
* `LightConeBasis.finrank_transverse_minkowskiProduct_add_one_eq`: in `d + 1`-dimensional
  Minkowski space the transverse projector of any light-cone basis has rank `d - 1`.
* `LightConeBasis.finrank_transverse_minkowskiProduct_eq_two`: in four-dimensional Minkowski
  space the transverse projector has rank two.

## References

* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011).
* P. J. Mulders and R. D. Tangerman, *The complete tree-level result up to order 1/Q for
  polarized deep-inelastic leptoproduction*, Nucl. Phys. B461 (1996) 197.
-/

public section

namespace LinearMap.BilinForm

/-! ### The standard light-cone basis of Minkowski space -/

section Minkowski

open Lorentz Vector
open Module

variable {d : ℕ}

namespace LightConeBasis

/-- The vector `(e₀ + s eᵢ)/√2`; both standard light-cone vectors are of this form. -/
private noncomputable def axisVector (i : Fin d) (s : ℝ) : Vector d :=
  (√2)⁻¹ • (basis (Sum.inl 0) + s • basis (Sum.inr i))

private theorem minkowskiProduct_axisVector_left (i : Fin d) (s : ℝ) (v : Vector d) :
    ⟪axisVector i s, v⟫ₘ = (v.timeComponent - s * v.spatialPart i) / √2 := by
  simp only [axisVector, map_smul, map_add, _root_.add_apply,
    FunLike.coe_smul, Pi.smul_apply, minkowskiProduct_basis_left,
    minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i, smul_eq_mul]
  ring

private theorem axisVector_timeComponent (i : Fin d) (s : ℝ) :
    timeComponent (axisVector i s) = (√2)⁻¹ := by
  simp [axisVector, basis_apply]

private theorem axisVector_spatialPart (i : Fin d) (s : ℝ) :
    spatialPart (axisVector i s) i = (√2)⁻¹ * s := by
  simp [axisVector, basis_apply]

private theorem minkowskiProduct_axisVector (i : Fin d) (s t : ℝ) :
    ⟪axisVector i s, axisVector i t⟫ₘ = (1 - s * t) / 2 := by
  have h : (√2)⁻¹ * (√2)⁻¹ = 2⁻¹ := by rw [← mul_inv, Real.mul_self_sqrt zero_le_two]
  rw [minkowskiProduct_axisVector_left, axisVector_timeComponent, axisVector_spatialPart]
  -- The left-hand side is `(1 - s * t) * ((√2)⁻¹ * (√2)⁻¹)`.
  linear_combination (1 - s * t) * h

/-- The standard light-cone basis `n± = (e₀ ± eᵢ)/√2` of `d + 1`-dimensional Minkowski space,
along the spatial axis `i`. -/
noncomputable def minkowskiAxis (i : Fin d) :
    LightConeBasis (minkowskiProduct (d := d)).toBilinForm where
  nPlus := axisVector i 1
  nMinus := axisVector i (-1)
  nPlus_nPlus_eq_zero := by norm_num [minkowskiProduct_axisVector]
  nMinus_nMinus_eq_zero := by norm_num [minkowskiProduct_axisVector]
  nPlus_nMinus_eq_one := by norm_num [minkowskiProduct_axisVector]
  nMinus_nPlus_eq_one := by norm_num [minkowskiProduct_axisVector]

/- The structure projections of `minkowskiAxis i`, holding by unfolding the definition. -/
private theorem minkowskiAxis_nPlus_eq (i : Fin d) : (minkowskiAxis i).nPlus = axisVector i 1 :=
  rfl

private theorem minkowskiAxis_nMinus_eq (i : Fin d) :
    (minkowskiAxis i).nMinus = axisVector i (-1) :=
  rfl

theorem minkowskiAxis_nPlus_eq_smul_add (i : Fin d) :
    (minkowskiAxis i).nPlus = (√2)⁻¹ • (basis (Sum.inl 0) + basis (Sum.inr i)) := by
  rw [minkowskiAxis_nPlus_eq, axisVector, one_smul]

theorem minkowskiAxis_nMinus_eq_smul_sub (i : Fin d) :
    (minkowskiAxis i).nMinus = (√2)⁻¹ • (basis (Sum.inl 0) - basis (Sum.inr i)) := by
  rw [minkowskiAxis_nMinus_eq, axisVector, neg_one_smul, _root_.sub_eq_add_neg]

/-- The plus component in the standard basis, `v⁺ = (v⁰ + vⁱ)/√2`. -/
@[simp low]
theorem minkowskiAxis_plus_apply (i : Fin d) (v : Vector d) :
    (minkowskiAxis i).plus v = (v.timeComponent + v.spatialPart i) / √2 := by
  rw [plus_apply, ContinuousLinearMap.toBilinForm_apply, minkowskiAxis_nMinus_eq,
    minkowskiProduct_axisVector_left, neg_one_mul, sub_neg_eq_add]

/-- The minus component in the standard basis, `v⁻ = (v⁰ - vⁱ)/√2`. -/
@[simp low]
theorem minkowskiAxis_minus_apply (i : Fin d) (v : Vector d) :
    (minkowskiAxis i).minus v = (v.timeComponent - v.spatialPart i) / √2 := by
  rw [minus_apply, ContinuousLinearMap.toBilinForm_apply, minkowskiAxis_nPlus_eq,
    minkowskiProduct_axisVector_left, one_mul]

/-- A vector is transverse to the standard light-cone basis along axis `i` iff its time and
`i`-th spatial components vanish. -/
@[simp high]
theorem mem_transverse_minkowskiAxis_iff (i : Fin d) (v : Vector d) :
    v ∈ (minkowskiAxis i).transverse ↔ v.timeComponent = 0 ∧ v.spatialPart i = 0 := by
  have h : √2 ≠ 0 := by positivity
  rw [mem_transverse_iff, minkowskiAxis_plus_apply, minkowskiAxis_minus_apply, div_eq_zero_iff,
    div_eq_zero_iff, or_iff_left h, or_iff_left h]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> exact ⟨by linarith, by linarith⟩

/-- For any light-cone basis of `d + 1`-dimensional Minkowski space the transverse subspace, the
range of the transverse projector (`L.isProj_transverseProj.range`), has dimension `d - 1`. -/
theorem finrank_transverse_minkowskiProduct_add_one_eq
    (L : LightConeBasis (minkowskiProduct (d := d)).toBilinForm) :
    finrank ℝ L.transverse + 1 = d := by
  have h := L.finrank_transverse_add_two_eq
  rw [finrank_eq_card_basis basis, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  omega

/-- In four-dimensional Minkowski space the transverse projector of any light-cone basis has
rank two. -/
theorem finrank_transverse_minkowskiProduct_eq_two
    (L : LightConeBasis (minkowskiProduct (d := 3)).toBilinForm) :
    finrank ℝ L.transverse = 2 := by
  have h := L.finrank_transverse_minkowskiProduct_add_one_eq
  omega

end LightConeBasis

end Minkowski

end LinearMap.BilinForm
