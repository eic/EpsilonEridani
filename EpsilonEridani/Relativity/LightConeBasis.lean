/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm

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

The transverse antisymmetric tensor `ε_T^{μν} = ε^{μνρσ} n_{+ρ} n_{-σ}` of a light-cone basis of
four-dimensional Minkowski space, built from the volume form
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.VolumeForm`, has components
`(ε_T u)^μ = η^{μμ} ε(u, e_μ, n₊, n₋)` (`transverseEpsLin_volumeForm_apply`) and squares to minus
the transverse projector, `ε_T^{μν} ε_{Tν}{}^{ρ} = -g_T^{μρ}`
(`transverseEpsLin_volumeForm_comp_self`): it is a rotation by a right angle of the transverse
plane. For an alternating four-form with another normalisation `c = ε(e₀, e₁, e₂, e₃)` the square
is `-c²` times the projector (`transverseEpsLin_comp_self`), so the identity is insensitive to the
sign convention chosen for the Levi-Civita tensor. This is the tensor in which the T-odd
structures of transverse-momentum-dependent distributions are written.

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
* `LightConeBasis.transverseEpsLin_volumeForm_apply`: the components
  `(ε_T u)^μ = η^{μμ} ε(u, e_μ, n₊, n₋)` of the raised transverse antisymmetric tensor.
* `LightConeBasis.transverseEpsLin_volumeForm_comp_self`: the transverse antisymmetric tensor
  squares to minus the transverse projector.
* `LightConeBasis.transverseEpsLin_comp_self`: the same for an alternating four-form of any
  normalisation.

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

/-! ### The transverse antisymmetric tensor -/

section TransverseEps

open EpsilonEridani (nondegenerate_toBilinForm_minkowskiProduct)

/-- The vector `μ ↦ η^{μμ} ε(u, e_μ, a, b)`, the contraction `ε_ν{}^μ{}_{ρσ} u^ν a^ρ b^σ` of the
volume form with `u`, `a` and `b`; for a light-cone basis `(a, b) = (n₊, n₋)` this is the raised
transverse antisymmetric tensor applied to `u`. -/
private noncomputable def epsRaise (a b u : Vector 3) : Vector 3 :=
  fun μ => minkowskiMatrix μ μ * volumeForm ![u, basis μ, a, b]

/- The components of `epsRaise a b u`: up to the sign `η^{μμ} (-1)^{μ+1}`, the `μ`-th component is
the `3 × 3` minor of the component matrix of `(u, a, b)` with row `μ` deleted. -/
private theorem epsRaise_apply_inl (a b u : Vector 3) :
    epsRaise a b u (Sum.inl 0) =
      -(u (Sum.inr 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        + u (Sum.inr 2) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0))) := by
  simp [epsRaise, volumeForm_eq_det_fin_three, Matrix.det_fin_three, basis_apply]
  ring

private theorem epsRaise_apply_inr_zero (a b u : Vector 3) :
    epsRaise a b u (Sum.inr 0) =
      -(u (Sum.inl 0) * (a (Sum.inr 1) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 1))
        - u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0))) := by
  simp [epsRaise, volumeForm_eq_det_fin_three, Matrix.det_fin_three, basis_apply]
  ring

private theorem epsRaise_apply_inr_one (a b u : Vector 3) :
    epsRaise a b u (Sum.inr 1) =
      u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 2) - a (Sum.inr 2) * b (Sum.inl 0))
        + u (Sum.inr 2) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0)) := by
  simp [epsRaise, volumeForm_eq_det_fin_three, Matrix.det_fin_three, basis_apply]
  ring

private theorem epsRaise_apply_inr_two (a b u : Vector 3) :
    epsRaise a b u (Sum.inr 2) =
      -(u (Sum.inl 0) * (a (Sum.inr 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inr 0))
        - u (Sum.inr 0) * (a (Sum.inl 0) * b (Sum.inr 1) - a (Sum.inr 1) * b (Sum.inl 0))
        + u (Sum.inr 1) * (a (Sum.inl 0) * b (Sum.inr 0) - a (Sum.inr 0) * b (Sum.inl 0))) := by
  simp [epsRaise, volumeForm_eq_det_fin_three, Matrix.det_fin_three, basis_apply]
  ring

/-- The square of `epsRaise a b` for arbitrary `a`, `b`: the polynomial identity, coming from the
contraction of two Levi-Civita tensors over one index, behind the square of the transverse
antisymmetric tensor. -/
private theorem epsRaise_epsRaise (a b u : Vector 3) :
    epsRaise a b (epsRaise a b u) =
      (⟪a, a⟫ₘ * ⟪b, b⟫ₘ - ⟪a, b⟫ₘ ^ 2) • u - (⟪a, a⟫ₘ * ⟪b, u⟫ₘ) • b
        + ⟪a, b⟫ₘ • (⟪a, u⟫ₘ • b + ⟪b, u⟫ₘ • a) - (⟪b, b⟫ₘ * ⟪a, u⟫ₘ) • a := by
  funext μ
  rcases μ with i | j
  · fin_cases i
    simp [epsRaise_apply_inl, epsRaise_apply_inr_zero, epsRaise_apply_inr_one,
      epsRaise_apply_inr_two, minkowskiProduct_toCoord, Fin.sum_univ_three]
    ring
  · fin_cases j <;>
      simp [epsRaise_apply_inl, epsRaise_apply_inr_zero, epsRaise_apply_inr_one,
        epsRaise_apply_inr_two, minkowskiProduct_toCoord, Fin.sum_univ_three] <;>
      ring

variable (L : LightConeBasis (minkowskiProduct (d := 3)).toBilinForm)

/-- The raised transverse antisymmetric tensor of Minkowski space in components:
`(E u)^μ = η^{μμ} ε(u, e_μ, n₊, n₋)`. -/
theorem transverseEpsLin_volumeForm_apply (u : Vector 3) (μ : Fin 1 ⊕ Fin 3) :
    L.transverseEpsLin volumeForm nondegenerate_toBilinForm_minkowskiProduct u μ =
      minkowskiMatrix μ μ * volumeForm ![u, basis μ, L.nPlus, L.nMinus] := by
  have h := L.bilinForm_transverseEpsLin_apply volumeForm nondegenerate_toBilinForm_minkowskiProduct
    u (basis μ)
  rw [transverseEps_apply, ContinuousLinearMap.toBilinForm_apply, minkowskiProduct_basis_right] at h
  rw [← h, ← _root_.mul_assoc, minkowskiMatrix.η_apply_mul_η_apply_diag, one_mul]

private theorem transverseEpsLin_volumeForm_eq_epsRaise (u : Vector 3) :
    L.transverseEpsLin volumeForm nondegenerate_toBilinForm_minkowskiProduct u =
      epsRaise L.nPlus L.nMinus u :=
  funext (L.transverseEpsLin_volumeForm_apply u)

/-- The transverse antisymmetric tensor of Minkowski space squares to minus the transverse
projector, `ε_T^{μν} ε_{Tν}{}^{ρ} = -g_T^{μρ}`. -/
@[simp]
theorem transverseEpsLin_volumeForm_transverseEpsLin_volumeForm (u : Vector 3) :
    L.transverseEpsLin volumeForm nondegenerate_toBilinForm_minkowskiProduct
      (L.transverseEpsLin volumeForm nondegenerate_toBilinForm_minkowskiProduct u) =
      -L.transverseProj u := by
  have hpp : ⟪L.nPlus, L.nPlus⟫ₘ = 0 := L.nPlus_nPlus_eq_zero
  have hmm : ⟪L.nMinus, L.nMinus⟫ₘ = 0 := L.nMinus_nMinus_eq_zero
  have hpm : ⟪L.nPlus, L.nMinus⟫ₘ = 1 := L.nPlus_nMinus_eq_one
  simp only [transverseEpsLin_volumeForm_eq_epsRaise, epsRaise_epsRaise, hpp, hmm, hpm,
    transverseProj_apply, plus_apply, minus_apply, ContinuousLinearMap.toBilinForm_apply]
  module

theorem transverseEpsLin_volumeForm_comp_self :
    L.transverseEpsLin volumeForm nondegenerate_toBilinForm_minkowskiProduct ∘ₗ
      L.transverseEpsLin volumeForm nondegenerate_toBilinForm_minkowskiProduct =
      -L.transverseProj :=
  LinearMap.ext L.transverseEpsLin_volumeForm_transverseEpsLin_volumeForm

/-- For any alternating four-form `ε` on Minkowski space, with normalisation
`c = ε(e₀, e₁, e₂, e₃)`, the raised transverse antisymmetric tensor squares to `-c²` times the
transverse projector. In particular the square does not depend on the sign convention for `ε`. -/
theorem transverseEpsLin_transverseEpsLin (ε : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ) (u : Vector 3) :
    L.transverseEpsLin ε nondegenerate_toBilinForm_minkowskiProduct
      (L.transverseEpsLin ε nondegenerate_toBilinForm_minkowskiProduct u) =
      -(ε basisFin4 ^ 2) • L.transverseProj u := by
  set c := ε basisFin4 with hc
  have hε : ε = c • volumeForm := ε.eq_smul_volumeForm
  rw [hε]
  simp only [transverseEpsLin_smul, LinearMap.smul_apply, map_smul,
    transverseEpsLin_volumeForm_transverseEpsLin_volumeForm]
  module

theorem transverseEpsLin_comp_self (ε : Vector 3 [⋀^Fin 4]→ₗ[ℝ] ℝ) :
    L.transverseEpsLin ε nondegenerate_toBilinForm_minkowskiProduct ∘ₗ
      L.transverseEpsLin ε nondegenerate_toBilinForm_minkowskiProduct =
      -(ε basisFin4 ^ 2) • L.transverseProj :=
  LinearMap.ext (L.transverseEpsLin_transverseEpsLin ε)

end TransverseEps

end LightConeBasis

end Minkowski

end LinearMap.BilinForm
