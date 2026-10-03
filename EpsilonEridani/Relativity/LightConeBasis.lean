/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Light-cone bases and the transverse projector

A *light-cone basis* for a bilinear form `B` on a module `V` is a pair of vectors `n₊`, `n₋`
that are light-like (`n₊ · n₊ = n₋ · n₋ = 0`) and normalised by `n₊ · n₋ = n₋ · n₊ = 1`.
Relative to such a pair every vector has light-cone components

  `v⁺ = n₋ · v`,  `v⁻ = n₊ · v`,

and a transverse part `v_T = v - v⁺ n₊ - v⁻ n₋`, so that `v = v⁺ n₊ + v⁻ n₋ + v_T` with
`n₊ · v_T = n₋ · v_T = 0`. The map `v ↦ v_T` is the transverse projector
`g_T^{μν} = g^{μν} - n₊^μ n₋^ν - n₋^μ n₊^ν`.

This is the kinematic frame of transverse-momentum-dependent and higher-twist factorisation:
light-cone components of hadron and parton momenta, and transverse momenta `k_T`, are taken with
respect to a light-cone basis aligned with the collision axis. In Minkowski space of dimension
`d + 1` the transverse subspace has dimension `d - 1`, so two in four dimensions.

The material is stated for an arbitrary bilinear form over a commutative ring. The pairing is
required in both orders, so no symmetry of `B` is needed for the decomposition itself; the
splitting `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T` of the scalar product uses only reflexivity.
The transverse subspace is Mathlib's `LinearMap.BilinForm.orthogonal`, which puts the basis
vectors in the left argument: `v` is transverse iff `B n₊ v = B n₋ v = 0`. The other order
`B v n₊ = B v n₋ = 0` characterises it only when `B` is reflexive
(`LightConeBasis.mem_transverse_iff_bilinForm_eq_zero`).

## Main definitions

* `EpsilonEridani.LightConeBasis B`: a light-cone basis `(n₊, n₋)` for `B`.
* `LightConeBasis.plus`, `LightConeBasis.minus`: the light-cone components `v⁺`, `v⁻`.
* `LightConeBasis.longitudinal`: the span of `n₊` and `n₋`.
* `LightConeBasis.transverse`: the transverse subspace `{v | n₊ · v = n₋ · v = 0}`, the
  (right) orthogonal complement of the longitudinal subspace.
* `LightConeBasis.transverseProj`: the transverse projector `v ↦ v_T`.
* `LightConeBasis.minkowskiAxis i`: the standard basis `n± = (e₀ ± eᵢ)/√2` of Minkowski space.

## Main statements

* `LightConeBasis.isProj_transverseProj`: the transverse projector is a projection onto the
  transverse subspace.
* `LightConeBasis.ker_transverseProj`: its kernel is the longitudinal subspace.
* `LightConeBasis.isCompl_longitudinal_transverse`: `V` is the direct sum of the longitudinal and
  transverse subspaces.
* `LightConeBasis.smul_add_smul_add_eq_iff`: uniqueness of the decomposition
  `v = v⁺ n₊ + v⁻ n₋ + v_T`.
* `LightConeBasis.bilinForm_eq_plus_mul_minus_add`: `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T`.
* `LightConeBasis.finrank_transverse_add_two`: the transverse subspace has codimension two.
* `LightConeBasis.finrank_transverse_minkowskiProduct_add_one`: in `d + 1`-dimensional
  Minkowski space the transverse projector of any light-cone basis has rank `d - 1`.
* `LightConeBasis.finrank_transverse_minkowskiProduct_eq_two`: in four-dimensional Minkowski space
  the transverse projector has rank two.

## References

* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011).
* P. J. Mulders and R. D. Tangerman, *The complete tree-level result up to order 1/Q for
  polarized deep-inelastic leptoproduction*, Nucl. Phys. B461 (1996) 197.
-/

public section

namespace EpsilonEridani

open LinearMap (BilinForm)
open Module

/-- A *light-cone basis* for a bilinear form `B`: two light-like vectors `n₊`, `n₋` with
`n₊ · n₋ = n₋ · n₊ = 1`. -/
@[ext]
structure LightConeBasis {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (B : BilinForm R V) where
  /-- The light-like vector `n₊`. -/
  nPlus : V
  /-- The light-like vector `n₋`. -/
  nMinus : V
  /-- `n₊` is light-like. -/
  nPlus_nPlus_eq_zero : B nPlus nPlus = 0
  /-- `n₋` is light-like. -/
  nMinus_nMinus_eq_zero : B nMinus nMinus = 0
  /-- The normalisation `n₊ · n₋ = 1`. -/
  nPlus_nMinus_eq_one : B nPlus nMinus = 1
  /-- The normalisation `n₋ · n₊ = 1`. -/
  nMinus_nPlus_eq_one : B nMinus nPlus = 1

namespace LightConeBasis

attribute [simp] nPlus_nPlus_eq_zero nMinus_nMinus_eq_zero nPlus_nMinus_eq_one nMinus_nPlus_eq_one

section CommRing

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V] {B : BilinForm R V}
  (L : LightConeBasis B)

/-! ### Light-cone components -/

/-- The plus component `v⁺ = n₋ · v`, the coefficient of `n₊` in `v`. -/
def plus : V →ₗ[R] R :=
  B L.nMinus

/-- The minus component `v⁻ = n₊ · v`, the coefficient of `n₋` in `v`. -/
def minus : V →ₗ[R] R :=
  B L.nPlus

theorem plus_apply (v : V) : L.plus v = B L.nMinus v :=
  (rfl)

theorem minus_apply (v : V) : L.minus v = B L.nPlus v :=
  (rfl)

@[simp]
theorem plus_nPlus : L.plus L.nPlus = 1 := by
  simp [plus_apply]

@[simp]
theorem plus_nMinus : L.plus L.nMinus = 0 := by
  simp [plus_apply]

@[simp]
theorem minus_nPlus : L.minus L.nPlus = 0 := by
  simp [minus_apply]

@[simp]
theorem minus_nMinus : L.minus L.nMinus = 1 := by
  simp [minus_apply]

/-! ### The longitudinal and transverse subspaces -/

/-- The longitudinal subspace, spanned by `n₊` and `n₋`. -/
def longitudinal : Submodule R V :=
  Submodule.span R {L.nPlus, L.nMinus}

/-- The transverse subspace `{v | n₊ · v = 0 ∧ n₋ · v = 0}`, the orthogonal complement
`B.orthogonal` of the longitudinal subspace (with `n₊`, `n₋` in the left argument of `B`). -/
def transverse : Submodule R V :=
  B.orthogonal L.longitudinal

theorem longitudinal_def : L.longitudinal = Submodule.span R {L.nPlus, L.nMinus} :=
  (rfl)

theorem transverse_def : L.transverse = B.orthogonal L.longitudinal :=
  (rfl)

theorem nPlus_mem_longitudinal : L.nPlus ∈ L.longitudinal :=
  Submodule.subset_span (by simp)

theorem nMinus_mem_longitudinal : L.nMinus ∈ L.longitudinal :=
  Submodule.subset_span (by simp)

theorem mem_longitudinal_iff {v : V} :
    v ∈ L.longitudinal ↔ ∃ a b : R, a • L.nPlus + b • L.nMinus = v :=
  Submodule.mem_span_pair

/-- A vector is transverse iff both of its light-cone components vanish. -/
@[simp]
theorem mem_transverse_iff {v : V} : v ∈ L.transverse ↔ L.plus v = 0 ∧ L.minus v = 0 := by
  refine ⟨fun h => ⟨h _ L.nMinus_mem_longitudinal, h _ L.nPlus_mem_longitudinal⟩, ?_⟩
  rintro ⟨hp, hm⟩ n hn
  obtain ⟨a, b, rfl⟩ := L.mem_longitudinal_iff.1 hn
  rw [plus_apply] at hp
  rw [minus_apply] at hm
  simp [hp, hm]

/-! ### The transverse projector -/

/-- The transverse projector `v ↦ v_T = v - v⁺ n₊ - v⁻ n₋`. -/
def transverseProj : V →ₗ[R] V :=
  LinearMap.id - L.plus.smulRight L.nPlus - L.minus.smulRight L.nMinus

theorem transverseProj_apply (v : V) :
    L.transverseProj v = v - L.plus v • L.nPlus - L.minus v • L.nMinus :=
  (rfl)

/-- Every vector is the sum of its light-cone and transverse parts,
`v = v⁺ n₊ + v⁻ n₋ + v_T`. -/
theorem plus_smul_add_minus_smul_add_transverseProj (v : V) :
    L.plus v • L.nPlus + L.minus v • L.nMinus + L.transverseProj v = v := by
  rw [transverseProj_apply]
  abel

@[simp]
theorem plus_transverseProj (v : V) : L.plus (L.transverseProj v) = 0 := by
  simp [transverseProj_apply]

@[simp]
theorem minus_transverseProj (v : V) : L.minus (L.transverseProj v) = 0 := by
  simp [transverseProj_apply]

/-- The transverse projector is a projection onto the transverse subspace. -/
theorem isProj_transverseProj : LinearMap.IsProj L.transverse L.transverseProj where
  map_mem v := L.mem_transverse_iff.2 ⟨L.plus_transverseProj v, L.minus_transverseProj v⟩
  map_id v h := by
    obtain ⟨hp, hm⟩ := L.mem_transverse_iff.1 h
    simp [transverseProj_apply, hp, hm]

@[simp]
theorem transverseProj_transverseProj (v : V) :
    L.transverseProj (L.transverseProj v) = L.transverseProj v :=
  L.isProj_transverseProj.map_id _ (L.isProj_transverseProj.map_mem v)

@[simp]
theorem transverseProj_nPlus : L.transverseProj L.nPlus = 0 := by
  simp [transverseProj_apply]

@[simp]
theorem transverseProj_nMinus : L.transverseProj L.nMinus = 0 := by
  simp [transverseProj_apply]

/-- The kernel of the transverse projector is the longitudinal subspace. -/
theorem ker_transverseProj : LinearMap.ker L.transverseProj = L.longitudinal := by
  ext v
  rw [LinearMap.mem_ker]
  refine ⟨fun h => L.mem_longitudinal_iff.2 ⟨L.plus v, L.minus v, ?_⟩, fun h => ?_⟩
  · simpa [h] using L.plus_smul_add_minus_smul_add_transverseProj v
  · obtain ⟨a, b, rfl⟩ := L.mem_longitudinal_iff.1 h
    simp

/-- `V` is the direct sum of the longitudinal and the transverse subspaces. -/
theorem isCompl_longitudinal_transverse : IsCompl L.longitudinal L.transverse := by
  simpa [ker_transverseProj] using L.isProj_transverseProj.isCompl.symm

/-- The decomposition `v = v⁺ n₊ + v⁻ n₋ + v_T` with `v_T` transverse is unique. -/
theorem smul_add_smul_add_eq_iff {a b : R} {w v : V} (hw : w ∈ L.transverse) :
    a • L.nPlus + b • L.nMinus + w = v ↔
      a = L.plus v ∧ b = L.minus v ∧ w = L.transverseProj v := by
  refine ⟨?_, ?_⟩
  · rintro rfl
    obtain ⟨hp, hm⟩ := L.mem_transverse_iff.1 hw
    refine ⟨by simp [hp], by simp [hm], ?_⟩
    simp [L.isProj_transverseProj.map_id w hw]
  · rintro ⟨rfl, rfl, rfl⟩
    exact L.plus_smul_add_minus_smul_add_transverseProj v

/-- `n₊` and `n₋` are linearly independent. -/
theorem linearIndependent : LinearIndependent R ![L.nPlus, L.nMinus] := by
  refine LinearIndependent.pair_iff.2 fun a b h => ⟨?_, ?_⟩
  · simpa using congrArg L.plus h
  · simpa using congrArg L.minus h

/-! ### The scalar product in light-cone components -/

section IsRefl

variable (hB : B.IsRefl)
include hB

/-- For a reflexive form, transversality can be tested with `n₊`, `n₋` in the right argument:
`w` is transverse iff `w · n₊ = w · n₋ = 0`. -/
theorem mem_transverse_iff_bilinForm_eq_zero {w : V} :
    w ∈ L.transverse ↔ B w L.nPlus = 0 ∧ B w L.nMinus = 0 := by
  rw [mem_transverse_iff, plus_apply, minus_apply]
  exact ⟨fun ⟨hp, hm⟩ => ⟨hB _ _ hm, hB _ _ hp⟩, fun ⟨hp, hm⟩ => ⟨hB _ _ hm, hB _ _ hp⟩⟩

/-- For a reflexive form, a transverse vector is orthogonal to `n₊` from the left,
`w · n₊ = 0`. -/
theorem bilinForm_nPlus_eq_zero_of_mem_transverse {w : V} (hw : w ∈ L.transverse) :
    B w L.nPlus = 0 :=
  ((L.mem_transverse_iff_bilinForm_eq_zero hB).1 hw).1

/-- For a reflexive form, a transverse vector is orthogonal to `n₋` from the left,
`w · n₋ = 0`. -/
theorem bilinForm_nMinus_eq_zero_of_mem_transverse {w : V} (hw : w ∈ L.transverse) :
    B w L.nMinus = 0 :=
  ((L.mem_transverse_iff_bilinForm_eq_zero hB).1 hw).2

/-- The scalar product in light-cone components, `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T`. -/
theorem bilinForm_eq_plus_mul_minus_add (u v : V) :
    B u v = L.plus u * L.minus v + L.minus u * L.plus v +
      B (L.transverseProj u) (L.transverseProj v) := by
  conv_lhs =>
    rw [← L.plus_smul_add_minus_smul_add_transverseProj u,
      ← L.plus_smul_add_minus_smul_add_transverseProj v]
  simp [L.bilinForm_nPlus_eq_zero_of_mem_transverse hB (L.isProj_transverseProj.map_mem _),
    L.bilinForm_nMinus_eq_zero_of_mem_transverse hB (L.isProj_transverseProj.map_mem _),
    ← plus_apply, ← minus_apply]

/-- The transverse projector is self-adjoint. -/
theorem isSelfAdjoint_transverseProj : B.IsSelfAdjoint L.transverseProj := by
  intro u v
  rw [L.bilinForm_eq_plus_mul_minus_add hB, L.bilinForm_eq_plus_mul_minus_add hB u]
  simp

end IsRefl

end CommRing

/-! ### Dimension of the transverse subspace -/

section Field

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {B : BilinForm K V}
  (L : LightConeBasis B)

/-- The longitudinal subspace is two-dimensional. -/
theorem finrank_longitudinal : finrank K L.longitudinal = 2 := by
  have h := finrank_span_eq_card L.linearIndependent
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at h

/-- The transverse subspace has codimension two. -/
theorem finrank_transverse_add_two [FiniteDimensional K V] :
    finrank K L.transverse + 2 = finrank K V := by
  rw [← L.finrank_longitudinal, add_comm]
  exact Submodule.finrank_add_eq_of_isCompl L.isCompl_longitudinal_transverse

end Field

/-! ### The standard light-cone basis of Minkowski space -/

section Minkowski

open Lorentz Vector

variable {d : ℕ}

/-- The vector `(e₀ + s eᵢ)/√2`; both standard light-cone vectors are of this form. -/
private noncomputable def axisVector (i : Fin d) (s : ℝ) : Vector d :=
  (√2)⁻¹ • (basis (Sum.inl 0) + s • basis (Sum.inr i))

private theorem minkowskiProduct_axisVector_left (i : Fin d) (s : ℝ) (v : Vector d) :
    ⟪axisVector i s, v⟫ₘ = (v (Sum.inl 0) - s * v (Sum.inr i)) / √2 := by
  simp only [axisVector, map_smul, map_add, add_apply,
    FunLike.coe_smul, Pi.smul_apply, minkowskiProduct_basis_left,
    minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i, smul_eq_mul]
  ring

private theorem minkowskiProduct_axisVector (i : Fin d) (s t : ℝ) :
    ⟪axisVector i s, axisVector i t⟫ₘ = (1 - s * t) / 2 := by
  rw [minkowskiProduct_axisVector_left]
  simp only [axisVector, apply_smul, apply_add, basis_apply, reduceIte, reduceCtorEq,
    MulZeroClass.mul_zero, _root_.add_zero, mul_one, _root_.zero_add]
  calc _ = (1 - s * t) / (√2 * √2) := by field_simp
    _ = _ := by rw [Real.mul_self_sqrt zero_le_two]

/-- The standard light-cone basis `n± = (e₀ ± eᵢ)/√2` of `d + 1`-dimensional Minkowski space,
along the spatial axis `i`. -/
noncomputable def minkowskiAxis (i : Fin d) :
    LightConeBasis (minkowskiProduct (d := d)).toBilinForm where
  nPlus := axisVector i 1
  nMinus := axisVector i (-1)
  nPlus_nPlus_eq_zero := by
    rw [ContinuousLinearMap.toBilinForm_apply, minkowskiProduct_axisVector]
    norm_num
  nMinus_nMinus_eq_zero := by
    rw [ContinuousLinearMap.toBilinForm_apply, minkowskiProduct_axisVector]
    norm_num
  nPlus_nMinus_eq_one := by
    rw [ContinuousLinearMap.toBilinForm_apply, minkowskiProduct_axisVector]
    norm_num
  nMinus_nPlus_eq_one := by
    rw [ContinuousLinearMap.toBilinForm_apply, minkowskiProduct_axisVector]
    norm_num

@[simp]
theorem minkowskiAxis_nPlus (i : Fin d) :
    (minkowskiAxis i).nPlus = (√2)⁻¹ • (basis (Sum.inl 0) + basis (Sum.inr i)) := by
  change axisVector i 1 = _
  rw [axisVector, one_smul]

@[simp]
theorem minkowskiAxis_nMinus (i : Fin d) :
    (minkowskiAxis i).nMinus = (√2)⁻¹ • (basis (Sum.inl 0) - basis (Sum.inr i)) := by
  change axisVector i (-1) = _
  rw [axisVector, neg_one_smul, _root_.sub_eq_add_neg]

/-- The plus component in the standard basis, `v⁺ = (v⁰ + vⁱ)/√2`. -/
@[simp]
theorem minkowskiAxis_plus (i : Fin d) (v : Vector d) :
    (minkowskiAxis i).plus v = (v (Sum.inl 0) + v (Sum.inr i)) / √2 := by
  rw [plus_apply, ContinuousLinearMap.toBilinForm_apply,
    show (minkowskiAxis i).nMinus = axisVector i (-1) from rfl,
    minkowskiProduct_axisVector_left, neg_one_mul, sub_neg_eq_add]

/-- The minus component in the standard basis, `v⁻ = (v⁰ - vⁱ)/√2`. -/
@[simp]
theorem minkowskiAxis_minus (i : Fin d) (v : Vector d) :
    (minkowskiAxis i).minus v = (v (Sum.inl 0) - v (Sum.inr i)) / √2 := by
  rw [minus_apply, ContinuousLinearMap.toBilinForm_apply,
    show (minkowskiAxis i).nPlus = axisVector i 1 from rfl,
    minkowskiProduct_axisVector_left, one_mul]

/-- A vector is transverse to the standard light-cone basis along axis `i` iff its time and
`i`-th spatial components vanish. -/
@[simp high]
theorem mem_transverse_minkowskiAxis_iff (i : Fin d) (v : Vector d) :
    v ∈ (minkowskiAxis i).transverse ↔ v (Sum.inl 0) = 0 ∧ v (Sum.inr i) = 0 := by
  have h : √2 ≠ 0 := by positivity
  rw [mem_transverse_iff, minkowskiAxis_plus, minkowskiAxis_minus, div_eq_zero_iff,
    div_eq_zero_iff, or_iff_left h, or_iff_left h]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by rw [h₁, h₂, _root_.add_zero], by rw [h₁, h₂, sub_zero]⟩

/-- For any light-cone basis of `d + 1`-dimensional Minkowski space the transverse subspace, the
range of the transverse projector (`L.isProj_transverseProj.range`), has dimension `d - 1`. -/
theorem finrank_transverse_minkowskiProduct_add_one
    (L : LightConeBasis (minkowskiProduct (d := d)).toBilinForm) :
    finrank ℝ L.transverse + 1 = d := by
  have h := L.finrank_transverse_add_two
  rw [finrank_eq_card_basis basis, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  omega

/-- In four-dimensional Minkowski space the transverse projector of any light-cone basis has
rank two. -/
theorem finrank_transverse_minkowskiProduct_eq_two
    (L : LightConeBasis (minkowskiProduct (d := 3)).toBilinForm) :
    finrank ℝ L.transverse = 2 := by
  have h := L.finrank_transverse_minkowskiProduct_add_one
  omega

end Minkowski

end LightConeBasis

end EpsilonEridani
