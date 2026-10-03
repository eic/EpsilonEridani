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
`v_T` orthogonal to both `n₊` and `n₋`. The map `v ↦ v_T` is the transverse projector
`g_T^{μν} = g^{μν} - n₊^μ n₋^ν - n₋^μ n₊^ν`.

This is the kinematic frame of transverse-momentum-dependent and higher-twist factorisation:
light-cone components of hadron and parton momenta, and transverse momenta `k_T`, are taken with
respect to a light-cone basis aligned with the collision axis. In Minkowski space of dimension
`d + 1` the transverse subspace has dimension `d - 1`, so two in four dimensions.

The material is stated for an arbitrary bilinear form over a commutative ring. The pairing is
required in both orders, so no symmetry of `B` is needed for the decomposition itself; the
splitting `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T` of the scalar product uses only reflexivity.

## Main definitions

* `EpsilonEridani.LightConeBasis B`: a light-cone basis `(n₊, n₋)` for `B`.
* `LightConeBasis.plus`, `LightConeBasis.minus`: the light-cone components `v⁺`, `v⁻`.
* `LightConeBasis.longitudinal`: the span of `n₊` and `n₋`.
* `LightConeBasis.transverse`: its orthogonal complement, the transverse subspace.
* `LightConeBasis.transverseProj`: the transverse projector `v ↦ v_T`.
* `LightConeBasis.minkowskiAxis i`: the standard basis `n± = (e₀ ± eᵢ)/√2` of Minkowski space.

## Main statements

* `LightConeBasis.isProj_transverseProj`: the transverse projector is a projection onto the
  transverse subspace; in particular it is idempotent (`isIdempotentElem_transverseProj`).
* `LightConeBasis.ker_transverseProj`: its kernel is the longitudinal subspace.
* `LightConeBasis.isCompl_longitudinal_transverse`: `V` is the direct sum of the longitudinal and
  transverse subspaces.
* `LightConeBasis.smul_add_smul_add_eq_iff`: uniqueness of the decomposition
  `v = v⁺ n₊ + v⁻ n₋ + v_T`.
* `LightConeBasis.apply_eq_plus_mul_minus_add`: `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T`.
* `LightConeBasis.finrank_transverse_add_two`: the transverse subspace has codimension two.
* `LightConeBasis.finrank_transverse_minkowskiAxis`: in `d + 1`-dimensional Minkowski space the
  transverse projector has rank `d - 1`.

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
  nPlus_nPlus : B nPlus nPlus = 0
  /-- `n₋` is light-like. -/
  nMinus_nMinus : B nMinus nMinus = 0
  /-- The normalisation `n₊ · n₋ = 1`. -/
  nPlus_nMinus : B nPlus nMinus = 1
  /-- The normalisation `n₋ · n₊ = 1`. -/
  nMinus_nPlus : B nMinus nPlus = 1

namespace LightConeBasis

attribute [simp] nPlus_nPlus nMinus_nMinus nPlus_nMinus nMinus_nPlus

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

/-- The transverse subspace, the orthogonal complement of `n₊` and `n₋`. -/
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

theorem transverseProj_mem_transverse (v : V) : L.transverseProj v ∈ L.transverse :=
  L.mem_transverse_iff.2 ⟨L.plus_transverseProj v, L.minus_transverseProj v⟩

theorem transverseProj_eq_self_iff {v : V} : L.transverseProj v = v ↔ v ∈ L.transverse := by
  refine ⟨fun h => h ▸ L.transverseProj_mem_transverse v, fun h => ?_⟩
  obtain ⟨hp, hm⟩ := L.mem_transverse_iff.1 h
  simp [transverseProj_apply, hp, hm]

/-- The transverse projector is a projection onto the transverse subspace. -/
theorem isProj_transverseProj : LinearMap.IsProj L.transverse L.transverseProj :=
  ⟨L.transverseProj_mem_transverse, fun _ => L.transverseProj_eq_self_iff.2⟩

/-- The transverse projector is idempotent. -/
theorem isIdempotentElem_transverseProj : IsIdempotentElem L.transverseProj :=
  L.isProj_transverseProj.isIdempotentElem

@[simp]
theorem transverseProj_transverseProj (v : V) :
    L.transverseProj (L.transverseProj v) = L.transverseProj v :=
  L.transverseProj_eq_self_iff.2 (L.transverseProj_mem_transverse v)

theorem range_transverseProj : LinearMap.range L.transverseProj = L.transverse :=
  L.isProj_transverseProj.range

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
    simp [L.transverseProj_eq_self_iff.2 hw]
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

theorem apply_transverseProj_nPlus (v : V) : B (L.transverseProj v) L.nPlus = 0 :=
  hB _ _ (L.minus_transverseProj v)

theorem apply_transverseProj_nMinus (v : V) : B (L.transverseProj v) L.nMinus = 0 :=
  hB _ _ (L.plus_transverseProj v)

/-- The scalar product in light-cone components, `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T`. -/
theorem apply_eq_plus_mul_minus_add (u v : V) :
    B u v = L.plus u * L.minus v + L.minus u * L.plus v +
      B (L.transverseProj u) (L.transverseProj v) := by
  conv_lhs =>
    rw [← L.plus_smul_add_minus_smul_add_transverseProj u,
      ← L.plus_smul_add_minus_smul_add_transverseProj v]
  simp [L.apply_transverseProj_nPlus hB, L.apply_transverseProj_nMinus hB, ← plus_apply,
    ← minus_apply]

/-- The transverse projector is self-adjoint. -/
theorem isAdjointPair_transverseProj :
    B.IsAdjointPair B L.transverseProj L.transverseProj := by
  intro u v
  rw [L.apply_eq_plus_mul_minus_add hB, L.apply_eq_plus_mul_minus_add hB u]
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

/-- The standard light-cone basis `n± = (e₀ ± eᵢ)/√2` of `d + 1`-dimensional Minkowski space,
along the spatial axis `i`. -/
noncomputable def minkowskiAxis (i : Fin d) :
    LightConeBasis (minkowskiProduct (d := d)).toBilinForm where
  nPlus := (√2)⁻¹ • (basis (Sum.inl 0) + basis (Sum.inr i))
  nMinus := (√2)⁻¹ • (basis (Sum.inl 0) - basis (Sum.inr i))
  nPlus_nPlus := by simp [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
  nMinus_nMinus := by simp [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
  nPlus_nMinus := by
    simp [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    field_simp
    norm_num
  nMinus_nPlus := by
    simp [minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
    field_simp
    norm_num

theorem minkowskiAxis_nPlus (i : Fin d) :
    (minkowskiAxis i).nPlus = (√2)⁻¹ • (basis (Sum.inl 0) + basis (Sum.inr i)) :=
  (rfl)

theorem minkowskiAxis_nMinus (i : Fin d) :
    (minkowskiAxis i).nMinus = (√2)⁻¹ • (basis (Sum.inl 0) - basis (Sum.inr i)) :=
  (rfl)

/-- The plus component in the standard basis, `v⁺ = (v⁰ + vⁱ)/√2`. -/
theorem minkowskiAxis_plus (i : Fin d) (v : Vector d) :
    (minkowskiAxis i).plus v = (v (Sum.inl 0) + v (Sum.inr i)) / √2 := by
  simp [plus_apply, minkowskiAxis_nMinus, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
  ring

/-- The minus component in the standard basis, `v⁻ = (v⁰ - vⁱ)/√2`. -/
theorem minkowskiAxis_minus (i : Fin d) (v : Vector d) :
    (minkowskiAxis i).minus v = (v (Sum.inl 0) - v (Sum.inr i)) / √2 := by
  simp [minus_apply, minkowskiAxis_nPlus, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]
  ring

/-- In `d + 1`-dimensional Minkowski space the transverse subspace, the range of the transverse
projector, has dimension `d - 1`; in four dimensions it is two-dimensional. -/
theorem finrank_transverse_minkowskiAxis (i : Fin d) :
    finrank ℝ (minkowskiAxis i).transverse = d - 1 := by
  have h := (minkowskiAxis i).finrank_transverse_add_two
  rw [finrank_eq_card_basis basis, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h
  omega

end Minkowski

end LightConeBasis

end EpsilonEridani
