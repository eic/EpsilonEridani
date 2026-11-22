/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection

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
respect to a light-cone basis aligned with the collision axis. The standard light-cone basis of
Minkowski space, `n± = (e₀ ± eᵢ)/√2`, is constructed in `EpsilonEridani.Relativity.LightConeBasis`.

The material is stated for an arbitrary bilinear form over a commutative ring. The pairing is
required in both orders, so no symmetry of `B` is needed for the decomposition itself; the
splitting `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T` of the scalar product uses only reflexivity.
The transverse subspace is Mathlib's `LinearMap.BilinForm.orthogonal`, which puts the basis
vectors in the left argument: `v` is transverse iff `B n₊ v = B n₋ v = 0`. The other order
`B v n₊ = B v n₋ = 0` characterises it only when `B` is reflexive
(`LightConeBasis.mem_transverse_iff_bilinForm_right_eq_zero`).

## Main definitions

* `LinearMap.BilinForm.LightConeBasis B`: a light-cone basis `(n₊, n₋)` for `B`.
* `LightConeBasis.plus`, `LightConeBasis.minus`: the light-cone components `v⁺`, `v⁻`.
* `LightConeBasis.longitudinal`: the span of `n₊` and `n₋`.
* `LightConeBasis.transverse`: the transverse subspace `{v | n₊ · v = n₋ · v = 0}`, the
  (right) orthogonal complement of the longitudinal subspace.
* `LightConeBasis.transverseProj`: the transverse projector `v ↦ v_T`.

## Main statements

* `LightConeBasis.isProj_transverseProj`: the transverse projector is a projection onto the
  transverse subspace.
* `LightConeBasis.transverseProj_transverseProj_eq`: the transverse projector is idempotent.
* `LightConeBasis.ker_transverseProj_eq_longitudinal`: its kernel is the longitudinal subspace.
* `LightConeBasis.isCompl_longitudinal_transverse`: `V` is the direct sum of the longitudinal and
  transverse subspaces.
* `LightConeBasis.smul_add_smul_add_eq_iff`: uniqueness of the decomposition
  `v = v⁺ n₊ + v⁻ n₋ + v_T`.
* `LightConeBasis.bilinForm_eq_plus_mul_minus_add`: `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T`.
* `LightConeBasis.isSelfAdjoint_transverseProj`: for a reflexive form the transverse projector is
  self-adjoint.
* `LightConeBasis.finrank_transverse_add_two_eq`: the transverse subspace has codimension two.

## References

* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011).
* P. J. Mulders and R. D. Tangerman, *The complete tree-level result up to order 1/Q for
  polarized deep-inelastic leptoproduction*, Nucl. Phys. B461 (1996) 197.
-/

public section

namespace LinearMap.BilinForm

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
theorem plus_nPlus_eq_one : L.plus L.nPlus = 1 := by
  simp [plus_apply]

@[simp]
theorem plus_nMinus_eq_zero : L.plus L.nMinus = 0 := by
  simp [plus_apply]

@[simp]
theorem minus_nPlus_eq_zero : L.minus L.nPlus = 0 := by
  simp [minus_apply]

@[simp]
theorem minus_nMinus_eq_one : L.minus L.nMinus = 1 := by
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

/-- A vector is transverse iff both of its light-cone components vanish. -/
@[simp]
theorem mem_transverse_iff {v : V} : v ∈ L.transverse ↔ L.plus v = 0 ∧ L.minus v = 0 := by
  rw [transverse_def, longitudinal_def]
  exact Submodule.mem_orthogonalBilin_span.trans (by simp [plus_apply, minus_apply, and_comm])

/-! ### The transverse projector -/

/-- The transverse projector `v ↦ v_T = v - v⁺ n₊ - v⁻ n₋`. -/
def transverseProj : V →ₗ[R] V :=
  LinearMap.id - L.plus.smulRight L.nPlus - L.minus.smulRight L.nMinus

theorem transverseProj_apply (v : V) :
    L.transverseProj v = v - L.plus v • L.nPlus - L.minus v • L.nMinus :=
  (rfl)

/-- Every vector is the sum of its light-cone and transverse parts,
`v = v⁺ n₊ + v⁻ n₋ + v_T`. -/
theorem plus_smul_add_minus_smul_add_transverseProj_eq (v : V) :
    L.plus v • L.nPlus + L.minus v • L.nMinus + L.transverseProj v = v := by
  rw [transverseProj_apply]
  abel

@[simp]
theorem plus_transverseProj_eq_zero (v : V) : L.plus (L.transverseProj v) = 0 := by
  simp [transverseProj_apply]

@[simp]
theorem minus_transverseProj_eq_zero (v : V) : L.minus (L.transverseProj v) = 0 := by
  simp [transverseProj_apply]

/-- The transverse projector is a projection onto the transverse subspace. -/
theorem isProj_transverseProj : LinearMap.IsProj L.transverse L.transverseProj where
  map_mem v := L.mem_transverse_iff.2 ⟨L.plus_transverseProj_eq_zero v,
    L.minus_transverseProj_eq_zero v⟩
  map_id v h := by
    obtain ⟨hp, hm⟩ := L.mem_transverse_iff.1 h
    simp [transverseProj_apply, hp, hm]

/-- The transverse projector is idempotent. -/
@[simp]
theorem transverseProj_transverseProj_eq (v : V) :
    L.transverseProj (L.transverseProj v) = L.transverseProj v :=
  L.isProj_transverseProj.map_id _ (L.isProj_transverseProj.map_mem v)

@[simp]
theorem transverseProj_nPlus_eq_zero : L.transverseProj L.nPlus = 0 := by
  simp [transverseProj_apply]

@[simp]
theorem transverseProj_nMinus_eq_zero : L.transverseProj L.nMinus = 0 := by
  simp [transverseProj_apply]

/-- The kernel of the transverse projector is the longitudinal subspace. -/
@[simp]
theorem ker_transverseProj_eq_longitudinal : LinearMap.ker L.transverseProj = L.longitudinal := by
  ext v
  rw [LinearMap.mem_ker]
  rw [longitudinal_def, Submodule.mem_span_pair]
  refine ⟨fun h => ⟨L.plus v, L.minus v, ?_⟩, fun ⟨a, b, hv⟩ => ?_⟩
  · simpa [h] using L.plus_smul_add_minus_smul_add_transverseProj_eq v
  · subst hv
    simp

/-- A vector is longitudinal iff its transverse part vanishes. -/
@[simp]
theorem mem_longitudinal_iff {v : V} : v ∈ L.longitudinal ↔ L.transverseProj v = 0 := by
  rw [← ker_transverseProj_eq_longitudinal, LinearMap.mem_ker]

/-- `V` is the direct sum of the longitudinal and the transverse subspaces. -/
theorem isCompl_longitudinal_transverse : IsCompl L.longitudinal L.transverse := by
  simpa [ker_transverseProj_eq_longitudinal] using L.isProj_transverseProj.isCompl.symm

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
    exact L.plus_smul_add_minus_smul_add_transverseProj_eq v

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
theorem mem_transverse_iff_bilinForm_right_eq_zero {w : V} :
    w ∈ L.transverse ↔ B w L.nPlus = 0 ∧ B w L.nMinus = 0 := by
  rw [mem_transverse_iff, plus_apply, minus_apply]
  exact ⟨fun ⟨hp, hm⟩ => ⟨hB _ _ hm, hB _ _ hp⟩, fun ⟨hp, hm⟩ => ⟨hB _ _ hm, hB _ _ hp⟩⟩

/-- The scalar product in light-cone components, `u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T`. -/
theorem bilinForm_eq_plus_mul_minus_add (u v : V) :
    B u v = L.plus u * L.minus v + L.minus u * L.plus v +
      B (L.transverseProj u) (L.transverseProj v) := by
  conv_lhs =>
    rw [← L.plus_smul_add_minus_smul_add_transverseProj_eq u,
      ← L.plus_smul_add_minus_smul_add_transverseProj_eq v]
  simp [((L.mem_transverse_iff_bilinForm_right_eq_zero hB).1
      (L.isProj_transverseProj.map_mem _)).1,
    ((L.mem_transverse_iff_bilinForm_right_eq_zero hB).1
      (L.isProj_transverseProj.map_mem _)).2,
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
@[simp]
theorem finrank_longitudinal_eq_two : finrank K L.longitudinal = 2 := by
  rw [longitudinal_def]
  have h := finrank_span_eq_card L.linearIndependent
  rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at h

/-- The transverse subspace has codimension two. -/
theorem finrank_transverse_add_two_eq [FiniteDimensional K V] :
    finrank K L.transverse + 2 = finrank K V := by
  rw [← L.finrank_longitudinal_eq_two, add_comm]
  exact Submodule.finrank_add_eq_of_isCompl L.isCompl_longitudinal_transverse

end Field

end LightConeBasis

end LinearMap.BilinForm
