/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck, Joseph Tooby-Smith
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.BasicExtensions
import Mathlib.LinearAlgebra.Reflection
import Mathlib.Tactic.FieldSimp

/-!
# Orthogonal projection along a non-null vector

For a bilinear form `g` on a vector space `V` over a field `K` and a vector `u` with
`g u u ≠ 0`, this file defines the projection
`LinearMap.BilinForm.orthogonalProjectionCompl g u : v ↦ v - (g v u / g u u) • u` along `K ∙ u`
onto the `g`-orthogonal complement of `u`, the vectors `v` with `g v u = 0`. It is
`Module.preReflection u f` for the functional `f = g · u / g u u`, and its pairing reduces to the
expansion `LinearMap.BilinForm.apply_sub_smul_sub_smul` of `g` on two vectors shifted along `u`.
For symmetric `g`, the reflection in the same hyperplane is `LinearMap.BilinForm.reflection` in
`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.Reflection`. The two-vector analogue of
the projection, along a light-cone pair, is `LinearMap.BilinForm.LightConeBasis.transverseProj` in
`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`.

## Main statements

* `LinearMap.BilinForm.apply_orthogonalProjectionCompl_eq_zero`,
  `orthogonalProjectionCompl_orthogonalProjectionCompl`, `ker_orthogonalProjectionCompl`,
  `range_orthogonalProjectionCompl`, `isProj_orthogonalProjectionCompl`: for `g u u ≠ 0` the
  projection is an idempotent with kernel `K ∙ u` and range `g.flip.orthogonal (K ∙ u)`.
* `LinearMap.BilinForm.orthogonalProjectionCompl_pairing`:
  `g (P v) (P w) = g v w - g v u * g u w / g u u`.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The projection along `K ∙ u` onto the `g`-orthogonal complement of `u`,
`v ↦ v - (g v u / g u u) • u`. It is `Module.preReflection u f` for the functional
`f = g · u / g u u`, which satisfies `f u = 1` when `g u u ≠ 0` (rather than the `f u = 2` of a
reflection). The definition is unconditional and degenerates to the identity when `g u u = 0`,
since `(0 : K)⁻¹ = 0`. -/
noncomputable def orthogonalProjectionCompl (g : BilinForm K V) (u : V) : V →ₗ[K] V :=
  Module.preReflection u ((g u u)⁻¹ • g.flip u)

lemma orthogonalProjectionCompl_apply (g : BilinForm K V) (u v : V) :
    g.orthogonalProjectionCompl u v = v - (g v u / g u u) • u := by
  simp [orthogonalProjectionCompl, Module.preReflection_apply, div_eq_inv_mul]

/-- The projection of any vector is `g`-orthogonal to `u`. -/
@[simp]
lemma apply_orthogonalProjectionCompl_eq_zero (g : BilinForm K V) {u : V} (hu : g u u ≠ 0)
    (v : V) :
    g (g.orthogonalProjectionCompl u v) u = 0 := by
  simp [orthogonalProjectionCompl_apply, hu]

/-- The projection annihilates `u`. -/
@[simp]
lemma orthogonalProjectionCompl_apply_self (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    g.orthogonalProjectionCompl u u = 0 := by
  rw [orthogonalProjectionCompl_apply, div_self hu, one_smul, sub_self]

/-- The projection fixes exactly the vectors `v` with `g v u = 0`. -/
lemma orthogonalProjectionCompl_eq_self_iff (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) {v : V} :
    g.orthogonalProjectionCompl u v = v ↔ g v u = 0 := by
  rw [orthogonalProjectionCompl_apply, sub_eq_self, smul_eq_zero, div_eq_zero_iff]
  simp [hu, LinearMap.BilinForm.ne_zero_of_not_isOrtho_self u hu]

/-- The projection is idempotent. For `g u u = 0` it is the identity. -/
@[simp]
lemma orthogonalProjectionCompl_orthogonalProjectionCompl (g : BilinForm K V) (u v : V) :
    g.orthogonalProjectionCompl u (g.orthogonalProjectionCompl u v) =
      g.orthogonalProjectionCompl u v := by
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [orthogonalProjectionCompl_apply, hu]
  exact (g.orthogonalProjectionCompl_eq_self_iff hu).mpr
    (g.apply_orthogonalProjectionCompl_eq_zero hu v)

/-- The kernel of the projection is the line `K ∙ u`. -/
lemma ker_orthogonalProjectionCompl (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.ker (g.orthogonalProjectionCompl u) = K ∙ u := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    rw [orthogonalProjectionCompl_apply, sub_eq_zero] at hv
    exact ⟨g v u / g u u, hv.symm⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, g.orthogonalProjectionCompl_apply_self hu, smul_zero]

/-- The range of the projection is the set of vectors `v` with `g v u = 0`, that is, the
orthogonal complement of `K ∙ u` for `g.flip` in the sense of `LinearMap.BilinForm.orthogonal`.
For a symmetric form this is `g.orthogonal (K ∙ u)`. -/
lemma range_orthogonalProjectionCompl (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.range (g.orthogonalProjectionCompl u) = g.flip.orthogonal (K ∙ u) := by
  rw [LinearMap.BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton]
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply]
  exact ⟨by rintro ⟨w, rfl⟩; exact g.apply_orthogonalProjectionCompl_eq_zero hu w,
    fun hv ↦ ⟨v, (g.orthogonalProjectionCompl_eq_self_iff hu).mpr hv⟩⟩

/-- The projection is a projection onto `g.flip.orthogonal (K ∙ u)` in the sense of
`LinearMap.IsProj`, giving access to Mathlib's projection API (`LinearMap.IsProj.isCompl`, …). -/
lemma isProj_orthogonalProjectionCompl (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.IsProj (g.flip.orthogonal (K ∙ u)) (g.orthogonalProjectionCompl u) where
  map_mem v := g.range_orthogonalProjectionCompl hu ▸ LinearMap.mem_range_self _ v
  map_id v hv := by
    rw [← g.range_orthogonalProjectionCompl hu] at hv
    obtain ⟨w, rfl⟩ := hv
    exact g.orthogonalProjectionCompl_orthogonalProjectionCompl u w

/-- The pairing of two projected vectors: `g (P v) (P w)
= g v w - g v u * g u w / g u u`. No symmetry of `g` is needed, and when `g u u = 0` both sides
are `g v w`. -/
lemma orthogonalProjectionCompl_pairing (g : BilinForm K V) (u v w : V) :
    g (g.orthogonalProjectionCompl u v) (g.orthogonalProjectionCompl u w) =
      g v w - g v u * g u w / g u u := by
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [orthogonalProjectionCompl_apply, hu]
  rw [orthogonalProjectionCompl_apply, orthogonalProjectionCompl_apply, apply_sub_smul_sub_smul]
  field_simp
  ring

/-- The projection depends on `u` only through the line `K ∙ u`. -/
lemma orthogonalProjectionCompl_smul_eq (g : BilinForm K V) {c : K} (hc : c ≠ 0) (u : V) :
    g.orthogonalProjectionCompl (c • u) = g.orthogonalProjectionCompl u := by
  ext v
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [orthogonalProjectionCompl_apply, hu]
  simp only [orthogonalProjectionCompl_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    smul_smul]
  congr 2
  field_simp

end LinearMap.BilinForm
