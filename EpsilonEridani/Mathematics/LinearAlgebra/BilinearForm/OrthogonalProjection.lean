/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck, Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.BasicExtensions
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# Orthogonal projections and reflections along a non-null vector

For a bilinear form `g` on a vector space `V` over a field `K` and a vector `u` with
`g u u ≠ 0`, this file defines

* the projection `LinearMap.BilinForm.orthogonalProjection g u : v ↦ v - (g v u / g u u) • u`
  along `K ∙ u` onto the vectors `v` with `g v u = 0`, and
* the reflection `LinearMap.BilinForm.reflection g u : v ↦ v - 2 (g u v / g u u) • u` in the
  `g`-orthogonal hyperplane of `u`,

both as `Module.preReflection u f` for the appropriate functional `f`, their pairings
reducing to the expansion `LinearMap.BilinForm.apply_sub_smul_sub_smul` of `g` on two vectors
shifted along `u`. The two-vector analogue of the projection, along a light-cone pair,
is `LinearMap.BilinForm.LightConeBasis.transverseProj` in
`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`.

## Main statements

* `LinearMap.BilinForm.orthogonalProjection_apply_eq_zero`,
  `orthogonalProjection_orthogonalProjection`, `ker_orthogonalProjection`,
  `range_orthogonalProjection`, `isProj_orthogonalProjection`: for `g u u ≠ 0` the projection is
  an idempotent with kernel `K ∙ u` and range `g.flip.orthogonal (K ∙ u)`.
* `LinearMap.BilinForm.orthogonalProjection_pairing`:
  `g (P v) (P w) = g v w - g v u * g u w / g u u`.
* `LinearMap.BilinForm.reflection_reflection`, `isOrthogonal_reflection`, `det_reflection`: for
  `g u u ≠ 0` the reflection is an involution and, for symmetric `g`, a `g`-isometry
  (`LinearMap.IsOrthogonal`), of determinant `-1` in finite dimension.
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
noncomputable def orthogonalProjection (g : BilinForm K V) (u : V) : V →ₗ[K] V :=
  Module.preReflection u ((g u u)⁻¹ • g.flip u)

lemma orthogonalProjection_apply (g : BilinForm K V) (u v : V) :
    g.orthogonalProjection u v = v - (g v u / g u u) • u := by
  simp [orthogonalProjection, Module.preReflection_apply, div_eq_inv_mul]

/-- The projection of any vector is `g`-orthogonal to `u`. -/
@[simp]
lemma orthogonalProjection_apply_eq_zero (g : BilinForm K V) {u : V} (hu : g u u ≠ 0)
    (v : V) :
    g (g.orthogonalProjection u v) u = 0 := by
  simp [orthogonalProjection_apply, hu]

/-- The projection annihilates `u`. -/
@[simp]
lemma orthogonalProjection_apply_self (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    g.orthogonalProjection u u = 0 := by
  rw [orthogonalProjection_apply, div_self hu, one_smul, sub_self]

/-- The projection fixes exactly the vectors `v` with `g v u = 0`. -/
lemma orthogonalProjection_eq_self_iff (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) {v : V} :
    g.orthogonalProjection u v = v ↔ g v u = 0 := by
  rw [orthogonalProjection_apply, sub_eq_self, smul_eq_zero, div_eq_zero_iff]
  simp [hu, LinearMap.BilinForm.ne_zero_of_not_isOrtho_self u hu]

/-- The projection is idempotent. -/
@[simp]
lemma orthogonalProjection_orthogonalProjection (g : BilinForm K V) {u : V} (hu : g u u ≠ 0)
    (v : V) :
    g.orthogonalProjection u (g.orthogonalProjection u v) = g.orthogonalProjection u v :=
  (g.orthogonalProjection_eq_self_iff hu).mpr (g.orthogonalProjection_apply_eq_zero hu v)

/-- The kernel of the projection is the line `K ∙ u`. -/
lemma ker_orthogonalProjection (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.ker (g.orthogonalProjection u) = K ∙ u := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    rw [orthogonalProjection_apply, sub_eq_zero] at hv
    exact ⟨g v u / g u u, hv.symm⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, g.orthogonalProjection_apply_self hu, smul_zero]

/-- The range of the projection is the set of vectors `v` with `g v u = 0`, that is, the
orthogonal complement of `K ∙ u` for `g.flip` in the sense of `LinearMap.BilinForm.orthogonal`.
For a symmetric form this is `g.orthogonal (K ∙ u)`. -/
lemma range_orthogonalProjection (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.range (g.orthogonalProjection u) = g.flip.orthogonal (K ∙ u) := by
  rw [LinearMap.BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton]
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply]
  exact ⟨by rintro ⟨w, rfl⟩; exact g.orthogonalProjection_apply_eq_zero hu w,
    fun hv ↦ ⟨v, (g.orthogonalProjection_eq_self_iff hu).mpr hv⟩⟩

/-- The projection is a projection onto `g.flip.orthogonal (K ∙ u)` in the sense of
`LinearMap.IsProj`, giving access to Mathlib's projection API (`LinearMap.IsProj.isCompl`, …). -/
lemma isProj_orthogonalProjection (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.IsProj (g.flip.orthogonal (K ∙ u)) (g.orthogonalProjection u) where
  map_mem v := g.range_orthogonalProjection hu ▸ LinearMap.mem_range_self _ v
  map_id v hv := by
    rw [← g.range_orthogonalProjection hu] at hv
    obtain ⟨w, rfl⟩ := hv
    exact g.orthogonalProjection_orthogonalProjection hu w

/-- The pairing of two projected vectors: `g (orthogonalProjection u v) (orthogonalProjection u w)
= g v w - g v u * g u w / g u u`. No symmetry of `g` is needed, and when `g u u = 0` both sides
are `g v w`. -/
lemma orthogonalProjection_pairing (g : BilinForm K V) (u v w : V) :
    g (g.orthogonalProjection u v) (g.orthogonalProjection u w) =
      g v w - g v u * g u w / g u u := by
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [orthogonalProjection_apply, hu]
  rw [orthogonalProjection_apply, orthogonalProjection_apply, apply_sub_smul_sub_smul]
  field_simp
  ring

/-- The projection depends on `u` only through the line `K ∙ u`. -/
lemma orthogonalProjection_smul (g : BilinForm K V) {c : K} (hc : c ≠ 0) (u : V) :
    g.orthogonalProjection (c • u) = g.orthogonalProjection u := by
  ext v
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [orthogonalProjection_apply, hu]
  simp only [orthogonalProjection_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 2
  field_simp

/-- Reflection of `V` in the `g`-orthogonal hyperplane to `u`, `v ↦ v - 2 (g u v / g u u) u`:
`Module.preReflection u f` for the functional `f = 2 g u · / g u u`, which satisfies `f u = 2`
when `g u u ≠ 0`. The definition is unconditional; it is a `g`-isometry
(`LinearMap.IsOrthogonal`) when `g` is symmetric and `g u u ≠ 0` (`isOrthogonal_reflection`), and
degenerates to the identity when `g u u = 0`, since `(0 : K)⁻¹ = 0`. -/
noncomputable def reflection (g : BilinForm K V) (u : V) : V →ₗ[K] V :=
  Module.preReflection u ((2 * (g u u)⁻¹) • g u)

lemma reflection_apply (g : BilinForm K V) (u v : V) :
    reflection g u v = v - (2 * (g u u)⁻¹ * g u v) • u := by
  simp only [reflection, Module.preReflection_apply, LinearMap.smul_apply, smul_eq_mul]

/-- The reflection in `u` reverses `u`. -/
@[simp]
lemma reflection_apply_self (g : BilinForm K V) (u : V) (hu : g u u ≠ 0) :
    reflection g u u = -u :=
  Module.preReflection_apply_self <| by
    rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]

/-- The reflection in `u` fixes every vector `g`-orthogonal to `u`. -/
@[simp]
lemma reflection_apply_of_orthogonal (g : BilinForm K V) (u v : V) (h : g u v = 0) :
    reflection g u v = v := by
  rw [reflection_apply, h, mul_zero, zero_smul, sub_zero]

/-- A reflection in a non-null direction is an involution. -/
@[simp]
lemma reflection_reflection (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) (v : V) :
    reflection g u (reflection g u v) = v :=
  Module.involutive_preReflection
    (by rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]) v

/-- A reflection in a non-null direction is a `g`-isometry when `g` is symmetric. -/
lemma isOrthogonal_reflection (g : BilinForm K V) (hSymm : g.IsSymm) (u : V) (hu : g u u ≠ 0) :
    g.IsOrthogonal (reflection g u) := by
  intro v w
  have hc : (g u u)⁻¹ * g u u = 1 := inv_mul_cancel₀ hu
  rw [reflection_apply, reflection_apply, apply_sub_smul_sub_smul, hSymm.eq v u]
  linear_combination (4 * (g u u)⁻¹ * g u v * g u w) * hc

/-- A reflection in a non-null direction of a finite-dimensional space has determinant `-1`. -/
@[simp]
lemma det_reflection [FiniteDimensional K V] (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.det (reflection g u) = -1 := by
  have h : reflection g u = LinearMap.transvection (-(2 * (g u u)⁻¹) • g u) u := by
    ext v
    rw [reflection_apply, LinearMap.transvection.apply, LinearMap.smul_apply, smul_eq_mul]
    module
  rw [h, LinearMap.transvection.det, LinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

end LinearMap.BilinForm
