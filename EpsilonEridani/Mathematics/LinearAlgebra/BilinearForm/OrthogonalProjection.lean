/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck, Joseph Tooby-Smith
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module

/-!
# Orthogonal projections and reflections along a non-null vector

For a real bilinear form `g` on `V` and a vector `u` with `g u u ≠ 0`, this file defines

* the projection `LinearMap.BilinForm.projOrthogonal g u : v ↦ v - (g v u / g u u) • u` along
  `ℝ ∙ u` onto the vectors `v` with `g v u = 0`, and
* the reflection `LinearMap.BilinForm.reflect g u : v ↦ v - 2 (g u v / g u u) • u` in the
  `g`-orthogonal hyperplane of `u`,

both as `Module.preReflection u f` for the appropriate functional `f`, together with the
rank-one forms `LinearMap.BilinForm.rankOne g a b : (v, w) ↦ g a v * g b w` and the expansion
`LinearMap.BilinForm.apply_sub_smul_pair` of `g` on two vectors shifted along `u`. The two-vector
analogue of the projection, along a light-cone pair, is
`LinearMap.BilinForm.LightConeBasis.transverseProj` in
`EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis`.

## Main statements

* `LinearMap.BilinForm.projOrthogonal_orthogonal`, `projOrthogonal_projOrthogonal`,
  `ker_projOrthogonal`, `range_projOrthogonal`: for `g u u ≠ 0` the projection is an idempotent
  with kernel `ℝ ∙ u` and range `g.flip.orthogonal (ℝ ∙ u)`.
* `LinearMap.BilinForm.projOrthogonal_pairing`: `g (P v) (P w) = g v w - g v u * g u w / g u u`.
* `LinearMap.BilinForm.reflect_reflect`, `reflect_isometry`, `det_reflect`: for `g u u ≠ 0` the
  reflection is an involution and, for symmetric `g`, a `g`-isometry (`LinearMap.IsOrthogonal`),
  of determinant `-1` in finite dimension.
* `LinearMap.isOrthogonal_id`, `LinearMap.IsOrthogonal.comp`: the isometries of a bilinear form
  contain the identity and are closed under composition.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

section IsOrthogonal

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {B : BilinForm R M}

/-- The identity is an isometry of every bilinear form. -/
lemma _root_.LinearMap.isOrthogonal_id (B : BilinForm R M) :
    B.IsOrthogonal (LinearMap.id : M →ₗ[R] M) := fun x y ↦ by
  rw [LinearMap.id_apply, LinearMap.id_apply]

/-- A composite of isometries of `B` is an isometry of `B`. -/
lemma _root_.LinearMap.IsOrthogonal.comp {f f' : M →ₗ[R] M} (hf : B.IsOrthogonal f)
    (hf' : B.IsOrthogonal f') : B.IsOrthogonal (f ∘ₗ f') := fun x y ↦ by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hf, hf']

end IsOrthogonal

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Expansion of a bilinear form on a pair of vectors each shifted along `u`. -/
lemma apply_sub_smul_pair (g : BilinForm ℝ V) (u x y : V) (a b : ℝ) :
    g (x - a • u) (y - b • u)
      = g x y - b * g x u - a * g u y + a * b * g u u := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The projection along `ℝ ∙ u` onto the `g`-orthogonal complement of `u`,
`v ↦ v - (g v u / g u u) • u`. It is `Module.preReflection u f` for the functional
`f = g · u / g u u`, which satisfies `f u = 1` when `g u u ≠ 0` (rather than the `f u = 2` of a
reflection). The definition is unconditional and degenerates to the identity when `g u u = 0`,
since `(0 : ℝ)⁻¹ = 0`. -/
noncomputable def projOrthogonal (g : BilinForm ℝ V) (u : V) : V →ₗ[ℝ] V :=
  Module.preReflection u ((g u u)⁻¹ • g.flip u)

lemma projOrthogonal_apply (g : BilinForm ℝ V) (u v : V) :
    g.projOrthogonal u v = v - (g v u / g u u) • u := by
  simp [projOrthogonal, Module.preReflection_apply, div_eq_inv_mul]

/-- The projection of any vector is `g`-orthogonal to `u`. -/
@[simp]
lemma projOrthogonal_orthogonal (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) (v : V) :
    g (g.projOrthogonal u v) u = 0 := by
  simp [projOrthogonal_apply, hu]

/-- The projection annihilates `u`. -/
@[simp]
lemma projOrthogonal_apply_self (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) :
    g.projOrthogonal u u = 0 := by
  rw [projOrthogonal_apply, div_self hu, one_smul, sub_self]

/-- The projection fixes exactly the vectors `v` with `g v u = 0`. -/
lemma projOrthogonal_eq_self_iff (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) {v : V} :
    g.projOrthogonal u v = v ↔ g v u = 0 := by
  rw [projOrthogonal_apply, sub_eq_self, smul_eq_zero, div_eq_zero_iff]
  simp [hu, LinearMap.BilinForm.ne_zero_of_not_isOrtho_self u hu]

/-- The projection is idempotent. -/
@[simp]
lemma projOrthogonal_projOrthogonal (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) (v : V) :
    g.projOrthogonal u (g.projOrthogonal u v) = g.projOrthogonal u v :=
  (g.projOrthogonal_eq_self_iff hu).mpr (g.projOrthogonal_orthogonal hu v)

/-- The kernel of the projection is the line `ℝ ∙ u`. -/
lemma ker_projOrthogonal (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.ker (g.projOrthogonal u) = ℝ ∙ u := by
  ext v
  rw [LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · intro hv
    rw [projOrthogonal_apply, sub_eq_zero] at hv
    exact ⟨g v u / g u u, hv.symm⟩
  · rintro ⟨c, rfl⟩
    rw [map_smul, g.projOrthogonal_apply_self hu, smul_zero]

/-- The range of the projection is the set of vectors `v` with `g v u = 0`, that is, the
orthogonal complement of `ℝ ∙ u` for `g.flip` in the sense of `LinearMap.BilinForm.orthogonal`.
For a symmetric form this is `g.orthogonal (ℝ ∙ u)`. -/
lemma range_projOrthogonal (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.range (g.projOrthogonal u) = g.flip.orthogonal (ℝ ∙ u) := by
  rw [LinearMap.BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton]
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply]
  exact ⟨by rintro ⟨w, rfl⟩; exact g.projOrthogonal_orthogonal hu w,
    fun hv ↦ ⟨v, (g.projOrthogonal_eq_self_iff hu).mpr hv⟩⟩

/-- The pairing of two projected vectors: `g (projOrthogonal u v) (projOrthogonal u w)
= g v w - g v u * g u w / g u u`. No symmetry of `g` is needed, and when `g u u = 0` both sides
are `g v w`. -/
lemma projOrthogonal_pairing (g : BilinForm ℝ V) (u v w : V) :
    g (g.projOrthogonal u v) (g.projOrthogonal u w) = g v w - g v u * g u w / g u u := by
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [projOrthogonal_apply, hu]
  rw [projOrthogonal_apply, projOrthogonal_apply, apply_sub_smul_pair]
  field_simp
  ring

/-- The projection depends on `u` only through the line `ℝ ∙ u`. -/
lemma projOrthogonal_smul (g : BilinForm ℝ V) {c : ℝ} (hc : c ≠ 0) (u : V) :
    g.projOrthogonal (c • u) = g.projOrthogonal u := by
  ext v
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [projOrthogonal_apply, hu]
  simp only [projOrthogonal_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 2
  field_simp

/-- Rank-one bilinear form `(v,w) ↦ g(a,v) g(b,w)` derived from a background bilinear form
`g`, as the Mathlib combinator `LinearMap.smulRight (g a) (g b)`, the map
`v ↦ g a v • g b`. -/
def rankOne (g : BilinForm ℝ V) (a b : V) : BilinForm ℝ V :=
  (g a).smulRight (g b)

@[simp] lemma rankOne_apply (g : BilinForm ℝ V) (a b v w : V) :
    rankOne g a b v w = g a v * g b w := (rfl)

/-- A rank-one form built from a single vector is symmetric. -/
lemma rankOne_isSymm (g : BilinForm ℝ V) (a : V) : (rankOne g a a).IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp [rankOne_apply, mul_comm]

/-- Reflection of `V` in the `g`-orthogonal hyperplane to `u`, `v ↦ v - 2 (g u v / g u u) u`:
`Module.preReflection u f` for the functional `f = 2 g u · / g u u`, which satisfies `f u = 2`
when `g u u ≠ 0`. The definition is unconditional; it is a `g`-isometry
(`LinearMap.IsOrthogonal`) when `g` is symmetric and `g u u ≠ 0` (`reflect_isometry`), and
degenerates to the identity when `g u u = 0`, since `(0 : ℝ)⁻¹ = 0`. -/
noncomputable def reflect (g : BilinForm ℝ V) (u : V) : V →ₗ[ℝ] V :=
  Module.preReflection u ((2 * (g u u)⁻¹) • g u)

@[simp] lemma reflect_apply (g : BilinForm ℝ V) (u v : V) :
    reflect g u v = v - (2 * (g u u)⁻¹ * g u v) • u := by
  simp only [reflect, Module.preReflection_apply, LinearMap.smul_apply, smul_eq_mul]

/-- The reflection in `u` reverses `u`. -/
lemma reflect_apply_self (g : BilinForm ℝ V) (u : V) (hu : g u u ≠ 0) :
    reflect g u u = -u :=
  Module.preReflection_apply_self <| by
    rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]

/-- The reflection in `u` fixes every vector `g`-orthogonal to `u`. -/
lemma reflect_apply_of_orthogonal (g : BilinForm ℝ V) (u v : V) (h : g u v = 0) :
    reflect g u v = v := by
  rw [reflect_apply, h, mul_zero, zero_smul, sub_zero]

/-- A reflection in a non-null direction is an involution. Not `@[simp]`: `reflect_apply`
already rewrites its left-hand side. -/
lemma reflect_reflect (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) (v : V) :
    reflect g u (reflect g u v) = v := by
  have h : g u (reflect g u v) = -g u v := by
    simp only [reflect_apply, map_sub, map_smul, smul_eq_mul]
    field_simp
    ring
  rw [reflect_apply g u (reflect g u v), h, reflect_apply]
  module

/-- A reflection in a non-null direction is a `g`-isometry when `g` is symmetric. -/
lemma reflect_isometry (g : BilinForm ℝ V) (hSymm : g.IsSymm) (u : V) (hu : g u u ≠ 0) :
    g.IsOrthogonal (reflect g u) := by
  intro v w
  have hc : (g u u)⁻¹ * g u u = 1 := inv_mul_cancel₀ hu
  rw [reflect_apply, reflect_apply, apply_sub_smul_pair, hSymm.eq v u]
  linear_combination (4 * (g u u)⁻¹ * g u v * g u w) * hc

/-- A reflection in a non-null direction of a finite-dimensional space has determinant `-1`. -/
@[simp]
lemma det_reflect [FiniteDimensional ℝ V] (g : BilinForm ℝ V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.det (reflect g u) = -1 := by
  have h : reflect g u = LinearMap.transvection (-(2 * (g u u)⁻¹) • g u) u := by
    ext v
    rw [reflect_apply, LinearMap.transvection.apply, LinearMap.smul_apply, smul_eq_mul]
    module
  rw [h, LinearMap.transvection.det, LinearMap.smul_apply, smul_eq_mul]
  field_simp
  ring

end LinearMap.BilinForm
