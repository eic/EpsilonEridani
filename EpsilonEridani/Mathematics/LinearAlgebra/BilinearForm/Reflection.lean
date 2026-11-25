/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Reflection
public import Mathlib.LinearAlgebra.RootSystem.OfBilinear
import Mathlib.LinearAlgebra.Transvection.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module

/-!
# Reflection in the hyperplane orthogonal to a non-null vector

For a bilinear form `g` on a vector space `V` over a field `K` and a vector `u`, the reflection
`LinearMap.BilinForm.reflection g u : v ↦ v - 2 (g u v / g u u) • u` is
`Module.preReflection u f` for the functional `f = 2 g u · / g u u`. It is defined
unconditionally and is the identity when `g u u = 0`, since `(0 : K)⁻¹ = 0`. For `g u u ≠ 0` the
vector `u` is reflective in the sense of `LinearMap.IsReflective`, and the reflection is Mathlib's
`Module.reflection` along the associated coroot, so the upstream reflection API applies.

## Main statements

* `LinearMap.BilinForm.isReflective_of_apply_self_ne_zero`, `reflection_eq_moduleReflection`: for
  `g u u ≠ 0`, `u` is reflective and `g.reflection u` is the corresponding `Module.reflection`.
* `LinearMap.BilinForm.reflection_reflection_apply`, `isOrthogonal_reflection`: the reflection is
  an involution and, for symmetric `g`, a `g`-isometry (`LinearMap.IsOrthogonal`).
* `LinearMap.BilinForm.det_reflection`: for `g u u ≠ 0` it has determinant `-1` in finite
  dimension.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Reflection of `V` in the `g`-orthogonal hyperplane to `u`, `v ↦ v - 2 (g u v / g u u) u`:
`Module.preReflection u f` for the functional `f = 2 g u · / g u u`, which satisfies `f u = 2`
when `g u u ≠ 0`. The definition is unconditional; it is a `g`-isometry
(`LinearMap.IsOrthogonal`) when `g` is symmetric (`isOrthogonal_reflection`), and degenerates to
the identity when `g u u = 0`, since `(0 : K)⁻¹ = 0`. -/
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

/-- A non-null vector is reflective for `g` in the sense of `LinearMap.IsReflective`. -/
lemma isReflective_of_apply_self_ne_zero (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.IsReflective g u where
  regular := (isUnit_iff_ne_zero.mpr hu).isRegular
  dvd_two_mul _ := (isUnit_iff_ne_zero.mpr hu).dvd

/-- For non-null `u`, `g.reflection u` is Mathlib's `Module.reflection` along the coroot of the
reflective vector `u`. -/
lemma reflection_eq_moduleReflection (g : BilinForm K V) {u : V} (hu : g u u ≠ 0) :
    g.reflection u = (Module.reflection (LinearMap.IsReflective.coroot_apply_self g
      (g.isReflective_of_apply_self_ne_zero hu)) : V →ₗ[K] V) := by
  ext v
  have h := LinearMap.IsReflective.apply_self_mul_coroot_apply g
    (g.isReflective_of_apply_self_ne_zero hu) (y := v)
  rw [reflection_apply, LinearEquiv.coe_coe, Module.reflection_apply]
  congr 2
  field_simp
  linear_combination -h

/-- The reflection is an involution. For `g u u = 0` it is the identity. -/
@[simp]
lemma reflection_reflection_apply (g : BilinForm K V) (u v : V) :
    reflection g u (reflection g u v) = v := by
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [reflection_apply, hu]
  exact Module.involutive_preReflection
    (by rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]) v

/-- The reflection is a `g`-isometry when `g` is symmetric: for `g u u ≠ 0` this is Mathlib's
`LinearMap.IsReflective.isOrthogonal_reflection`, and for `g u u = 0` it is the identity. -/
lemma isOrthogonal_reflection (g : BilinForm K V) (hSymm : g.IsSymm) (u : V) :
    g.IsOrthogonal (reflection g u) := by
  rcases eq_or_ne (g u u) 0 with hu | hu
  · intro v w
    simp [reflection_apply, hu]
  rw [g.reflection_eq_moduleReflection hu, LinearEquiv.coe_coe]
  exact LinearMap.IsReflective.isOrthogonal_reflection g _ (isSymm_iff.mp hSymm)

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
