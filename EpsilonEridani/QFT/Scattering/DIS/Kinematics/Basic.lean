/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Deep Inelastic Scattering Kinematics

This module introduces a minimal kinematic record and canonical DIS invariants.
The design follows the architecture freeze document.

It also supplies the basic API of the abstract bilinear form `Bilin V` that the kinematics is
evaluated against: the expansion `Bilin.apply_sub_smul_pair`, the projection
`Bilin.projOrthogonal` onto the `g`-orthogonal complement of a non-null vector, the rank-one
forms `Bilin.rankOne`, the `g`-isometries `Bilin.IsIsometry` and the reflections
`Bilin.reflect`.

-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]

/-- A bilinear form used to evaluate Lorentz-invariant scalar products in abstract form. -/
abbrev Bilin (V : Type) [AddCommGroup V] [Module ℝ V] := LinearMap.BilinForm ℝ V

namespace Bilin

variable {V}

/-- Expansion of a bilinear form on a pair of vectors each shifted along `u`. -/
lemma apply_sub_smul_pair (g : Bilin V) (u x y : V) (a b : ℝ) :
    g (x - a • u) (y - b • u)
      = g x y - b * g x u - a * g u y + a * b * g u u := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The projection along `ℝ ∙ u` onto the `g`-orthogonal complement of `u`,
`v ↦ v - (g v u / g u u) • u`. It is `Module.preReflection u f` for the functional
`f = g · u / g u u`, which satisfies `f u = 1` when `g u u ≠ 0` (rather than the `f u = 2` of a
reflection). The definition is unconditional and degenerates to the identity when `g u u = 0`,
since `(0 : ℝ)⁻¹ = 0`. -/
noncomputable def projOrthogonal (g : Bilin V) (u : V) : V →ₗ[ℝ] V :=
  Module.preReflection u ((g u u)⁻¹ • g.flip u)

lemma projOrthogonal_apply (g : Bilin V) (u v : V) :
    g.projOrthogonal u v = v - (g v u / g u u) • u := by
  simp [projOrthogonal, Module.preReflection_apply, div_eq_inv_mul]

/-- The projection of any vector is `g`-orthogonal to `u`. -/
lemma projOrthogonal_orthogonal (g : Bilin V) {u : V} (hu : g u u ≠ 0) (v : V) :
    g (g.projOrthogonal u v) u = 0 := by
  simp [projOrthogonal_apply, hu]

/-- The projection annihilates `u`. -/
lemma projOrthogonal_apply_self (g : Bilin V) {u : V} (hu : g u u ≠ 0) :
    g.projOrthogonal u u = 0 := by
  rw [projOrthogonal_apply, div_self hu, one_smul, sub_self]

/-- The projection fixes exactly the vectors `v` with `g v u = 0`. -/
lemma projOrthogonal_eq_self_iff (g : Bilin V) {u : V} (hu : g u u ≠ 0) {v : V} :
    g.projOrthogonal u v = v ↔ g v u = 0 := by
  rw [projOrthogonal_apply, sub_eq_self, smul_eq_zero, div_eq_zero_iff]
  simp [hu, LinearMap.BilinForm.ne_zero_of_not_isOrtho_self u hu]

/-- The projection is idempotent. -/
lemma projOrthogonal_projOrthogonal (g : Bilin V) {u : V} (hu : g u u ≠ 0) (v : V) :
    g.projOrthogonal u (g.projOrthogonal u v) = g.projOrthogonal u v :=
  (g.projOrthogonal_eq_self_iff hu).mpr (g.projOrthogonal_orthogonal hu v)

/-- The kernel of the projection is the line `ℝ ∙ u`. -/
lemma ker_projOrthogonal (g : Bilin V) {u : V} (hu : g u u ≠ 0) :
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
lemma range_projOrthogonal (g : Bilin V) {u : V} (hu : g u u ≠ 0) :
    LinearMap.range (g.projOrthogonal u) = g.flip.orthogonal (ℝ ∙ u) := by
  rw [LinearMap.BilinForm.orthogonal, Submodule.orthogonalBilin_span_singleton]
  ext v
  rw [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.BilinForm.flip_apply]
  exact ⟨by rintro ⟨w, rfl⟩; exact g.projOrthogonal_orthogonal hu w,
    fun hv ↦ ⟨v, (g.projOrthogonal_eq_self_iff hu).mpr hv⟩⟩

/-- The pairing of two projected vectors: `g (projOrthogonal u v) (projOrthogonal u w)
= g v w - g v u * g u w / g u u`. No symmetry of `g` is needed, and when `g u u = 0` both sides
are `g v w`. -/
lemma projOrthogonal_pairing (g : Bilin V) (u v w : V) :
    g (g.projOrthogonal u v) (g.projOrthogonal u w) = g v w - g v u * g u w / g u u := by
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [projOrthogonal_apply, hu]
  rw [projOrthogonal_apply, projOrthogonal_apply, apply_sub_smul_pair]
  field_simp
  ring

/-- The projection depends on `u` only through the line `ℝ ∙ u`. -/
lemma projOrthogonal_smul (g : Bilin V) {c : ℝ} (hc : c ≠ 0) (u : V) :
    g.projOrthogonal (c • u) = g.projOrthogonal u := by
  ext v
  rcases eq_or_ne (g u u) 0 with hu | hu
  · simp [projOrthogonal_apply, hu]
  simp only [projOrthogonal_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_smul]
  congr 2
  field_simp

/-- Rank-one bilinear form `(v,w) ↦ g(a,v) g(b,w)` derived from a background bilinear form `g`. -/
def rankOne (g : Bilin V) (a b : V) : Bilin V where
  toFun := fun v =>
    { toFun := fun w => g a v * g b w
      map_add' := by
        intro w₁ w₂
        simp [mul_add, map_add]
      map_smul' := by
        intro c w
        change g a v * g b (c • w) = c * (g a v * g b w)
        rw [map_smul]
        ring }
  map_add' := by
    intro v₁ v₂
    ext w
    simp [add_mul, map_add]
  map_smul' := by
    intro c v
    ext w
    change g a (c • v) * g b w = c * (g a v * g b w)
    rw [map_smul]
    ring

@[simp] lemma rankOne_apply (g : Bilin V) (a b v w : V) :
    rankOne g a b v w = g a v * g b w := rfl

/-- A rank-one form built from a single vector is symmetric. -/
lemma rankOne_isSymm (g : Bilin V) (a : V) : (rankOne g a a).IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp [rankOne_apply, mul_comm]

/-- A linear endomorphism preserving the background form `g`. For `g` a Lorentz metric these
are exactly the (linear) Lorentz transformations. -/
def IsIsometry (g : Bilin V) (f : V →ₗ[ℝ] V) : Prop :=
  ∀ v w : V, g (f v) (f w) = g v w

/-- The identity map is a `g`-isometry. -/
lemma isIsometry_id (g : Bilin V) : IsIsometry g (LinearMap.id) := by
  intro v w
  simp

/-- Reflection of `V` in the `g`-orthogonal hyperplane to `u`, `v ↦ v - 2 (g u v / g u u) u`:
`Module.preReflection u f` for the functional `f = 2 g u · / g u u`, which satisfies `f u = 2`
when `g u u ≠ 0`. The definition is unconditional; it is a `g`-isometry when `g` is symmetric
and `g u u ≠ 0` (`reflect_isometry`), and degenerates to the identity when `g u u = 0`, since
`(0 : ℝ)⁻¹ = 0`. -/
noncomputable def reflect (g : Bilin V) (u : V) : V →ₗ[ℝ] V :=
  Module.preReflection u ((2 * (g u u)⁻¹) • g u)

@[simp] lemma reflect_apply (g : Bilin V) (u v : V) :
    reflect g u v = v - (2 * (g u u)⁻¹ * g u v) • u := by
  simp only [reflect, Module.preReflection_apply, LinearMap.smul_apply, smul_eq_mul]

/-- The reflection in `u` reverses `u`. -/
lemma reflect_apply_self (g : Bilin V) (u : V) (hu : g u u ≠ 0) :
    reflect g u u = -u :=
  Module.preReflection_apply_self <| by
    rw [LinearMap.smul_apply, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hu, mul_one]

/-- The reflection in `u` fixes every vector `g`-orthogonal to `u`. -/
lemma reflect_apply_of_orthogonal (g : Bilin V) (u v : V) (h : g u v = 0) :
    reflect g u v = v := by
  rw [reflect_apply, h, mul_zero, zero_smul, sub_zero]

/-- A reflection in a non-null direction is a `g`-isometry when `g` is symmetric. -/
lemma reflect_isometry (g : Bilin V) (hSymm : g.IsSymm) (u : V) (hu : g u u ≠ 0) :
    IsIsometry g (reflect g u) := by
  intro v w
  have hc : (g u u)⁻¹ * g u u = 1 := inv_mul_cancel₀ hu
  rw [reflect_apply, reflect_apply, apply_sub_smul_pair, hSymm.eq v u]
  linear_combination (4 * (g u u)⁻¹ * g u v * g u w) * hc

end Bilin

/-- Minimal process-level kinematics for inclusive DIS. -/
structure DisKinematics where
  /-- Incoming hadron momentum. -/
  p : V
  /-- Outgoing hadron momentum in exclusive/semi-inclusive projections.
    For inclusive DIS this field can be carried as background data. -/
  pPrime : V
  /-- Incoming lepton momentum. -/
  k : V
  /-- Outgoing hadron-side aggregate not represented explicitly here; outgoing lepton momentum. -/
  kPrime : V
  /-- Momentum transfer to the hadronic system. -/
  q : V
  /-- Kinematic relation `q = k - kPrime`. -/
  hq : q = k - kPrime

namespace DisKinematics

variable {V}

/-- The hard scale `Q2 := - q^2`. -/
def Q2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  - g K.q K.q

/-- The Bjorken scaling variable `xBj := Q2 / (2 p·q)`. -/
noncomputable def xBj (g : Bilin V) (K : DisKinematics V) : ℝ :=
  K.Q2 g / (2 * g K.p K.q)

/-- The inelasticity variable `y := (p·q)/(p·k)`. -/
noncomputable def yInel (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g K.p K.q / g K.p K.k

/-- The hadronic invariant mass squared `W2 := (p + q)^2`. -/
def W2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (K.p + K.q) (K.p + K.q)

omit [Module ℝ V] in
lemma q_eq_sub (K : DisKinematics V) : K.q = K.k - K.kPrime := K.hq

omit [Module ℝ V] in
lemma kPrime_eq (K : DisKinematics V) : K.kPrime = K.k - K.q := by
  have hSub : K.k - K.q = K.kPrime := by
    calc
      K.k - K.q = K.k - (K.k - K.kPrime) := by rw [K.hq]
      _ = K.kPrime := by abel
  exact hSub.symm

/-- A direct expansion of `W2` in terms of bilinear pieces. -/
lemma W2_expand (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    K.W2 g = g K.p K.p + 2 * g K.p K.q + g K.q K.q := by
  unfold W2
  calc
    g (K.p + K.q) (K.p + K.q)
    = g (K.p + K.q) K.p + g (K.p + K.q) K.q := by
        rw [(g (K.p + K.q)).map_add]
    _ = (g K.p K.p + g K.q K.p) + (g K.p K.q + g K.q K.q) := by
      have hp : g (K.p + K.q) K.p = g K.p K.p + g K.q K.p := by
        rw [map_add, LinearMap.add_apply]
      have hq : g (K.p + K.q) K.q = g K.p K.q + g K.q K.q := by
        rw [map_add, LinearMap.add_apply]
      rw [hp, hq]
    _ = g K.p K.p + g K.p K.q + (g K.q K.p + g K.q K.q) := by ring
    _ = g K.p K.p + g K.p K.q + (g K.p K.q + g K.q K.q) := by
      rw [hSymm.eq K.q K.p]
    _ = g K.p K.p + 2 * g K.p K.q + g K.q K.q := by ring

/-- Rewrite `W2` using `Q2 = -q^2`. -/
lemma W2_eq_with_Q2 (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    K.W2 g = g K.p K.p + 2 * g K.p K.q - K.Q2 g := by
  rw [W2_expand g K hSymm]
  unfold Q2
  ring

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
