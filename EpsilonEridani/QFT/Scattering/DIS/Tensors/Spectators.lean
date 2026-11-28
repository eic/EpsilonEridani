/-
Copyright (c) 2026 Joseph Tooby-Smith, Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic
import EpsilonEridani.Mathematics.LinearAlgebra.SesquilinearForm.Basic

/-!
# Spectator frames and turns of the spectator plane

Kinematic inputs of the parity-odd sector (`Tensors.ParityOdd`) and of the three-coefficient
decomposition (`Tensors.Decomposition`). Like `SpectatorAssumptions` they are, apart from the
last result below, facts about `g`, `p`, `q` and the isometry group rather than about the
hadronic tensor; they supply the determinant-one stabilizer elements that
`IsProperLorentzCovariant` constrains.

## Main definitions

- `SpectatorPair`: two non-null, mutually orthogonal spectator directions `e₁`, `e₂`.
- `SpectatorPlane`: a `SpectatorPair` completing `p_T`, `q` to a frame of `V`.
- `SpectatorPair.equalizeNorms`, `SpectatorPlane.equalizeNorms`: `e₂` rescaled to the norm of `e₁`,
  when the two norms have the same sign.

## Main results

- `reflection_comp_reflection_isKinematicStabilizer`: the composite of the reflections in two
  spectators is a stabilizer element, for non-null spectators of determinant one by
  `LinearMap.BilinForm.det_reflection_comp_reflection`.
- `exists_half_turn`: two orthogonal spectators are both reversed by such an element.
- `exists_quarter_turn`: two orthogonal spectators of equal norm are turned into each other,
  `u ↦ u' ↦ -u`, by such an element.
- `IsProperLorentzCovariant.apply_eq_of_spectatorPair`: the half-turn removes the mixed
  `p_T`-spectator components of a conserved, properly covariant tensor, leaving `W(p_T, p_T)`
  and its four spectator components.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Tensors

variable {V : Type} [AddCommGroup V] [Module ℝ V]

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin)

namespace Hadronic

open Kinematics

/-!
## Turns of the spectator plane
-/

/-- The composite of the reflections in two spectators `u` and `u'` is a kinematic stabilizer
element; for non-null `u`, `u'` its determinant is one by
`LinearMap.BilinForm.det_reflection_comp_reflection`. -/
lemma reflection_comp_reflection_isKinematicStabilizer {g : Bilin V} {K : DisKinematics V}
    (hSymm : g.IsSymm) {u u' : V} (huq : g K.q u = 0) (huT : g (pTransverse g K) u = 0)
    (hu'q : g K.q u' = 0) (hu'T : g (pTransverse g K) u' = 0) :
    IsKinematicStabilizer g K (g.reflection u ∘ₗ g.reflection u') := by
  have h₁ := reflection_isKinematicStabilizer g K hSymm u
    (apply_p_eq_zero_of_spectator g K hSymm huq huT) (by rw [hSymm.eq, huq])
  have h₂ := reflection_isKinematicStabilizer g K hSymm u'
    (apply_p_eq_zero_of_spectator g K hSymm hu'q hu'T) (by rw [hSymm.eq, hu'q])
  exact ⟨by rw [LinearMap.coe_comp]; exact h₁.isOrthogonal.comp h₂.isOrthogonal,
    by rw [LinearMap.comp_apply, h₂.fixes_p, h₁.fixes_p],
    by rw [LinearMap.comp_apply, h₂.fixes_q, h₁.fixes_q]⟩

/-- Two orthogonal non-null spectators `u` and `u'` give a kinematic stabilizer element of
determinant one reversing both: the composite of the reflections in `u` and in `u'`. -/
lemma exists_half_turn {g : Bilin V} {K : DisKinematics V} (hSymm : g.IsSymm)
    {u u' : V} (huq : g K.q u = 0) (huT : g (pTransverse g K) u = 0) (hu : g u u ≠ 0)
    (hu'q : g K.q u' = 0) (hu'T : g (pTransverse g K) u' = 0) (hu' : g u' u' ≠ 0)
    (huu' : g u u' = 0) :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f u = -u ∧ f u' = -u' := by
  have hu'u : g u' u = 0 := by rw [hSymm.eq, huu']
  refine ⟨_, reflection_comp_reflection_isKinematicStabilizer hSymm huq huT hu'q hu'T,
    g.det_reflection_comp_reflection hu hu', ?_, ?_⟩
  · rw [LinearMap.comp_apply, g.reflection_apply_of_orthogonal _ _ hu'u,
      g.reflection_apply_self _ hu]
  · rw [LinearMap.comp_apply, g.reflection_apply_self _ hu', map_neg,
      g.reflection_apply_of_orthogonal _ _ huu']

/-- Two orthogonal spectators `u` and `u'` of equal non-zero norm give a kinematic stabilizer
element of determinant one with `u ↦ u' ↦ -u`: the reflection in `u - u'` exchanges `u` and
`u'`, and the reflection in `u` then reverses `u`. -/
lemma exists_quarter_turn {g : Bilin V} {K : DisKinematics V} (hSymm : g.IsSymm) {u u' : V}
    (huq : g K.q u = 0) (huT : g (pTransverse g K) u = 0) (hu : g u u ≠ 0)
    (hu'q : g K.q u' = 0) (hu'T : g (pTransverse g K) u' = 0) (huu' : g u u' = 0)
    (hnorm : g u u = g u' u') :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f u = u' ∧ f u' = -u := by
  have hdd : g (u - u') (u - u') = 2 * g u u := by
    rw [Bilin.apply_sub_self g hSymm, huu', ← hnorm]
    ring
  have hdd0 : g (u - u') (u - u') ≠ 0 := by
    rw [hdd]
    exact mul_ne_zero two_ne_zero hu
  have hdq : g K.q (u - u') = 0 := by rw [map_sub, huq, hu'q, sub_zero]
  have hdT : g (pTransverse g K) (u - u') = 0 := by rw [map_sub, huT, hu'T, sub_zero]
  refine ⟨_, reflection_comp_reflection_isKinematicStabilizer hSymm huq huT hdq hdT,
    g.det_reflection_comp_reflection hu hdd0, ?_, ?_⟩
  · rw [LinearMap.comp_apply, g.reflection_sub_apply_left hSymm hnorm hdd0,
      g.reflection_apply_of_orthogonal _ _ huu']
  · rw [LinearMap.comp_apply, g.reflection_sub_apply_right hSymm hnorm hdd0,
      g.reflection_apply_self _ hu]

/-!
## Spectator pairs and planes
-/

/-- Two spectator directions `e₁`, `e₂` for the kinematics, non-null and `g`-orthogonal to each
other and to `p_T` and `q`. They supply the half-turn of `exists_half_turn`, at equal norms the
quarter-turn of `exists_quarter_turn`, and, through `e₁`, the probe pairs
`uniquenessAssumptionsOfSpectator` of the `F1`/`F2` uniqueness theorem. `SpectatorPlane` adds
that they complete `p_T`, `q` to a frame of `V`. -/
@[ext]
structure SpectatorPair (g : Bilin V) (K : DisKinematics V) : Type where
  /-- The first spectator direction. -/
  e₁ : V
  /-- The second spectator direction. -/
  e₂ : V
  /-- The momentum transfer is `g`-orthogonal to `e₁`. -/
  q_orthogonal_e₁ : g K.q e₁ = 0
  /-- The momentum transfer is `g`-orthogonal to `e₂`. -/
  q_orthogonal_e₂ : g K.q e₂ = 0
  /-- The transverse hadron momentum is `g`-orthogonal to `e₁`. -/
  pT_orthogonal_e₁ : g (pTransverse g K) e₁ = 0
  /-- The transverse hadron momentum is `g`-orthogonal to `e₂`. -/
  pT_orthogonal_e₂ : g (pTransverse g K) e₂ = 0
  /-- The two spectator directions are orthogonal. -/
  e₁_orthogonal_e₂ : g e₁ e₂ = 0
  /-- `e₁` is not null. -/
  e₁_self_ne_zero : g e₁ e₁ ≠ 0
  /-- `e₂` is not null. -/
  e₂_self_ne_zero : g e₂ e₂ ≠ 0

/-- The momentum transfer is `g`-orthogonal to a combination of the spectator directions. -/
lemma SpectatorPair.q_orthogonal_smul_add_smul {g : Bilin V} {K : DisKinematics V}
    (hP : SpectatorPair g K) (c₁ c₂ : ℝ) : g K.q (c₁ • hP.e₁ + c₂ • hP.e₂) = 0 := by
  simp only [map_add, map_smul, hP.q_orthogonal_e₁, hP.q_orthogonal_e₂, smul_zero, add_zero]

/-- The transverse hadron momentum is `g`-orthogonal to a combination of the spectator
directions. -/
lemma SpectatorPair.pT_orthogonal_smul_add_smul {g : Bilin V} {K : DisKinematics V}
    (hP : SpectatorPair g K) (c₁ c₂ : ℝ) :
    g (pTransverse g K) (c₁ • hP.e₁ + c₂ • hP.e₂) = 0 := by
  simp only [map_add, map_smul, hP.pT_orthogonal_e₁, hP.pT_orthogonal_e₂, smul_zero, add_zero]

/-- The half-turn of a `SpectatorPair`: a kinematic stabilizer element of determinant one
reversing both spectator directions (`exists_half_turn` applied to `e₁`, `e₂`). -/
lemma SpectatorPair.exists_half_turn {g : Bilin V} {K : DisKinematics V}
    (hP : SpectatorPair g K) (hSymm : g.IsSymm) :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f hP.e₁ = -hP.e₁ ∧ f hP.e₂ = -hP.e₂ :=
  Hadronic.exists_half_turn hSymm hP.q_orthogonal_e₁ hP.pT_orthogonal_e₁ hP.e₁_self_ne_zero
    hP.q_orthogonal_e₂ hP.pT_orthogonal_e₂ hP.e₂_self_ne_zero hP.e₁_orthogonal_e₂

/-- **The half-turn removes the mixed `p_T`-spectator components.** On the span of `p_T`, `q`
and a `SpectatorPair` `e₁`, `e₂`, a conserved, properly covariant tensor is determined by
`W(p_T, p_T)` and its four spectator components. -/
lemma IsProperLorentzCovariant.apply_eq_of_spectatorPair {g : Bilin V} {K : DisKinematics V}
    {W : Bilin V} (hSymm : g.IsSymm) (hP : SpectatorPair g K) (hW : IsProperLorentzCovariant g K W)
    (hleft : ∀ v : V, W K.q v = 0) (hright : ∀ v : V, W v K.q = 0)
    (a b c₁ c₂ a' b' d₁ d₂ : ℝ) :
    W (a • pTransverse g K + b • K.q + c₁ • hP.e₁ + c₂ • hP.e₂)
        (a' • pTransverse g K + b' • K.q + d₁ • hP.e₁ + d₂ • hP.e₂) =
      a * a' * W (pTransverse g K) (pTransverse g K) + c₁ * d₁ * W hP.e₁ hP.e₁
        + c₁ * d₂ * W hP.e₁ hP.e₂ + c₂ * d₁ * W hP.e₂ hP.e₁ + c₂ * d₂ * W hP.e₂ hP.e₂ := by
  obtain ⟨f, hf, hdet, hf₁, hf₂⟩ := hP.exists_half_turn hSymm
  have hT₁ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₁
  have hT₂ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₂
  have h₁T := hW.apply_pTransverse_right_eq_zero_of_apply_eq_neg hf hdet hf₁
  have h₂T := hW.apply_pTransverse_right_eq_zero_of_apply_eq_neg hf hdet hf₂
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hleft,
    hright, hT₁, hT₂, h₁T, h₂T]
  ring

/-- An adapted frame for the kinematics: a `SpectatorPair` `e₁`, `e₂` such that `p_T`, `q`,
`e₁`, `e₂` span `V`.

For `V` Minkowski space with `p` timelike and `q` spacelike the spectator subspace
`{p, q}^⊥` is a spacelike plane, and any orthogonal basis of it is such a frame. The frame
is the only place where four-dimensionality enters the hypotheses on the hadronic tensor
`W` of `Tensors.ParityOdd` and `Tensors.Decomposition`; constructing the canonical
parity-odd structure `A` there needs an alternating four-form, and its proper covariance a
basis of four vectors, separately. -/
@[ext]
structure SpectatorPlane (g : Bilin V) (K : DisKinematics V) : Type extends SpectatorPair g K where
  /-- The frame spans `V`. -/
  span : ∀ v : V, ∃ a b c₁ c₂ : ℝ, v = a • pTransverse g K + b • K.q + c₁ • e₁ + c₂ • e₂

/-- The adapted frame of a `SpectatorPlane` splits every vector: the spectator part of
`a • p_T + b • q + c₁ • e₁ + c₂ • e₂` is `c₁ • e₁ + c₂ • e₂`. -/
lemma SpectatorPlane.toSpectatorSplitting {g : Bilin V} {K : DisKinematics V}
    (hP : SpectatorPlane g K) : SpectatorSplitting g K where
  span v := by
    obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
    exact ⟨a, b, c₁ • hP.e₁ + c₂ • hP.e₂, hP.q_orthogonal_smul_add_smul c₁ c₂,
      hP.pT_orthogonal_smul_add_smul c₁ c₂, add_assoc _ _ _⟩

/-- The quarter-turn of a `SpectatorPair` whose directions have equal norm: a kinematic
stabilizer element of determinant one with `e₁ ↦ e₂ ↦ -e₁` (`exists_quarter_turn` applied to
`e₁`, `e₂`). -/
lemma SpectatorPair.exists_quarter_turn {g : Bilin V} {K : DisKinematics V}
    (hP : SpectatorPair g K) (hSymm : g.IsSymm) (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂) :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f hP.e₁ = hP.e₂ ∧ f hP.e₂ = -hP.e₁ :=
  Hadronic.exists_quarter_turn hSymm hP.q_orthogonal_e₁ hP.pT_orthogonal_e₁ hP.e₁_self_ne_zero
    hP.q_orthogonal_e₂ hP.pT_orthogonal_e₂ hP.e₁_orthogonal_e₂ hnorm

section equalizeNorms

variable {g : Bilin V} {K : DisKinematics V}

/-- The ratio of the two norms of a `SpectatorPair` is positive when they have the same sign;
`SpectatorPair.equalizeNorms` rescales `e₂` by its square root. -/
lemma SpectatorPair.equalizeNorms_div_pos (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) :
    0 < g hP.e₁ hP.e₁ / g hP.e₂ hP.e₂ :=
  div_pos_iff.mpr (mul_pos_iff.mp hsign)

/-- A `SpectatorPair` whose two directions have norms of the same sign, with `e₂` rescaled by
`√(e₁·e₁ / e₂·e₂)` so that both directions have the norm of `e₁`
(`SpectatorPair.equalizeNorms_self_eq`). -/
noncomputable def SpectatorPair.equalizeNorms (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) : SpectatorPair g K where
  e₁ := hP.e₁
  e₂ := √(g hP.e₁ hP.e₁ / g hP.e₂ hP.e₂) • hP.e₂
  q_orthogonal_e₁ := hP.q_orthogonal_e₁
  q_orthogonal_e₂ := by rw [map_smul, hP.q_orthogonal_e₂, smul_zero]
  pT_orthogonal_e₁ := hP.pT_orthogonal_e₁
  pT_orthogonal_e₂ := by rw [map_smul, hP.pT_orthogonal_e₂, smul_zero]
  e₁_orthogonal_e₂ := by rw [map_smul, hP.e₁_orthogonal_e₂, smul_zero]
  e₁_self_ne_zero := hP.e₁_self_ne_zero
  e₂_self_ne_zero := by
    have ht := Real.sqrt_ne_zero'.mpr (hP.equalizeNorms_div_pos hsign)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero ht (mul_ne_zero ht hP.e₂_self_ne_zero)

@[simp] lemma SpectatorPair.equalizeNorms_e₁ (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) : (hP.equalizeNorms hsign).e₁ = hP.e₁ := (rfl)

@[simp] lemma SpectatorPair.equalizeNorms_e₂ (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) :
    (hP.equalizeNorms hsign).e₂ = √(g hP.e₁ hP.e₁ / g hP.e₂ hP.e₂) • hP.e₂ := (rfl)

/-- The two directions of `SpectatorPair.equalizeNorms` have equal norms. -/
lemma SpectatorPair.equalizeNorms_self_eq (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) :
    g (hP.equalizeNorms hsign).e₁ (hP.equalizeNorms hsign).e₁ =
      g (hP.equalizeNorms hsign).e₂ (hP.equalizeNorms hsign).e₂ := by
  rw [equalizeNorms_e₁, equalizeNorms_e₂,
    Bilin.apply_smul_sqrt_div_self g hP.e₂_self_ne_zero (hP.equalizeNorms_div_pos hsign).le]

/-- A `SpectatorPlane` whose two directions have norms of the same sign, with `e₂` rescaled as in
`SpectatorPair.equalizeNorms`; it is still a frame. -/
noncomputable def SpectatorPlane.equalizeNorms (hP : SpectatorPlane g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) : SpectatorPlane g K where
  toSpectatorPair := hP.toSpectatorPair.equalizeNorms hsign
  span v := by
    obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
    refine ⟨a, b, c₁, c₂ / √(g hP.e₁ hP.e₁ / g hP.e₂ hP.e₂), ?_⟩
    rw [SpectatorPair.equalizeNorms_e₁, SpectatorPair.equalizeNorms_e₂, smul_smul,
      div_mul_cancel₀ _
        (Real.sqrt_ne_zero'.mpr (hP.toSpectatorPair.equalizeNorms_div_pos hsign))]

@[simp] lemma SpectatorPlane.equalizeNorms_toSpectatorPair (hP : SpectatorPlane g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) :
    (hP.equalizeNorms hsign).toSpectatorPair = hP.toSpectatorPair.equalizeNorms hsign := (rfl)

end equalizeNorms

end Hadronic

end Tensors
end DIS
end Scattering
end QFT
end EpsilonEridani
