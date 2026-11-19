/-
Copyright (c) 2026 Joseph Tooby-Smith, Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic

/-!
# Spectator frames and turns of the spectator plane

Kinematic inputs of the parity-odd sector (`Tensors.ParityOdd`) and of the three-coefficient
decomposition (`Tensors.Decomposition`). Like `SpectatorAssumptions` they are facts about `g`,
`p`, `q` and the isometry group, not about the hadronic tensor; they supply the determinant-one
stabilizer elements that `IsProperLorentzCovariant` constrains.

## Main definitions

- `SpectatorPair`: two non-null, mutually orthogonal spectator directions `e₁`, `e₂`.
- `SpectatorPlane`: a `SpectatorPair` completing `p_T`, `q` to a frame of `V`.
- `SpectatorPair.normalize`, `SpectatorPlane.normalize`: `e₂` rescaled to the norm of `e₁`,
  when the two norms have the same sign.
- `SpectatorPair.uniquenessAssumptions`: the probe pairs of `UniquenessAssumptions` built from
  `e₁` and `p_T`.

## Main results

- `reflect_comp_reflect_isKinematicStabilizer`: the composite of the reflections in two
  non-null spectators is a stabilizer element, of determinant one by
  `Bilin.det_reflect_comp_reflect`.
- `exists_half_turn`: two orthogonal spectators are both reversed by such an element.
- `exists_quarter_turn`: two orthogonal spectators of equal norm are turned into each other,
  `u ↦ u' ↦ -u`, by such an element.
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

/-- The composite of the reflections in two non-null spectators `u` and `u'` is a kinematic
stabilizer element; its determinant is one by `Bilin.det_reflect_comp_reflect`. -/
lemma reflect_comp_reflect_isKinematicStabilizer {g : Bilin V} {K : DisKinematics V}
    (hSymm : g.IsSymm) {u u' : V} (huq : g K.q u = 0) (huT : g (pTransverse g K) u = 0)
    (hu : g u u ≠ 0) (hu'q : g K.q u' = 0) (hu'T : g (pTransverse g K) u' = 0)
    (hu' : g u' u' ≠ 0) :
    IsKinematicStabilizer g K (Bilin.reflect g u ∘ₗ Bilin.reflect g u') := by
  have h₁ := reflect_isKinematicStabilizer g K hSymm _ hu
    (apply_p_eq_zero_of_spectator g K hSymm huq huT) (by rw [hSymm.eq, huq])
  have h₂ := reflect_isKinematicStabilizer g K hSymm _ hu'
    (apply_p_eq_zero_of_spectator g K hSymm hu'q hu'T) (by rw [hSymm.eq, hu'q])
  exact ⟨fun v w => by simp only [LinearMap.comp_apply, h₁.isometry _ _, h₂.isometry _ _],
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
  refine ⟨_, reflect_comp_reflect_isKinematicStabilizer hSymm huq huT hu hu'q hu'T hu',
    Bilin.det_reflect_comp_reflect g hu hu', ?_, ?_⟩
  · rw [LinearMap.comp_apply, Bilin.reflect_apply_of_orthogonal g _ _ hu'u,
      Bilin.reflect_apply_self g _ hu]
  · rw [LinearMap.comp_apply, Bilin.reflect_apply_self g _ hu', map_neg,
      Bilin.reflect_apply_of_orthogonal g _ _ huu']

/-- Two orthogonal spectators `u` and `u'` of equal non-zero norm give a kinematic stabilizer
element of determinant one with `u ↦ u' ↦ -u`: the reflection in `u - u'` exchanges `u` and
`u'`, and the reflection in `u` then reverses `u`. -/
lemma exists_quarter_turn {g : Bilin V} {K : DisKinematics V} (hSymm : g.IsSymm) {u u' : V}
    (huq : g K.q u = 0) (huT : g (pTransverse g K) u = 0) (hu : g u u ≠ 0)
    (hu'q : g K.q u' = 0) (hu'T : g (pTransverse g K) u' = 0) (huu' : g u u' = 0)
    (hnorm : g u u = g u' u') :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f u = u' ∧ f u' = -u := by
  have hu'u : g u' u = 0 := by rw [hSymm.eq, huu']
  have hdd : g (u - u') (u - u') = 2 * g u u := by
    simp only [map_sub, LinearMap.sub_apply, huu', hu'u, ← hnorm]
    ring
  have hdd0 : g (u - u') (u - u') ≠ 0 := by
    rw [hdd]
    exact mul_ne_zero two_ne_zero hu
  have hdq : g K.q (u - u') = 0 := by rw [map_sub, huq, hu'q, sub_zero]
  have hdT : g (pTransverse g K) (u - u') = 0 := by rw [map_sub, huT, hu'T, sub_zero]
  refine ⟨_, reflect_comp_reflect_isKinematicStabilizer hSymm huq huT hu hdq hdT hdd0,
    Bilin.det_reflect_comp_reflect g hu hdd0, ?_, ?_⟩
  · rw [LinearMap.comp_apply, Bilin.reflect_sub_apply_left g hSymm hnorm hdd0,
      Bilin.reflect_apply_of_orthogonal g _ _ huu']
  · rw [LinearMap.comp_apply, Bilin.reflect_sub_apply_right g hSymm hnorm hdd0,
      Bilin.reflect_apply_self g _ hu]

/-!
## Spectator pairs and planes
-/

/-- Two spectator directions `e₁`, `e₂` for the kinematics, non-null and `g`-orthogonal to each
other and to `p_T` and `q`. They supply the half-turn of `exists_half_turn`, at equal norms the
quarter-turn of `exists_quarter_turn`, and the probe pairs `SpectatorPair.uniquenessAssumptions`
of the `F1`/`F2` uniqueness theorem; `SpectatorPlane` adds that they complete `p_T`, `q` to a
frame of `V`. -/
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

/-- The probe pairs of `UniquenessAssumptions` supplied by a spectator pair: `(e₁, e₁)` sees only
the transverse projector, and `(p_T + e₁, p_T - (p_T·p_T / e₁·e₁) e₁)` sees only
`p_T ⊗ p_T`, which needs `p_T` to be non-null. -/
noncomputable def SpectatorPair.uniquenessAssumptions {g : Bilin V} {K : DisKinematics V}
    (hP : SpectatorPair g K) (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) : UniquenessAssumptions g K where
  vF1 := hP.e₁
  wF1 := hP.e₁
  transverse_nonzero := by
    rw [transverseMetric_apply, hP.q_orthogonal_e₁, mul_zero, mul_zero, add_zero, neg_ne_zero]
    exact hP.e₁_self_ne_zero
  pT_outer_zero := by rw [hP.pT_orthogonal_e₁, mul_zero]
  vF2 := pTransverse g K + hP.e₁
  wF2 := pTransverse g K - (g (pTransverse g K) (pTransverse g K) / g hP.e₁ hP.e₁) • hP.e₁
  transverse_zero := by
    have hqT : g K.q (pTransverse g K) = 0 := by
      rw [hSymm.eq, pTransverse_orthogonal_q g K hQ2]
    have he₁T : g hP.e₁ (pTransverse g K) = 0 := by rw [hSymm.eq, hP.pT_orthogonal_e₁]
    rw [transverseMetric_apply]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, smul_eq_mul, hqT,
      hP.q_orthogonal_e₁, hP.pT_orthogonal_e₁, he₁T]
    field_simp [hP.e₁_self_ne_zero]
    ring
  pT_outer_nonzero := by
    simp only [map_add, map_sub, map_smul, smul_eq_mul, hP.pT_orthogonal_e₁, mul_zero,
      add_zero, sub_zero]
    exact mul_ne_zero hTT hTT

section uniquenessAssumptions

variable {g : Bilin V} {K : DisKinematics V} (hP : SpectatorPair g K) (hSymm : g.IsSymm)
  (hQ2 : g K.q K.q ≠ 0) (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0)

@[simp] lemma SpectatorPair.uniquenessAssumptions_vF1 :
    (hP.uniquenessAssumptions hSymm hQ2 hTT).vF1 = hP.e₁ := (rfl)

@[simp] lemma SpectatorPair.uniquenessAssumptions_wF1 :
    (hP.uniquenessAssumptions hSymm hQ2 hTT).wF1 = hP.e₁ := (rfl)

@[simp] lemma SpectatorPair.uniquenessAssumptions_vF2 :
    (hP.uniquenessAssumptions hSymm hQ2 hTT).vF2 = pTransverse g K + hP.e₁ := (rfl)

@[simp] lemma SpectatorPair.uniquenessAssumptions_wF2 :
    (hP.uniquenessAssumptions hSymm hQ2 hTT).wF2 =
      pTransverse g K - (g (pTransverse g K) (pTransverse g K) / g hP.e₁ hP.e₁) • hP.e₁ :=
  (rfl)

end uniquenessAssumptions

section normalize

variable {g : Bilin V} {K : DisKinematics V}

/-- A `SpectatorPair` whose two directions have norms of the same sign, with `e₂` rescaled by
`√(e₁·e₁ / e₂·e₂)` so that both directions have the norm of `e₁`
(`SpectatorPair.normalize_self_eq`). -/
noncomputable def SpectatorPair.normalize (hP : SpectatorPair g K)
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
    have ht := Real.sqrt_ne_zero'.mpr (div_pos_iff.mpr (mul_pos_iff.mp hsign))
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_ne_zero ht (mul_ne_zero ht hP.e₂_self_ne_zero)

@[simp] lemma SpectatorPair.normalize_e₁ (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) : (hP.normalize hsign).e₁ = hP.e₁ := (rfl)

@[simp] lemma SpectatorPair.normalize_e₂ (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) :
    (hP.normalize hsign).e₂ = √(g hP.e₁ hP.e₁ / g hP.e₂ hP.e₂) • hP.e₂ := (rfl)

/-- The two directions of `SpectatorPair.normalize` have equal norms. -/
lemma SpectatorPair.normalize_self_eq (hP : SpectatorPair g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) :
    g (hP.normalize hsign).e₁ (hP.normalize hsign).e₁ =
      g (hP.normalize hsign).e₂ (hP.normalize hsign).e₂ := by
  simp only [normalize_e₁, normalize_e₂, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, Real.mul_self_sqrt (div_pos_iff.mpr (mul_pos_iff.mp hsign)).le,
    div_mul_cancel₀ _ hP.e₂_self_ne_zero]

/-- A `SpectatorPlane` whose two directions have norms of the same sign, with `e₂` rescaled as in
`SpectatorPair.normalize`; it is still a frame. -/
noncomputable def SpectatorPlane.normalize (hP : SpectatorPlane g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) : SpectatorPlane g K where
  toSpectatorPair := hP.toSpectatorPair.normalize hsign
  span v := by
    obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
    refine ⟨a, b, c₁, c₂ / √(g hP.e₁ hP.e₁ / g hP.e₂ hP.e₂), ?_⟩
    rw [SpectatorPair.normalize_e₁, SpectatorPair.normalize_e₂, smul_smul,
      div_mul_cancel₀ _ (Real.sqrt_ne_zero'.mpr (div_pos_iff.mpr (mul_pos_iff.mp hsign)))]

@[simp] lemma SpectatorPlane.toSpectatorPair_normalize (hP : SpectatorPlane g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂) :
    (hP.normalize hsign).toSpectatorPair = hP.toSpectatorPair.normalize hsign := (rfl)

end normalize

end Hadronic

end Tensors
end DIS
end Scattering
end QFT
end EpsilonEridani
