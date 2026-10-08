/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic

/-!
# The parity-odd part of the hadronic tensor

For a parity-violating probe (a `Z` or `W` exchange) the inclusive hadronic tensor of an
unpolarized target acquires the parity-odd structure `F₃ ε^{μναβ} p_α q_β / (2 p·q)`
(Devenish & Cooper-Sarkar, *Deep Inelastic Scattering* (2004), ch. 3; Halzen & Martin,
*Quarks and Leptons* (1984), ch. 8). Hermiticity makes that term the imaginary, antisymmetric
part of the tensor; in the real bilinear forms of `Tensors.Basic` it is represented by an
antisymmetric form. This module proves that, under a `SpectatorPlane`, the antisymmetric,
conserved, properly covariant tensors are exactly the multiples of a single non-zero structure
`A`, the role played by `ε(·, ·, p, q)`, which on an abstract real vector space is supplied as
data.

## Proper covariance

`IsLorentzCovariant` asks for invariance under *every* `g`-isometry fixing `p` and `q`. Such
isometries include reflections in spectator directions, and a reflection reverses the sign of
`ε(·, ·, p, q)`. Full covariance is therefore the statement of parity conservation, and once
every vector splits into `p_T`, `q` and spectator parts and every non-zero spectator direction
is non-null it kills every antisymmetric conserved tensor
(`ParityOddAssumptions.eq_zero_of_isLorentzCovariant`).
The parity-odd sector is governed instead by `IsProperLorentzCovariant` (from
`Tensors.Basic`): invariance under the stabilizer elements of determinant one.

## Main definitions

- `ParityOddAssumptions g K W`: `W` is alternating, conserved and properly covariant.
- `SpectatorPair g K`: two spectator directions `e₁`, `e₂`, non-null and orthogonal to each
  other and to `p_T` and `q`.
- `SpectatorPlane g K`: a `SpectatorPair` such that `{p_T, q, e₁, e₂}` spans `V`. This is the
  four-dimensionality input: the spectator subspace is a plane.
- `SpectatorSplitting g K`: every vector splits into `p_T`, `q` and spectator parts.
- `SpectatorPartners g K`: a `SpectatorSplitting` in which every non-zero spectator is non-null
  with a non-null spectator orthogonal to it.

## Main results

- `ParityOddAssumptions.apply_eq_mul_apply_e₁_e₂`: for a `SpectatorPair`, a parity-odd tensor
  on the span of `p_T`, `q`, `e₁`, `e₂` is determined by its single component `W e₁ e₂`.
- `ParityOddAssumptions.eq_div_smul`, `ParityOddAssumptions.existsUnique_eq_smul`: under a
  `SpectatorPlane`, any two parity-odd tensors are proportional, so a non-zero one `A` spans
  them all, with the unique coefficient `W e₁ e₂ / A e₁ e₂`.
- `sub_flip_eq_div_smul`, `existsUnique_sub_flip_eq_smul`: under a `SpectatorPlane`, `W - Wᵀ`
  (twice the antisymmetric part) of any conserved, properly covariant tensor is a unique
  multiple of a non-zero parity-odd `A`.
- `ParityOddAssumptions.apply_pTransverse_eq_zero`, `ParityOddAssumptions.apply_p_eq_zero`: a
  parity-odd tensor annihilates `p_T` and `p` under `SpectatorPartners`, that is, when every
  vector splits into `p_T`, `q` and spectator parts and every non-zero spectator is non-null
  with a non-null spectator orthogonal to it. The `_of_spectatorPlane` forms give the same
  under a `SpectatorPlane`.
- `ParityOddAssumptions.eq_zero_of_isLorentzCovariant`: under a `SpectatorSplitting` in which
  non-zero spectators are non-null, the parity-odd part vanishes under
  full covariance. No four-dimensionality enters.
- `Witness.parityOddAssumptions_aFour`, `Witness.aFour_ne_zero` and
  `Witness.existsUnique_eq_smul_aFour`: on Minkowski space `ℝ⁴` the contraction
  `ε(·, ·, p, q)` of the determinant is a non-zero parity-odd tensor, and every parity-odd
  tensor there is a unique multiple of it, so the parity-odd sector is exactly
  one-dimensional.
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
## The parity-odd hadronic tensor
-/

/-- Assumptions on the parity-odd part of a hadronic tensor: proper covariance, current
conservation, and antisymmetry in the form of `LinearMap.BilinForm.IsAlt`. Conservation in the
second slot follows from the first (`ParityOddAssumptions.conserved_right`). -/
structure ParityOddAssumptions (g : Bilin V) (K : DisKinematics V) (W : Bilin V) : Prop where
  /-- Invariance under every `g`-isometry of determinant one fixing `p` and `q`. -/
  proper_covariant : IsProperLorentzCovariant g K W
  /-- Current conservation in the first tensor slot. -/
  conserved_left : ∀ v : V, W K.q v = 0
  /-- The tensor is alternating, hence antisymmetric. -/
  isAlt : W.IsAlt

namespace ParityOddAssumptions

variable {g : Bilin V} {K : DisKinematics V} {W : Bilin V}

/-- A parity-odd tensor is conserved in the second slot as well. -/
lemma conserved_right (hW : ParityOddAssumptions g K W) (v : V) : W v K.q = 0 := by
  rw [← hW.isAlt.neg_eq, hW.conserved_left, neg_zero]

/-- The parity-odd assumptions are preserved by scalar multiples. -/
lemma smul (hW : ParityOddAssumptions g K W) (c : ℝ) : ParityOddAssumptions g K (c • W) where
  proper_covariant := hW.proper_covariant.smul c
  conserved_left v := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hW.conserved_left v, smul_zero]
  isAlt := hW.isAlt.smul c

end ParityOddAssumptions

/-- The zero tensor satisfies the parity-odd assumptions. -/
lemma parityOddAssumptions_zero (g : Bilin V) (K : DisKinematics V) :
    ParityOddAssumptions g K 0 where
  proper_covariant _ _ _ _ _ := rfl
  conserved_left _ := rfl
  isAlt := LinearMap.BilinForm.isAlt_zero

/-- **The antisymmetric part of a conserved covariant tensor is parity-odd.** For any hadronic
tensor conserved in both slots and properly covariant, `W - Wᵀ`, twice its antisymmetric
part, satisfies the parity-odd assumptions. -/
lemma parityOddAssumptions_sub_flip {g : Bilin V} {K : DisKinematics V} {W : Bilin V}
    (hcov : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) :
    ParityOddAssumptions g K (W - W.flip) where
  proper_covariant := hcov.sub hcov.flip
  conserved_left v := by simp [hleft v, hright v]
  isAlt v := by simp

/-- Two orthogonal non-null spectators `u` and `u'` give a kinematic stabilizer element of
determinant one reversing both: the composite of the reflections in `u` and in `u'`. -/
lemma exists_half_turn {g : Bilin V} {K : DisKinematics V} (hSymm : g.IsSymm)
    {u u' : V} (huq : g K.q u = 0) (huT : g (pTransverse g K) u = 0) (hu : g u u ≠ 0)
    (hu'q : g K.q u' = 0) (hu'T : g (pTransverse g K) u' = 0) (hu' : g u' u' ≠ 0)
    (huu' : g u u' = 0) :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f u = -u ∧ f u' = -u' := by
  have h₁ := reflect_isKinematicStabilizer g K hSymm _ hu
    (apply_p_eq_zero_of_spectator g K hSymm huq huT) (by rw [hSymm.eq, huq])
  have h₂ := reflect_isKinematicStabilizer g K hSymm _ hu'
    (apply_p_eq_zero_of_spectator g K hSymm hu'q hu'T) (by rw [hSymm.eq, hu'q])
  have hu'u : g u' u = 0 := by rw [hSymm.eq, huu']
  refine ⟨Bilin.reflect g u ∘ₗ Bilin.reflect g u',
    ⟨fun v w => by simp only [LinearMap.comp_apply, h₁.isometry _ _, h₂.isometry _ _],
      by rw [LinearMap.comp_apply, h₂.fixes_p, h₁.fixes_p],
      by rw [LinearMap.comp_apply, h₂.fixes_q, h₁.fixes_q]⟩, ?_, ?_, ?_⟩
  · by_cases hfin : Module.Finite ℝ V
    · rw [LinearMap.det_comp, Bilin.det_reflect g hu, Bilin.det_reflect g hu']
      norm_num
    · exact LinearMap.det_eq_one_of_not_module_finite hfin _
  · rw [LinearMap.comp_apply, Bilin.reflect_apply_of_orthogonal g _ _ hu'u,
      Bilin.reflect_apply_self g _ hu]
  · rw [LinearMap.comp_apply, Bilin.reflect_apply_self g _ hu', map_neg,
      Bilin.reflect_apply_of_orthogonal g _ _ huu']

/-!
## The spectator plane
-/

/-- Two spectator directions `e₁`, `e₂` for the kinematics, non-null and `g`-orthogonal to each
other and to `p_T` and `q`. They supply the half-turn of `exists_half_turn` that a parity-odd
tensor must respect; `SpectatorPlane` adds that they complete `p_T`, `q` to a frame of `V`. -/
@[ext]
structure SpectatorPair (g : Bilin V) (K : DisKinematics V) : Type where
  /-- The first spectator direction. -/
  e₁ : V
  /-- The second spectator direction. -/
  e₂ : V
  /-- `e₁` is orthogonal to the momentum transfer. -/
  e₁_orthogonal_q : g K.q e₁ = 0
  /-- `e₂` is orthogonal to the momentum transfer. -/
  e₂_orthogonal_q : g K.q e₂ = 0
  /-- `e₁` is orthogonal to the transverse hadron momentum. -/
  e₁_orthogonal_pT : g (pTransverse g K) e₁ = 0
  /-- `e₂` is orthogonal to the transverse hadron momentum. -/
  e₂_orthogonal_pT : g (pTransverse g K) e₂ = 0
  /-- The two spectator directions are orthogonal. -/
  e₁_orthogonal_e₂ : g e₁ e₂ = 0
  /-- `e₁` is not null. -/
  e₁_self_ne_zero : g e₁ e₁ ≠ 0
  /-- `e₂` is not null. -/
  e₂_self_ne_zero : g e₂ e₂ ≠ 0

/-- An adapted frame for the kinematics: a `SpectatorPair` `e₁`, `e₂` such that `p_T`, `q`,
`e₁`, `e₂` span `V`.

For `V` Minkowski space with `p` timelike and `q` spacelike the spectator subspace
`{p, q}^⊥` is a spacelike plane, and any orthogonal basis of it is such a frame. The frame
is the only place where four-dimensionality enters. -/
@[ext]
structure SpectatorPlane (g : Bilin V) (K : DisKinematics V) : Type extends SpectatorPair g K where
  /-- The frame spans `V`. -/
  span : ∀ v : V, ∃ a b c₁ c₂ : ℝ, v = a • pTransverse g K + b • K.q + c₁ • e₁ + c₂ • e₂

/-- Every vector splits into a `p_T` part, a `q` part and a spectator part orthogonal to both.
This is the `span` field of `SpectatorAssumptions`, without its definiteness and transitivity
inputs. -/
structure SpectatorSplitting (g : Bilin V) (K : DisKinematics V) : Prop where
  /-- Every vector splits into a transverse-hadron part, a longitudinal `q` part, and a
  spectator part orthogonal to both. -/
  span : ∀ v : V, ∃ (a b : ℝ) (u : V), g K.q u = 0 ∧ g (pTransverse g K) u = 0 ∧
    v = a • pTransverse g K + b • K.q + u

/-- A `SpectatorSplitting` in which every non-zero spectator `u` is non-null and has a non-null
spectator `u'` orthogonal to it, so that `exists_half_turn` reverses `u`. A definite spectator
subspace of any dimension at least two qualifies. -/
structure SpectatorPartners (g : Bilin V) (K : DisKinematics V) : Prop
    extends SpectatorSplitting g K where
  /-- Every non-zero spectator is non-null and has a non-null spectator orthogonal to it. -/
  partner : ∀ u : V, g K.q u = 0 → g (pTransverse g K) u = 0 → u ≠ 0 →
    g u u ≠ 0 ∧ ∃ u' : V, g K.q u' = 0 ∧ g (pTransverse g K) u' = 0 ∧ g u u' = 0 ∧
      g u' u' ≠ 0

/-- The adapted frame of a `SpectatorPlane` splits every vector: the spectator part of
`a • p_T + b • q + c₁ • e₁ + c₂ • e₂` is `c₁ • e₁ + c₂ • e₂`. -/
lemma SpectatorPlane.spectatorSplitting {g : Bilin V} {K : DisKinematics V}
    (hP : SpectatorPlane g K) : SpectatorSplitting g K where
  span v := by
    obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
    refine ⟨a, b, c₁ • hP.e₁ + c₂ • hP.e₂, ?_, ?_, add_assoc _ _ _⟩
    · simp only [map_add, map_smul, hP.e₁_orthogonal_q, hP.e₂_orthogonal_q, smul_zero,
        add_zero]
    · simp only [map_add, map_smul, hP.e₁_orthogonal_pT, hP.e₂_orthogonal_pT, smul_zero,
        add_zero]

namespace ParityOddAssumptions

variable {g : Bilin V} {K : DisKinematics V} {W : Bilin V}

/-- **A parity-odd tensor has a single component.** On the span of `p_T`, `q` and a
`SpectatorPair` `e₁`, `e₂`, `W` is `W e₁ e₂` times the `2 × 2` determinant of the spectator
coordinates of its arguments. -/
lemma apply_eq_mul_apply_e₁_e₂ (hSymm : g.IsSymm) (hP : SpectatorPair g K)
    (hW : ParityOddAssumptions g K W) (a b c₁ c₂ a' b' d₁ d₂ : ℝ) :
    W (a • pTransverse g K + b • K.q + c₁ • hP.e₁ + c₂ • hP.e₂)
        (a' • pTransverse g K + b' • K.q + d₁ • hP.e₁ + d₂ • hP.e₂) =
      (c₁ * d₂ - c₂ * d₁) * W hP.e₁ hP.e₂ := by
  obtain ⟨f, hf, hdet, hf₁, hf₂⟩ := exists_half_turn hSymm hP.e₁_orthogonal_q
    hP.e₁_orthogonal_pT hP.e₁_self_ne_zero hP.e₂_orthogonal_q hP.e₂_orthogonal_pT
    hP.e₂_self_ne_zero hP.e₁_orthogonal_e₂
  have hfW := hW.proper_covariant f hf hdet
  have hfT := stabilizer_fixes_pTransverse g K hf
  have h₁ := Bilin.apply_eq_zero_of_apply_eq_self_of_apply_eq_neg hfW hfT hf₁
  have h₂ := Bilin.apply_eq_zero_of_apply_eq_self_of_apply_eq_neg hfW hfT hf₂
  have h₁' : W hP.e₁ (pTransverse g K) = 0 := by rw [← hW.isAlt.neg_eq, h₁, neg_zero]
  have h₂' : W hP.e₂ (pTransverse g K) = 0 := by rw [← hW.isAlt.neg_eq, h₂, neg_zero]
  have h₂₁ : W hP.e₂ hP.e₁ = -W hP.e₁ hP.e₂ := (hW.isAlt.neg_eq _ _).symm
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hW.conserved_left, hW.conserved_right, hW.isAlt.self_eq_zero, h₁, h₂, h₁', h₂', h₂₁]
  ring

/-- **A parity-odd tensor annihilates the transverse hadron momentum `p_T`.** Under
`SpectatorPartners`, every vector splits into a `p_T` part, a `q` part and a spectator part
`u`, and the half-turn in the plane of `u` and its partner reverses `u` and fixes `p_T`.
No four-dimensionality enters: a definite spectator subspace of any dimension at least two
qualifies. -/
lemma apply_pTransverse_eq_zero (hSymm : g.IsSymm)
    (hS : SpectatorPartners g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W (pTransverse g K) v = 0 := by
  obtain ⟨a, b, u, huq, huT, rfl⟩ := hS.span v
  have hTu : W (pTransverse g K) u = 0 := by
    by_cases hu : u = 0
    · simp [hu]
    obtain ⟨huu, u', hu'q, hu'T, huu', hu'u'⟩ := hS.partner u huq huT hu
    obtain ⟨f, hf, hdet, hfu, -⟩ := exists_half_turn hSymm huq huT huu hu'q hu'T hu'u' huu'
    exact Bilin.apply_eq_zero_of_apply_eq_self_of_apply_eq_neg (hW.proper_covariant f hf hdet)
      (stabilizer_fixes_pTransverse g K hf) hfu
  simp only [map_add, map_smul, smul_eq_mul, hW.isAlt.self_eq_zero, hW.conserved_right, hTu,
    mul_zero, add_zero]

/-- By conservation, a parity-odd tensor does not distinguish `p` from `p_T`. -/
lemma apply_p_eq_apply_pTransverse (hW : ParityOddAssumptions g K W) (v : V) :
    W K.p v = W (pTransverse g K) v := by
  have hp : K.p = pTransverse g K + (g K.p K.q / g K.q K.q) • K.q := by
    rw [pTransverse, sub_add_cancel]
  rw [hp, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hW.conserved_left,
    smul_zero, add_zero]

/-- A parity-odd tensor annihilates the hadron momentum `p`, under the hypotheses of
`apply_pTransverse_eq_zero`. -/
lemma apply_p_eq_zero (hSymm : g.IsSymm)
    (hS : SpectatorPartners g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W K.p v = 0 := by
  rw [hW.apply_p_eq_apply_pTransverse, hW.apply_pTransverse_eq_zero hSymm hS]

/-- A parity-odd tensor annihilates `p_T` in the second slot as well, under the hypotheses of
`apply_pTransverse_eq_zero`. -/
lemma apply_pTransverse_eq_zero_right (hSymm : g.IsSymm)
    (hS : SpectatorPartners g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W v (pTransverse g K) = 0 := by
  rw [← hW.isAlt.neg_eq, hW.apply_pTransverse_eq_zero hSymm hS, neg_zero]

/-- A parity-odd tensor annihilates `p` in the second slot as well, under the hypotheses of
`apply_pTransverse_eq_zero`. -/
lemma apply_p_eq_zero_right (hSymm : g.IsSymm)
    (hS : SpectatorPartners g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W v K.p = 0 := by
  rw [← hW.isAlt.neg_eq, hW.apply_p_eq_zero hSymm hS, neg_zero]

/-- Under a `SpectatorPlane`, a parity-odd tensor annihilates `p_T`: its `p_T` row has no
spectator coordinates in the adapted frame. -/
lemma apply_pTransverse_eq_zero_of_spectatorPlane (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W (pTransverse g K) v = 0 := by
  obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
  simpa using hW.apply_eq_mul_apply_e₁_e₂ hSymm hP.toSpectatorPair 1 0 0 0 a b c₁ c₂

/-- Under a `SpectatorPlane`, a parity-odd tensor annihilates the hadron momentum `p`. -/
lemma apply_p_eq_zero_of_spectatorPlane (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W K.p v = 0 := by
  rw [hW.apply_p_eq_apply_pTransverse, hW.apply_pTransverse_eq_zero_of_spectatorPlane hSymm hP]

/-- Under a `SpectatorPlane`, a parity-odd tensor annihilates `p_T` in the second slot. -/
lemma apply_pTransverse_eq_zero_right_of_spectatorPlane (hSymm : g.IsSymm)
    (hP : SpectatorPlane g K) (hW : ParityOddAssumptions g K W) (v : V) :
    W v (pTransverse g K) = 0 := by
  rw [← hW.isAlt.neg_eq, hW.apply_pTransverse_eq_zero_of_spectatorPlane hSymm hP, neg_zero]

/-- Under a `SpectatorPlane`, a parity-odd tensor annihilates `p` in the second slot. -/
lemma apply_p_eq_zero_right_of_spectatorPlane (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W v K.p = 0 := by
  rw [← hW.isAlt.neg_eq, hW.apply_p_eq_zero_of_spectatorPlane hSymm hP, neg_zero]

/-- Two parity-odd tensors agreeing on the spectator pair `(e₁, e₂)` are equal. -/
lemma eq_of_apply_e₁_e₂_eq (hSymm : g.IsSymm) (hP : SpectatorPlane g K) {W' : Bilin V}
    (hW : ParityOddAssumptions g K W) (hW' : ParityOddAssumptions g K W')
    (h : W hP.e₁ hP.e₂ = W' hP.e₁ hP.e₂) : W = W' := by
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
  obtain ⟨a', b', d₁, d₂, rfl⟩ := hP.span w
  rw [hW.apply_eq_mul_apply_e₁_e₂ hSymm hP.toSpectatorPair,
    hW'.apply_eq_mul_apply_e₁_e₂ hSymm hP.toSpectatorPair, h]

/-- A parity-odd tensor vanishes exactly when its spectator component `W e₁ e₂` does. -/
lemma eq_zero_iff (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) : W = 0 ↔ W hP.e₁ hP.e₂ = 0 :=
  ⟨fun h => by simp [h],
    fun h => hW.eq_of_apply_e₁_e₂_eq hSymm hP (parityOddAssumptions_zero g K) h⟩

/-- **The parity-odd sector is at most one-dimensional.** Under a `SpectatorPlane`, every
parity-odd tensor is the multiple `W e₁ e₂ / A e₁ e₂` of a fixed non-zero one `A`. -/
theorem eq_div_smul (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) {A : Bilin V} (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) : W = (W hP.e₁ hP.e₂ / A hP.e₁ hP.e₂) • A := by
  have hAe : A hP.e₁ hP.e₂ ≠ 0 := fun h => hA0 ((hA.eq_zero_iff hSymm hP).mpr h)
  refine hW.eq_of_apply_e₁_e₂_eq hSymm hP (hA.smul _) ?_
  simp only [LinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- Under a `SpectatorPlane`, every parity-odd tensor is a multiple of a fixed non-zero one
`A`, with a unique coefficient. The coefficient is relative to the chosen normalisation of
`A`: for `W` the parity-odd part of the hadronic tensor and `A = ε(·, ·, p, q)` it is the
literature's `F₃ / (2 p·q)`, up to the sign convention of `ε` and the factor `i` dropped in
the real model. -/
theorem existsUnique_eq_smul (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) {A : Bilin V} (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) : ∃! c : ℝ, W = c • A := by
  have hAe : A hP.e₁ hP.e₂ ≠ 0 := fun h => hA0 ((hA.eq_zero_iff hSymm hP).mpr h)
  refine ⟨_, hW.eq_div_smul hSymm hP hA hA0, ?_⟩
  rintro c rfl
  simp only [LinearMap.smul_apply, smul_eq_mul]
  field_simp

/-- **Parity conservation removes the parity-odd sector.** Under a `SpectatorSplitting` in
which every non-zero spectator is non-null, a parity-odd tensor
that is covariant under every stabilizer element, reflections included, vanishes. No
dimension hypothesis is needed. -/
theorem eq_zero_of_isLorentzCovariant (hSymm : g.IsSymm) (hS : SpectatorSplitting g K)
    (hnull : ∀ u : V, g K.q u = 0 → g (pTransverse g K) u = 0 → u ≠ 0 → g u u ≠ 0)
    (hW : ParityOddAssumptions g K W) (hcov : IsLorentzCovariant g K W) : W = 0 := by
  -- The reflection in a spectator `u` kills every component of `W` between `u` and `u^⊥`.
  have hperp : ∀ u v : V, g K.q u = 0 → g (pTransverse g K) u = 0 → g u v = 0 →
      W u v = 0 := fun u _ huq huT huv =>
    covariant_offDiagonal_zero_of_spectator g K W hSymm hcov (hnull u huq huT) huq huT huv
  -- Two spectators: split `u'` along `u` and its orthogonal complement.
  have hspec : ∀ u u' : V, g K.q u = 0 → g (pTransverse g K) u = 0 → W u u' = 0 := by
    intro u u' huq huT
    by_cases hu : u = 0
    · simp [hu]
    have huu := hnull u huq huT hu
    have h := hperp u (u' - (g u u' / g u u) • u) huq huT (by
      rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ huu, sub_self])
    rwa [map_sub, map_smul, hW.isAlt.self_eq_zero, smul_zero, sub_zero] at h
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨a, b, u, huq, huT, rfl⟩ := hS.span v
  obtain ⟨a', b', u', hu'q, hu'T, rfl⟩ := hS.span w
  have hTu' : W (pTransverse g K) u' = 0 := by
    rw [← hW.isAlt.neg_eq, hspec u' _ hu'q hu'T, neg_zero]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hW.conserved_left, hW.conserved_right, hW.isAlt.self_eq_zero, hTu', hspec u _ huq huT,
    LinearMap.zero_apply]

end ParityOddAssumptions

/-- Under a `SpectatorPlane`, for any tensor `W` conserved in both slots and properly
covariant, and any non-zero parity-odd `A`, `W - Wᵀ` is the multiple
`(W - Wᵀ) e₁ e₂ / A e₁ e₂` of `A`. -/
theorem sub_flip_eq_div_smul {g : Bilin V} {K : DisKinematics V} {W A : Bilin V}
    (hSymm : g.IsSymm) (hP : SpectatorPlane g K) (hcov : IsProperLorentzCovariant g K W)
    (hleft : ∀ v : V, W K.q v = 0) (hright : ∀ v : V, W v K.q = 0)
    (hA : ParityOddAssumptions g K A) (hA0 : A ≠ 0) :
    W - W.flip = ((W - W.flip) hP.e₁ hP.e₂ / A hP.e₁ hP.e₂) • A :=
  (parityOddAssumptions_sub_flip hcov hleft hright).eq_div_smul hSymm hP hA hA0

/-- **The antisymmetric part of the hadronic tensor is a single multiple of the parity-odd
structure.** Under a `SpectatorPlane`, for any tensor `W` conserved in both slots and properly
covariant, and any non-zero parity-odd `A`, there is a unique `c` with `W - Wᵀ = c • A`;
`W - Wᵀ` is twice the antisymmetric part of `W`. -/
theorem existsUnique_sub_flip_eq_smul {g : Bilin V} {K : DisKinematics V} {W A : Bilin V}
    (hSymm : g.IsSymm) (hP : SpectatorPlane g K) (hcov : IsProperLorentzCovariant g K W)
    (hleft : ∀ v : V, W K.q v = 0) (hright : ∀ v : V, W v K.q = 0)
    (hA : ParityOddAssumptions g K A) (hA0 : A ≠ 0) :
    ∃! c : ℝ, W - W.flip = c • A :=
  (parityOddAssumptions_sub_flip hcov hleft hright).existsUnique_eq_smul hSymm hP hA hA0

/-!
## A four-dimensional witness

On Minkowski space `ℝ⁴` with `p = (1, 0, 0, 0)` and `q = (0, 0, 0, 1)`, the contraction
`ε(·, ·, p, q)` of the determinant is a non-zero parity-odd tensor, and the two remaining
coordinate directions form a `SpectatorPlane`. So the hypotheses of
`ParityOddAssumptions.existsUnique_eq_smul` are satisfiable, and the parity-odd sector is exactly
one-dimensional on these kinematics (`existsUnique_eq_smul_aFour`). The same tensor is not
`IsLorentzCovariant`, so proper covariance is strictly weaker than full covariance.
-/

namespace Witness

/-- The `+---` Minkowski form on `ℝ⁴`: `g v w = v₀w₀ - v₁w₁ - v₂w₂ - v₃w₃`. -/
def gFour : Bilin (Fin 4 → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal ![1, -1, -1, -1])

@[simp] lemma gFour_apply (v w : Fin 4 → ℝ) :
    gFour v w = v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := by
  simp [gFour, Matrix.toBilin'_apply, Fin.sum_univ_four, Matrix.diagonal]
  ring

/-- `gFour` is symmetric. -/
lemma gFour_isSymm : gFour.IsSymm :=
  Matrix.isSymm_toBilin'_iff_isSymm.mpr (Matrix.isSymm_diagonal _)

/-- Witness kinematics on `ℝ⁴`: timelike `p = (1, 0, 0, 0)` and spacelike
`q = (0, 0, 0, 1)`, with `Q² = 1`. Here `p` and `q` are `g`-orthogonal, so `p_T = p` and
`p·q = 0`: the witness tests the linear-algebra hypotheses only, not the physical
`1 / (2 p·q)` normalisation of `F₃` (nor `ν` or `x_Bj`, which are undefined here). The lepton
momenta are placeholders. -/
def kFour : DisKinematics (Fin 4 → ℝ) where
  p := ![1, 0, 0, 0]
  pPrime := 0
  k := ![0, 0, 0, 1]
  kPrime := 0
  q := ![0, 0, 0, 1]
  hq := by simp

@[simp] lemma kFour_p : kFour.p = ![1, 0, 0, 0] := (rfl)

@[simp] lemma kFour_q : kFour.q = ![0, 0, 0, 1] := (rfl)

/-- The transverse hadron momentum of the witness kinematics is `p` itself. -/
@[simp] lemma pTransverse_kFour : pTransverse gFour kFour = ![1, 0, 0, 0] := by
  simp [pTransverse]

/-- The parity-odd structure `ε(v, w, p, q)` on the witness kinematics, with `ε` the
determinant of `ℝ⁴`. -/
noncomputable def aFour : Bilin (Fin 4 → ℝ) :=
  LinearMap.mk₂ ℝ (fun v w => (Pi.basisFun ℝ (Fin 4)).det ![v, w, kFour.p, kFour.q])
    (fun _ _ _ => AlternatingMap.map_vecCons_add _ _ _ _)
    (fun _ _ _ => AlternatingMap.map_vecCons_smul _ _ _ _)
    (fun v _ _ => ((Pi.basisFun ℝ (Fin 4)).det.curryLeft v).map_vecCons_add _ _ _)
    (fun _ v _ => ((Pi.basisFun ℝ (Fin 4)).det.curryLeft v).map_vecCons_smul _ _ _)

/-- `aFour` as the determinant of its two arguments together with `p` and `q`. -/
lemma aFour_eq_det (v w : Fin 4 → ℝ) :
    aFour v w = (Pi.basisFun ℝ (Fin 4)).det ![v, w, kFour.p, kFour.q] :=
  LinearMap.mk₂_apply ..

/-- The closed form of `aFour`: with `p` and `q` along the `0` and `3` axes, `ε(v, w, p, q)` is
the `2 × 2` determinant of the spectator components `1`, `2` of `v` and `w`. -/
@[simp] lemma aFour_apply (v w : Fin 4 → ℝ) : aFour v w = v 1 * w 2 - v 2 * w 1 := by
  rw [aFour_eq_det, Module.Basis.det_apply]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Module.Basis.toMatrix_apply,
    Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc]
  ring

/-- **`ParityOddAssumptions` is satisfiable.** The witness tensor `aFour` is alternating,
conserved and properly covariant. -/
lemma parityOddAssumptions_aFour : ParityOddAssumptions gFour kFour aFour where
  properCovariant f hf hdet v w := by
    have hp : f ![1, 0, 0, 0] = ![1, 0, 0, 0] := hf.fixes_p
    have hq : f ![0, 0, 0, 1] = ![0, 0, 0, 1] := hf.fixes_q
    have h : ![f v, f w, ![1, 0, 0, 0], ![0, 0, 0, 1]] =
        f ∘ ![v, w, ![1, 0, 0, 0], ![0, 0, 0, 1]] := by
      ext1 i
      fin_cases i <;> simp [hp, hq]
    simp only [aFour_eq_det, kFour_p, kFour_q, h, Module.Basis.det_comp, hdet, one_mul]
  conserved_left v := by
    rw [aFour_eq_det]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 3) rfl (by decide)
  isAlt v := by
    rw [aFour_eq_det]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)

/-- The spectator plane of the witness kinematics, spanned by the coordinate directions
`e₁ = (0, 1, 0, 0)` and `e₂ = (0, 0, 1, 0)`. -/
def spectatorPlaneFour : SpectatorPlane gFour kFour where
  e₁ := ![0, 1, 0, 0]
  e₂ := ![0, 0, 1, 0]
  e₁_orthogonal_q := by simp
  e₂_orthogonal_q := by simp
  e₁_orthogonal_pT := by simp
  e₂_orthogonal_pT := by simp
  e₁_orthogonal_e₂ := by simp
  e₁_self_ne_zero := by simp
  e₂_self_ne_zero := by simp
  span v := ⟨v 0, v 3, v 1, v 2, by ext i; fin_cases i <;> simp⟩

@[simp] lemma spectatorPlaneFour_e₁ : spectatorPlaneFour.e₁ = ![0, 1, 0, 0] := (rfl)

@[simp] lemma spectatorPlaneFour_e₂ : spectatorPlaneFour.e₂ = ![0, 0, 1, 0] := (rfl)

/-- The spectator component of the witness parity-odd tensor: `aFour e₁ e₂ = 1` for the
spectator directions `e₁ = (0, 1, 0, 0)` and `e₂ = (0, 0, 1, 0)` of `spectatorPlaneFour`. -/
lemma aFour_e₁_e₂ : aFour spectatorPlaneFour.e₁ spectatorPlaneFour.e₂ = 1 := by
  simp

/-- The witness parity-odd tensor is non-zero. -/
lemma aFour_ne_zero : aFour ≠ 0 := fun h => by
  simpa [h] using aFour_e₁_e₂

/-- **The parity-odd sector of the witness is one-dimensional.** Every parity-odd tensor on
the witness kinematics is a unique multiple of `aFour`. -/
theorem existsUnique_eq_smul_aFour {W : Bilin (Fin 4 → ℝ)}
    (hW : ParityOddAssumptions gFour kFour W) : ∃! c : ℝ, W = c • aFour :=
  hW.existsUnique_eq_smul gFour_isSymm spectatorPlaneFour parityOddAssumptions_aFour
    aFour_ne_zero

/-- On the witness kinematics every non-zero spectator is non-null: the spectator subspace is
the spacelike plane of the coordinates `1` and `2`. This follows from `spectatorPlaneFour`. -/
lemma spectatorPlaneFour_self_ne_zero_of_spectator {u : Fin 4 → ℝ}
    (hq : gFour kFour.q u = 0) (hT : gFour (pTransverse gFour kFour) u = 0)
    (hu : u ≠ 0) : gFour u u ≠ 0 := by
  obtain ⟨a, b, c₁, c₂, rfl⟩ := spectatorPlaneFour.span u
  simp only [gFour_apply, kFour_q, pTransverse_kFour, spectatorPlaneFour_e₁,
    spectatorPlaneFour_e₂] at hq hT ⊢
  have h₀ : a = 0 := by simpa using hT
  have h₃ : b = 0 := by simpa using hq
  have h₁₂ : c₁ ≠ 0 ∨ c₂ ≠ 0 := by
    intro h
    apply hu
    simp [h₀, h₃, h.1, h.2]
  rcases h₁₂ with h | h <;> nlinarith [mul_self_pos.mpr h, mul_self_nonneg (c₁),
    mul_self_nonneg (c₂)]

/-- **Proper covariance is strictly weaker than full covariance.** The properly covariant,
non-zero tensor `aFour` is not `IsLorentzCovariant`. -/
lemma not_isLorentzCovariant_aFour : ¬ IsLorentzCovariant gFour kFour aFour := fun h =>
  aFour_ne_zero (parityOddAssumptions_aFour.eq_zero_of_isLorentzCovariant gFour_isSymm
    spectatorPlaneFour.spectatorSplitting
    (fun u hq hT hu => spectatorPlaneFour_self_ne_zero_of_spectator hq hT hu) h)

end Witness

end Hadronic

end Tensors
end DIS
end Scattering
end QFT
end EpsilonEridani
