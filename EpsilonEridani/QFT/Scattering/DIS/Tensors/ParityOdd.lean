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
antisymmetric form. This module proves that the antisymmetric, conserved, covariant tensors are
exactly the multiples of a single structure `A`, the role played by `ε(·, ·, p, q)`, which on an
abstract real vector space is supplied as data.

## Proper covariance

`IsLorentzCovariant` asks for invariance under *every* `g`-isometry fixing `p` and `q`. Such
isometries include reflections in spectator directions, and a reflection reverses the sign of
`ε(·, ·, p, q)`. Full covariance is therefore the statement of parity conservation, and it
kills every antisymmetric conserved tensor (`ParityOddAssumptions.eq_zero_of_isLorentzCovariant`).
The parity-odd sector is governed instead by `IsProperLorentzCovariant`: invariance under the
stabilizer elements of determinant one.

## Main definitions

- `IsProperLorentzCovariant g K W`: invariance of `W` under every kinematic stabilizer element
  of determinant one.
- `ParityOddAssumptions g K W`: `W` is alternating, conserved and properly covariant.
- `SpectatorPlane g K`: an adapted frame `{p_T, q, e₁, e₂}` of `V` in which the spectator
  directions `e₁`, `e₂` are non-null and orthogonal to each other and to `p_T` and `q`. This is
  the four-dimensionality input: the spectator subspace is a plane.

## Main results

- `ParityOddAssumptions.apply_eq_mul_apply_e₁_e₂`: under a `SpectatorPlane`, a parity-odd
  tensor is determined by its single component `W e₁ e₂`.
- `ParityOddAssumptions.existsUnique_eq_smul`: any two parity-odd tensors are proportional, so
  a non-zero one `A` spans them all, with a unique coefficient.
- `existsUnique_sub_flip_eq_smul`: the antisymmetric part `W - Wᵀ` of any conserved, properly
  covariant tensor is a unique multiple of `A`.
- `ParityOddAssumptions.eq_zero_of_isLorentzCovariant`: under full covariance the parity-odd
  part vanishes.
- `Witness.parityOddAssumptions_aFour` and `Witness.aFour_ne_zero`: on Minkowski space `ℝ⁴`
  the contraction `ε(·, ·, p, q)` of the determinant is a non-zero parity-odd tensor, so the
  parity-odd sector there is exactly one-dimensional.
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
## Proper covariance
-/

/-- Proper Lorentz covariance of a hadronic tensor: `W` is invariant under every `g`-isometry
of determinant one fixing `p` and `q`. This is the covariance of a parity-violating
interaction, which need not respect the reflections allowed by `IsLorentzCovariant`. -/
def IsProperLorentzCovariant (g : Bilin V) (K : DisKinematics V) (W : Bilin V) : Prop :=
  ∀ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f → LinearMap.det f = 1 →
    ∀ v w : V, W (f v) (f w) = W v w

/-- The defining property of `IsProperLorentzCovariant`. -/
lemma isProperLorentzCovariant_iff {g : Bilin V} {K : DisKinematics V} {W : Bilin V} :
    IsProperLorentzCovariant g K W ↔ ∀ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f →
      LinearMap.det f = 1 → ∀ v w : V, W (f v) (f w) = W v w :=
  Iff.rfl

/-- Full covariance implies proper covariance. -/
lemma IsLorentzCovariant.isProperLorentzCovariant {g : Bilin V} {K : DisKinematics V}
    {W : Bilin V} (hW : IsLorentzCovariant g K W) : IsProperLorentzCovariant g K W :=
  fun f hf _ => hW f hf

/-- Proper covariance is preserved by scalar multiples. -/
lemma IsProperLorentzCovariant.smul {g : Bilin V} {K : DisKinematics V} {W : Bilin V}
    (hW : IsProperLorentzCovariant g K W) (c : ℝ) : IsProperLorentzCovariant g K (c • W) := by
  intro f hf hdet v w
  simp only [LinearMap.smul_apply, hW f hf hdet v w]

/-- Proper covariance is preserved by sums. -/
lemma IsProperLorentzCovariant.add {g : Bilin V} {K : DisKinematics V} {W W' : Bilin V}
    (hW : IsProperLorentzCovariant g K W) (hW' : IsProperLorentzCovariant g K W') :
    IsProperLorentzCovariant g K (W + W') := by
  intro f hf hdet v w
  simp only [LinearMap.add_apply, hW f hf hdet v w, hW' f hf hdet v w]

/-- Proper covariance is preserved by differences. -/
lemma IsProperLorentzCovariant.sub {g : Bilin V} {K : DisKinematics V} {W W' : Bilin V}
    (hW : IsProperLorentzCovariant g K W) (hW' : IsProperLorentzCovariant g K W') :
    IsProperLorentzCovariant g K (W - W') := by
  intro f hf hdet v w
  simp only [LinearMap.sub_apply, hW f hf hdet v w, hW' f hf hdet v w]

/-- Proper covariance is preserved by exchanging the two slots. -/
lemma IsProperLorentzCovariant.flip {g : Bilin V} {K : DisKinematics V} {W : Bilin V}
    (hW : IsProperLorentzCovariant g K W) : IsProperLorentzCovariant g K W.flip := by
  intro f hf hdet v w
  exact hW f hf hdet w v

/-!
## The parity-odd hadronic tensor
-/

/-- Assumptions on the parity-odd part of a hadronic tensor: proper covariance, current
conservation, and antisymmetry in the form of `LinearMap.BilinForm.IsAlt`. Conservation in the
second slot follows from the first (`ParityOddAssumptions.conserved_right`). -/
structure ParityOddAssumptions (g : Bilin V) (K : DisKinematics V) (W : Bilin V) : Prop where
  /-- Invariance under every `g`-isometry of determinant one fixing `p` and `q`. -/
  covariant : IsProperLorentzCovariant g K W
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
  covariant := hW.covariant.smul c
  conserved_left v := by
    rw [LinearMap.smul_apply, LinearMap.smul_apply, hW.conserved_left v, smul_zero]
  isAlt := hW.isAlt.smul c

end ParityOddAssumptions

/-- The zero tensor satisfies the parity-odd assumptions. -/
lemma parityOddAssumptions_zero (g : Bilin V) (K : DisKinematics V) :
    ParityOddAssumptions g K 0 where
  covariant _ _ _ _ _ := rfl
  conserved_left _ := rfl
  isAlt := LinearMap.BilinForm.isAlt_zero

/-- **The antisymmetric part of a conserved covariant tensor is parity-odd.** For any hadronic
tensor conserved in both slots and properly covariant, `W - Wᵀ` satisfies the parity-odd
assumptions. -/
lemma parityOddAssumptions_sub_flip {g : Bilin V} {K : DisKinematics V} {W : Bilin V}
    (hcov : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) :
    ParityOddAssumptions g K (W - W.flip) where
  covariant := hcov.sub hcov.flip
  conserved_left v := by simp [hleft v, hright v]
  isAlt v := by simp

/-!
## The spectator plane
-/

/-- An adapted frame for the kinematics: two spectator directions `e₁`, `e₂`, non-null and
`g`-orthogonal to each other and to `p_T` and `q`, such that `p_T`, `q`, `e₁`, `e₂` span `V`.

For `V` Minkowski space with `p` timelike and `q` spacelike the spectator subspace
`{p, q}^⊥` is a spacelike plane, and any orthogonal basis of it is such a frame. The frame
is the only place where four-dimensionality enters. -/
structure SpectatorPlane (g : Bilin V) (K : DisKinematics V) : Type where
  /-- The first spectator direction. -/
  e₁ : V
  /-- The second spectator direction. -/
  e₂ : V
  /-- `e₁` is orthogonal to the momentum transfer. -/
  q_e₁ : g K.q e₁ = 0
  /-- `e₂` is orthogonal to the momentum transfer. -/
  q_e₂ : g K.q e₂ = 0
  /-- `e₁` is orthogonal to the transverse hadron momentum. -/
  pT_e₁ : g (pTransverse g K) e₁ = 0
  /-- `e₂` is orthogonal to the transverse hadron momentum. -/
  pT_e₂ : g (pTransverse g K) e₂ = 0
  /-- The two spectator directions are orthogonal. -/
  e₁_e₂ : g e₁ e₂ = 0
  /-- `e₁` is not null. -/
  e₁_e₁ : g e₁ e₁ ≠ 0
  /-- `e₂` is not null. -/
  e₂_e₂ : g e₂ e₂ ≠ 0
  /-- The frame spans `V`. -/
  span : ∀ v : V, ∃ a b c₁ c₂ : ℝ, v = a • pTransverse g K + b • K.q + c₁ • e₁ + c₂ • e₂

namespace SpectatorPlane

variable {g : Bilin V} {K : DisKinematics V}

/-- There is a kinematic stabilizer element of determinant one reversing both spectator
directions `e₁` and `e₂`. -/
private lemma exists_halfTurn (hSymm : g.IsSymm) (hP : SpectatorPlane g K) :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f hP.e₁ = -hP.e₁ ∧ f hP.e₂ = -hP.e₂ := by
  have h₁ := reflect_isKinematicStabilizer g K hSymm _ hP.e₁_e₁
    (apply_p_eq_zero_of_spectator g K hSymm hP.q_e₁ hP.pT_e₁) (by rw [hSymm.eq, hP.q_e₁])
  have h₂ := reflect_isKinematicStabilizer g K hSymm _ hP.e₂_e₂
    (apply_p_eq_zero_of_spectator g K hSymm hP.q_e₂ hP.pT_e₂) (by rw [hSymm.eq, hP.q_e₂])
  have h₂₁ : g hP.e₂ hP.e₁ = 0 := by rw [hSymm.eq, hP.e₁_e₂]
  refine ⟨Bilin.reflect g hP.e₁ ∘ₗ Bilin.reflect g hP.e₂,
    ⟨fun v w => by simp only [LinearMap.comp_apply, h₁.isometry _ _, h₂.isometry _ _],
      by rw [LinearMap.comp_apply, h₂.fixes_p, h₁.fixes_p],
      by rw [LinearMap.comp_apply, h₂.fixes_q, h₁.fixes_q]⟩, ?_, ?_, ?_⟩
  · by_cases hfin : Module.Finite ℝ V
    · rw [LinearMap.det_comp, Bilin.det_reflect g hP.e₁_e₁, Bilin.det_reflect g hP.e₂_e₂]
      norm_num
    · exact LinearMap.det_eq_one_of_not_module_finite hfin _
  · rw [LinearMap.comp_apply, Bilin.reflect_apply_of_orthogonal g _ _ h₂₁,
      Bilin.reflect_apply_self g _ hP.e₁_e₁]
  · rw [LinearMap.comp_apply, Bilin.reflect_apply_self g _ hP.e₂_e₂, map_neg,
      Bilin.reflect_apply_of_orthogonal g _ _ hP.e₁_e₂]

end SpectatorPlane

namespace ParityOddAssumptions

variable {g : Bilin V} {K : DisKinematics V} {W : Bilin V}

/-- A parity-odd tensor has no component mixing `p_T` with the spectator direction `e₁`. -/
lemma apply_pTransverse_e₁_eq_zero (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) : W (pTransverse g K) hP.e₁ = 0 := by
  obtain ⟨f, hf, hdet, hf₁, -⟩ := hP.exists_halfTurn hSymm
  have h := hW.covariant f hf hdet (pTransverse g K) hP.e₁
  rw [stabilizer_fixes_pTransverse g K hf, hf₁, map_neg] at h
  linarith

/-- A parity-odd tensor has no component mixing `p_T` with the spectator direction `e₂`. -/
lemma apply_pTransverse_e₂_eq_zero (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) : W (pTransverse g K) hP.e₂ = 0 := by
  obtain ⟨f, hf, hdet, -, hf₂⟩ := hP.exists_halfTurn hSymm
  have h := hW.covariant f hf hdet (pTransverse g K) hP.e₂
  rw [stabilizer_fixes_pTransverse g K hf, hf₂, map_neg] at h
  linarith

/-- **A parity-odd tensor has a single component.** In the adapted frame of a
`SpectatorPlane`, `W` is `W e₁ e₂` times the `2 × 2` determinant of the spectator
coordinates of its arguments. -/
lemma apply_eq_mul_apply_e₁_e₂ (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (a b c₁ c₂ a' b' d₁ d₂ : ℝ) :
    W (a • pTransverse g K + b • K.q + c₁ • hP.e₁ + c₂ • hP.e₂)
        (a' • pTransverse g K + b' • K.q + d₁ • hP.e₁ + d₂ • hP.e₂) =
      (c₁ * d₂ - c₂ * d₁) * W hP.e₁ hP.e₂ := by
  have h₁ := hW.apply_pTransverse_e₁_eq_zero hSymm hP
  have h₂ := hW.apply_pTransverse_e₂_eq_zero hSymm hP
  have h₁' : W hP.e₁ (pTransverse g K) = 0 := by rw [← hW.isAlt.neg_eq, h₁, neg_zero]
  have h₂' : W hP.e₂ (pTransverse g K) = 0 := by rw [← hW.isAlt.neg_eq, h₂, neg_zero]
  have h₂₁ : W hP.e₂ hP.e₁ = -W hP.e₁ hP.e₂ := (hW.isAlt.neg_eq _ _).symm
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hW.conserved_left, hW.conserved_right, hW.isAlt.self_eq_zero, h₁, h₂, h₁', h₂', h₂₁]
  ring

/-- Two parity-odd tensors agreeing on the spectator pair `(e₁, e₂)` are equal. -/
lemma eq_of_apply_e₁_e₂_eq (hSymm : g.IsSymm) (hP : SpectatorPlane g K) {W' : Bilin V}
    (hW : ParityOddAssumptions g K W) (hW' : ParityOddAssumptions g K W')
    (h : W hP.e₁ hP.e₂ = W' hP.e₁ hP.e₂) : W = W' := by
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
  obtain ⟨a', b', d₁, d₂, rfl⟩ := hP.span w
  rw [hW.apply_eq_mul_apply_e₁_e₂ hSymm hP, hW'.apply_eq_mul_apply_e₁_e₂ hSymm hP, h]

/-- A parity-odd tensor vanishes exactly when its spectator component `W e₁ e₂` does. -/
lemma eq_zero_iff (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) : W = 0 ↔ W hP.e₁ hP.e₂ = 0 :=
  ⟨fun h => by simp [h],
    fun h => hW.eq_of_apply_e₁_e₂_eq hSymm hP (parityOddAssumptions_zero g K) h⟩

/-- **The parity-odd sector is at most one-dimensional.** Under a `SpectatorPlane`, every
parity-odd tensor is a multiple of a fixed non-zero one `A`, with a unique coefficient. For
`A = ε(·, ·, p, q)` that coefficient is the third invariant coefficient of the hadronic
tensor. -/
theorem existsUnique_eq_smul (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) {A : Bilin V} (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) : ∃! c : ℝ, W = c • A := by
  have hAe : A hP.e₁ hP.e₂ ≠ 0 := fun h => hA0 ((hA.eq_zero_iff hSymm hP).mpr h)
  refine ⟨W hP.e₁ hP.e₂ / A hP.e₁ hP.e₂, hW.eq_of_apply_e₁_e₂_eq hSymm hP (hA.smul _) ?_, ?_⟩
  · simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp
  · rintro c rfl
    simp only [LinearMap.smul_apply, smul_eq_mul]
    field_simp

/-- **Parity conservation removes the parity-odd sector.** Under a `SpectatorPlane`, a
parity-odd tensor that is covariant under every stabilizer element, reflections included,
vanishes. -/
theorem eq_zero_of_isLorentzCovariant (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (hcov : IsLorentzCovariant g K W) : W = 0 :=
  (hW.eq_zero_iff hSymm hP).mpr <|
    covariant_spectator_offDiagonal_zero g K W hSymm hcov hP.e₁ hP.e₂ hP.e₁_e₁
      (apply_p_eq_zero_of_spectator g K hSymm hP.q_e₁ hP.pT_e₁) (by rw [hSymm.eq, hP.q_e₁])
      hP.e₁_e₂

end ParityOddAssumptions

/-- **The antisymmetric part of the hadronic tensor is a single multiple of the parity-odd
structure.** Under a `SpectatorPlane`, for any tensor `W` conserved in both slots and properly
covariant, and any non-zero parity-odd `A`, there is a unique `c` with `W - Wᵀ = c • A`. -/
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
one-dimensional on these kinematics. The same tensor is not `IsLorentzCovariant`, so proper
covariance is strictly weaker than full covariance.
-/

namespace Witness

/-- The `+---` Minkowski form on `ℝ⁴`: `g v w = v₀w₀ - v₁w₁ - v₂w₂ - v₃w₃`. -/
def gFour : Bilin (Fin 4 → ℝ) :=
  LinearMap.mk₂ ℝ (fun v w => v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Pi.add_apply]; ring)
    (fun _ _ _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring)

@[simp] lemma gFour_apply (v w : Fin 4 → ℝ) :
    gFour v w = v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := (rfl)

/-- `gFour` is symmetric. -/
lemma gFour_isSymm : gFour.IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp only [gFour_apply]
  ring

/-- Witness kinematics on `ℝ⁴`: timelike `p = (1, 0, 0, 0)` and spacelike
`q = (0, 0, 0, 1)`, with `Q² = 1`. -/
def kFour : DisKinematics (Fin 4 → ℝ) where
  p := ![1, 0, 0, 0]
  pPrime := 0
  k := ![0, 0, 0, 1]
  kPrime := 0
  q := ![0, 0, 0, 1]
  hq := by simp

@[simp] lemma kFour_p : kFour.p = ![1, 0, 0, 0] := (rfl)

@[simp] lemma kFour_pPrime : kFour.pPrime = 0 := (rfl)

@[simp] lemma kFour_k : kFour.k = ![0, 0, 0, 1] := (rfl)

@[simp] lemma kFour_kPrime : kFour.kPrime = 0 := (rfl)

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

@[simp] lemma aFour_apply (v w : Fin 4 → ℝ) :
    aFour v w = (Pi.basisFun ℝ (Fin 4)).det ![v, w, kFour.p, kFour.q] := (rfl)

/-- **`ParityOddAssumptions` is satisfiable.** The witness tensor `aFour` is alternating,
conserved and properly covariant. -/
lemma parityOddAssumptions_aFour : ParityOddAssumptions gFour kFour aFour where
  covariant f hf hdet v w := by
    have hp : f ![1, 0, 0, 0] = ![1, 0, 0, 0] := hf.fixes_p
    have hq : f ![0, 0, 0, 1] = ![0, 0, 0, 1] := hf.fixes_q
    have h : ![f v, f w, ![1, 0, 0, 0], ![0, 0, 0, 1]] =
        f ∘ ![v, w, ![1, 0, 0, 0], ![0, 0, 0, 1]] := by
      ext1 i
      fin_cases i <;> simp [hp, hq]
    simp only [aFour_apply, kFour_p, kFour_q, h, Module.Basis.det_comp, hdet, one_mul]
  conserved_left v := by
    rw [aFour_apply]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 3) rfl (by decide)
  isAlt v := by
    rw [aFour_apply]
    exact AlternatingMap.map_eq_zero_of_eq _ _ (i := 0) (j := 1) rfl (by decide)

/-- The spectator plane of the witness kinematics, spanned by the coordinate directions
`e₁ = (0, 1, 0, 0)` and `e₂ = (0, 0, 1, 0)`. -/
def spectatorPlaneFour : SpectatorPlane gFour kFour where
  e₁ := ![0, 1, 0, 0]
  e₂ := ![0, 0, 1, 0]
  q_e₁ := by simp
  q_e₂ := by simp
  pT_e₁ := by simp
  pT_e₂ := by simp
  e₁_e₂ := by simp
  e₁_e₁ := by simp
  e₂_e₂ := by simp
  span v := ⟨v 0, v 3, v 1, v 2, by ext i; fin_cases i <;> simp⟩

@[simp] lemma spectatorPlaneFour_e₁ : spectatorPlaneFour.e₁ = ![0, 1, 0, 0] := (rfl)

@[simp] lemma spectatorPlaneFour_e₂ : spectatorPlaneFour.e₂ = ![0, 0, 1, 0] := (rfl)

/-- The witness parity-odd tensor is non-zero. -/
lemma aFour_ne_zero : aFour ≠ 0 := by
  intro h
  have h₀ : aFour ![0, 1, 0, 0] ![0, 0, 1, 0] = 0 := by simp [h]
  rw [aFour_apply, Module.Basis.det_apply] at h₀
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Module.Basis.toMatrix_apply,
    Fin.succAbove] at h₀

/-- **Proper covariance is strictly weaker than full covariance.** The properly covariant,
non-zero tensor `aFour` is not `IsLorentzCovariant`. -/
lemma not_isLorentzCovariant_aFour : ¬ IsLorentzCovariant gFour kFour aFour := fun h =>
  aFour_ne_zero (parityOddAssumptions_aFour.eq_zero_of_isLorentzCovariant gFour_isSymm
    spectatorPlaneFour h)

end Witness

end Hadronic

end Tensors
end DIS
end Scattering
end QFT
end EpsilonEridani
