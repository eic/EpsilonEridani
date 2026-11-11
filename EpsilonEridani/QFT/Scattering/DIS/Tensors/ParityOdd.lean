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
data — an alternating four-form `ε`, contracted with `K.p` and `K.q` by `aOfAlt`, the hadronic
counterpart of `Leptonic.lMuNuOdd` — and is properly covariant on every space carrying a basis
of four vectors (`parityOddAssumptions_aOfAlt`).

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
- `aOfAlt ε K`: the parity-odd structure `ε(·, ·, p, q)`, the contraction of an alternating
  four-form `ε` with the hadron momentum `K.p` and the momentum transfer `K.q`; it is
  alternating and conserved on every space, and properly covariant on every space with a basis
  of four vectors (`parityOddAssumptions_aOfAlt`).

The kinematic hypotheses come from `Tensors.Basic`: `SpectatorPair` (two non-null, mutually
orthogonal spectator directions `e₁`, `e₂`), `SpectatorPlane` (a `SpectatorPair` completing
`p_T`, `q` to a frame of `V`) and `SpectatorSplitting` (every vector splits into `p_T`, `q`
and spectator parts), together with the determinant-one half-turn `exists_half_turn`. A
`SpectatorPlane` is the only place where four-dimensionality enters the hypotheses on the
tensor `W`; the canonical structure `A` needs an alternating four-form — and, for its proper
covariance, a basis of four vectors — separately.

## Main results

- `ParityOddAssumptions.apply_eq_mul_apply_e₁_e₂`: for a `SpectatorPair`, a parity-odd tensor
  on the span of `p_T`, `q`, `e₁`, `e₂` is determined by its single component `W e₁ e₂`.
- `ParityOddAssumptions.eq_div_smul`, `ParityOddAssumptions.existsUnique_eq_smul`: under a
  `SpectatorPlane`, any two parity-odd tensors are proportional, so a non-zero one `A` spans
  them all, with the unique coefficient `W e₁ e₂ / A e₁ e₂`.
- `sub_flip_eq_div_smul`, `existsUnique_sub_flip_eq_smul`: under a `SpectatorPlane`, `W - Wᵀ`
  (twice the antisymmetric part) of any conserved, properly covariant tensor is a unique
  multiple of a non-zero parity-odd `A`.
- `ParityOddAssumptions.apply_pTransverse_eq_zero_of_spectatorPlane`,
  `ParityOddAssumptions.apply_p_eq_zero_of_spectatorPlane`: a parity-odd tensor annihilates
  `p_T` and `p` in both slots under a `SpectatorPlane`.
- `ParityOddAssumptions.eq_zero_of_isLorentzCovariant`: under a `SpectatorSplitting` in which
  non-zero spectators are non-null, the parity-odd part vanishes under
  full covariance. No four-dimensionality enters.
- `Witness.aFour`: on Minkowski space `ℝ⁴` at the witness kinematics `kFour` — where
  `p·q ≠ 0`, so the DIS invariants are non-degenerate — the determinant contraction
  `ε(·, ·, p, q)` is a non-zero parity-odd tensor (`Witness.aFour_ne_zero`) and every
  parity-odd tensor there is a unique multiple of it (`Witness.existsUnique_eq_smul_aFour`),
  so the parity-odd sector is exactly one-dimensional. The same tensor is not
  `IsLorentzCovariant` (`Witness.not_isLorentzCovariant_aFour`), so proper covariance is
  strictly weaker than full covariance.
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
lemma conserved_right (hW : ParityOddAssumptions g K W) (v : V) : W v K.q = 0 :=
  hW.isAlt.isRefl.eq_zero (hW.conserved_left v)

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

namespace ParityOddAssumptions

variable {g : Bilin V} {K : DisKinematics V} {W : Bilin V}

/-- A parity-odd tensor annihilates `p_T` against any vector that a determinant-one
stabilizer element reverses: the component is both invariant under the element and negated
by it. -/
lemma apply_pTransverse_eq_zero_of_apply_eq_neg (hW : ParityOddAssumptions g K W)
    {f : V →ₗ[ℝ] V} (hf : IsKinematicStabilizer g K f) (hdet : LinearMap.det f = 1)
    {u : V} (hfu : f u = -u) : W (pTransverse g K) u = 0 :=
  Bilin.apply_eq_zero_of_apply_eq_self_of_apply_eq_neg (hW.proper_covariant f hf hdet _ _)
    (stabilizer_fixes_pTransverse g K hf) hfu

/-- **A parity-odd tensor has a single component.** On the span of `p_T`, `q` and a
`SpectatorPair` `e₁`, `e₂`, `W` is `W e₁ e₂` times the `2 × 2` determinant of the spectator
coordinates of its arguments. -/
lemma apply_eq_mul_apply_e₁_e₂ (hSymm : g.IsSymm) (hP : SpectatorPair g K)
    (hW : ParityOddAssumptions g K W) (a b c₁ c₂ a' b' d₁ d₂ : ℝ) :
    W (a • pTransverse g K + b • K.q + c₁ • hP.e₁ + c₂ • hP.e₂)
        (a' • pTransverse g K + b' • K.q + d₁ • hP.e₁ + d₂ • hP.e₂) =
      (c₁ * d₂ - c₂ * d₁) * W hP.e₁ hP.e₂ := by
  obtain ⟨f, hf, hdet, hf₁, hf₂⟩ := exists_half_turn hSymm hP.q_orthogonal_e₁
    hP.pT_orthogonal_e₁ hP.e₁_self_ne_zero hP.q_orthogonal_e₂ hP.pT_orthogonal_e₂
    hP.e₂_self_ne_zero hP.e₁_orthogonal_e₂
  have h₁ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₁
  have h₂ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₂
  have h₁' : W hP.e₁ (pTransverse g K) = 0 := hW.isAlt.isRefl.eq_zero h₁
  have h₂' : W hP.e₂ (pTransverse g K) = 0 := hW.isAlt.isRefl.eq_zero h₂
  have h₂₁ : W hP.e₂ hP.e₁ = -W hP.e₁ hP.e₂ := (hW.isAlt.neg_eq _ _).symm
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hW.conserved_left, hW.conserved_right, hW.isAlt.self_eq_zero, h₁, h₂, h₁', h₂', h₂₁]
  ring

/-- **A parity-odd tensor annihilates `p_T` under a `SpectatorPlane`.** In the frame `p_T`, `q`,
`e₁`, `e₂`, the vector `p_T` has no spectator coordinates. -/
lemma apply_pTransverse_eq_zero_of_spectatorPlane (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W (pTransverse g K) v = 0 := by
  obtain ⟨a', b', d₁, d₂, rfl⟩ := hP.span v
  simpa using hW.apply_eq_mul_apply_e₁_e₂ hSymm hP.toSpectatorPair 1 0 0 0 a' b' d₁ d₂

/-- A parity-odd tensor annihilates `p` under a `SpectatorPlane`. -/
lemma apply_p_eq_zero_of_spectatorPlane (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W K.p v = 0 := by
  rw [apply_p_eq_apply_pTransverse (g := g) hW.conserved_left,
    hW.apply_pTransverse_eq_zero_of_spectatorPlane hSymm hP]

/-- A parity-odd tensor annihilates `p_T` in the second slot under a `SpectatorPlane`. -/
lemma apply_pTransverse_eq_zero_right_of_spectatorPlane (hSymm : g.IsSymm)
    (hP : SpectatorPlane g K) (hW : ParityOddAssumptions g K W) (v : V) :
    W v (pTransverse g K) = 0 :=
  hW.isAlt.isRefl.eq_zero (hW.apply_pTransverse_eq_zero_of_spectatorPlane hSymm hP v)

/-- A parity-odd tensor annihilates `p` in the second slot under a `SpectatorPlane`. -/
lemma apply_p_eq_zero_right_of_spectatorPlane (hSymm : g.IsSymm) (hP : SpectatorPlane g K)
    (hW : ParityOddAssumptions g K W) (v : V) :
    W v K.p = 0 :=
  hW.isAlt.isRefl.eq_zero (hW.apply_p_eq_zero_of_spectatorPlane hSymm hP v)

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
    covariant_spectator_offDiagonal_zero' g K W hSymm hcov (hnull u huq huT) huq huT huv
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
  have hTu' : W (pTransverse g K) u' = 0 := hW.isAlt.isRefl.eq_zero (hspec u' _ hu'q hu'T)
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
## The canonical parity-odd structure

On any real vector space the parity-odd structure `ε(·, ·, p, q)` is the contraction of an
alternating four-form with the hadron momentum and the momentum transfer; the form is supplied
as data, exactly as on the leptonic side (`Leptonic.lMuNuOdd`). Alternation and conservation
hold on every space, with no basis at all. On a space carrying a basis `b` of four vectors
every alternating four-form is a multiple of the volume form `b.det`
(`AlternatingMap.eq_smul_basis_det`), and a stabilizer element of determinant one commutes
with the volume form, so the structure is properly covariant there for every bilinear form.
-/

/-- The parity-odd structure `ε(v, w, p, q)` of the kinematics `K` on a real vector space: the
contraction of an alternating four-form `ε` with the hadron momentum `K.p` and the momentum
transfer `K.q`. This is the hadronic counterpart of `Leptonic.lMuNuOdd`. -/
def aOfAlt (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V) : Bilin V :=
  ε.bilinMap ![K.p, K.q]

/-- Pointwise value of the parity-odd structure. -/
lemma aOfAlt_apply (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V) (v w : V) :
    aOfAlt ε K v w = ε ![v, w, K.p, K.q] :=
  ε.bilinMap_apply _ v w

/-- The parity-odd structure is alternating. -/
lemma isAlt_aOfAlt (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V) :
    (aOfAlt ε K).IsAlt :=
  ε.isAlt_bilinMap _

/-- The parity-odd structure vanishes on the diagonal. -/
@[simp] lemma aOfAlt_apply_self (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V) (v : V) :
    aOfAlt ε K v v = 0 :=
  ε.bilinMap_apply_self _ v

/-- The parity-odd structure annihilates the hadron momentum in its first slot. -/
@[simp] lemma aOfAlt_apply_p_left_eq_zero (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V)
    (w : V) : aOfAlt ε K K.p w = 0 :=
  ε.bilinMap_apply_left_eq_zero ![K.p, K.q] 0 w

/-- The parity-odd structure annihilates the hadron momentum in its second slot. -/
@[simp] lemma aOfAlt_apply_p_right_eq_zero (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V)
    (v : V) : aOfAlt ε K v K.p = 0 :=
  ε.bilinMap_apply_right_eq_zero ![K.p, K.q] 0 v

/-- The parity-odd structure annihilates the momentum transfer in its first slot: it is
conserved there. -/
@[simp] lemma aOfAlt_apply_q_left_eq_zero (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V)
    (w : V) : aOfAlt ε K K.q w = 0 :=
  ε.bilinMap_apply_left_eq_zero ![K.p, K.q] 1 w

/-- The parity-odd structure annihilates the momentum transfer in its second slot: it is
conserved there. -/
@[simp] lemma aOfAlt_apply_q_right_eq_zero (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : DisKinematics V)
    (v : V) : aOfAlt ε K v K.q = 0 :=
  ε.bilinMap_apply_right_eq_zero ![K.p, K.q] 1 v

/-- **The contraction of an alternating four-form with `p` and `q` is parity-odd.** For any
bilinear form `g`, any alternating four-form `ε` on a space carrying a basis `b` of four
vectors, and any kinematics `K`, the structure `aOfAlt ε K` is alternating, conserved and
properly covariant. Alternation and conservation use nothing but the alternating-map API;
proper covariance uses that `ε` is a multiple of the volume form `b.det`, which a stabilizer
element of determinant one commutes with. -/
lemma parityOddAssumptions_aOfAlt (g : Bilin V) (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (b : Module.Basis (Fin 4) ℝ V) (K : DisKinematics V) :
    ParityOddAssumptions g K (aOfAlt ε K) where
  proper_covariant f hf hdet v w := by
    have hvec : ![f v, f w, K.p, K.q] = f ∘ ![v, w, K.p, K.q] := by
      ext1 i
      fin_cases i <;> simp [hf.fixes_p, hf.fixes_q]
    obtain ⟨c, hc⟩ : ∃ c : ℝ, ε = c • b.det := ⟨ε b, ε.eq_smul_basis_det b⟩
    simp only [aOfAlt_apply, hc, IsSMulApply.smul_apply, smul_eq_mul, hvec,
      Module.Basis.det_comp, hdet, one_mul]
  conserved_left v := aOfAlt_apply_q_left_eq_zero ε K v
  isAlt := isAlt_aOfAlt ε K

/-!
## A four-dimensional witness

On Minkowski space `ℝ⁴` with `p = (1, 0, 0, -4/5)` and `q = (0, 0, 0, 1)`, the contraction
`ε(·, ·, p, q)` of the determinant is a non-zero parity-odd tensor, and the two remaining
coordinate directions form a `SpectatorPlane`. The kinematics are non-degenerate —
`p·q = 4/5`, `Q² = 1` and `x_Bj = 5/8` — so the DIS invariants are defined there. The
hypotheses of `ParityOddAssumptions.existsUnique_eq_smul` are satisfiable, and the parity-odd
sector is exactly one-dimensional on these kinematics (`existsUnique_eq_smul_aFour`). The
same tensor is not `IsLorentzCovariant`, so proper covariance is strictly weaker than full
covariance.

The structure `aFour` is `aOfAlt` at the volume form of the standard basis
`Pi.basisFun ℝ (Fin 4)`, specialized to the witness kinematics; the declarations of this
section are stated about it directly.
-/

namespace Witness

/-- The `+---` Minkowski form on `ℝ⁴`: `g v w = v₀w₀ - v₁w₁ - v₂w₂ - v₃w₃`. -/
def gFour : Bilin (Fin 4 → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal ![1, -1, -1, -1])

@[simp] lemma gFour_apply (v w : Fin 4 → ℝ) :
    gFour v w = v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := by
  simp only [gFour, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_mul,
    neg_mul, mul_neg]
  ring

/-- `gFour` is symmetric. -/
lemma gFour_isSymm : gFour.IsSymm :=
  Matrix.isSymm_toBilin'_iff_isSymm.mpr (Matrix.isSymm_diagonal _)

/-- Witness kinematics on `ℝ⁴`: timelike `p = (1, 0, 0, -4/5)` and spacelike
`q = (0, 0, 0, 1)`. The invariants are non-degenerate: `Q² = 1`, `p·q = 4/5` and `x_Bj = 5/8`,
so the transverse hadron momentum is `p_T = (1, 0, 0, 0)` and the spectator plane is the
coordinate `1`-`2` plane. The lepton momenta are placeholders. -/
noncomputable def kFour : DisKinematics (Fin 4 → ℝ) where
  p := ![1, 0, 0, -4/5]
  pPrime := 0
  k := ![0, 0, 0, 1]
  kPrime := 0
  q := ![0, 0, 0, 1]
  hq := by simp

@[simp] lemma kFour_p : kFour.p = ![1, 0, 0, -4/5] := (rfl)

@[simp] lemma kFour_q : kFour.q = ![0, 0, 0, 1] := (rfl)

@[simp] lemma kFour_k : kFour.k = ![0, 0, 0, 1] := (rfl)

@[simp] lemma kFour_kPrime : kFour.kPrime = 0 := (rfl)

@[simp] lemma kFour_pPrime : kFour.pPrime = 0 := (rfl)

/-- The transverse hadron momentum of the witness kinematics is `(1, 0, 0, 0)`: the
`q`-component of `p` is exactly cancelled. -/
@[simp] lemma pTransverse_kFour : pTransverse gFour kFour = ![1, 0, 0, 0] := by
  ext i
  fin_cases i <;> simp [pTransverse]

/-- The parity-odd structure `ε(v, w, p, q)` of the witness kinematics on `ℝ⁴`: `aOfAlt` at
the volume form of the standard basis `Pi.basisFun ℝ (Fin 4)`, whose contraction with
`kFour.p` and `kFour.q` is the determinant `ε(v, w, p, q) = det(v, w, p, q)`. -/
noncomputable def aFour : Bilin (Fin 4 → ℝ) :=
  aOfAlt (Pi.basisFun ℝ (Fin 4)).det kFour

/-- The closed form of `aFour`: with `p_T` along the `0` axis and `q` along the `3` axis,
`ε(v, w, p, q)` is the `2 × 2` determinant of the spectator components `1`, `2` of `v` and
`w`; the components of `v` and `w` along `p_T` and `q` do not enter. -/
@[simp] lemma aFour_apply (v w : Fin 4 → ℝ) :
    aFour v w = v 1 * w 2 - v 2 * w 1 := by
  simp only [aFour, aOfAlt_apply, Module.Basis.det_apply, Module.Basis.toMatrix_apply,
    Pi.basisFun_repr, kFour_p, kFour_q, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.cons_val_one,
    Matrix.cons_val, Matrix.cons_val_succ, Matrix.submatrix_apply,
    Matrix.submatrix_submatrix, Matrix.det_unique, Function.comp_apply, Fin.isValue,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.default_eq_zero, Fin.reduceSucc,
    Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.succ_eq_add_one, Nat.reduceAdd, pow_zero,
    one_mul, Fin.castSucc_zero, Fin.castSucc_one, Fin.reduceCastSucc, Fin.val_succ,
    Fin.val_eq_zero, zero_add, pow_one, neg_mul, Fin.succ_pos, Fin.succAbove_of_le_castSucc,
    Fin.succAbove_of_castSucc_lt, Finset.univ_unique, Finset.sum_neg_distrib,
    Finset.sum_singleton, Fin.succ_succAbove_one, even_two, Even.neg_pow, one_pow, mul_one,
    zero_mul, neg_zero, add_zero, mul_zero, zero_le, Std.le_refl, Fin.reduceLE,
    Finset.sum_const_zero]
  ring

/-- The spectator plane of the witness kinematics, spanned by the coordinate directions
`e₁ = (0, 1, 0, 0)` and `e₂ = (0, 0, 1, 0)`. -/
def spectatorPlaneFour : SpectatorPlane gFour kFour where
  e₁ := ![0, 1, 0, 0]
  e₂ := ![0, 0, 1, 0]
  q_orthogonal_e₁ := by simp
  q_orthogonal_e₂ := by simp
  pT_orthogonal_e₁ := by simp
  pT_orthogonal_e₂ := by simp
  e₁_orthogonal_e₂ := by simp
  e₁_self_ne_zero := by simp
  e₂_self_ne_zero := by simp
  span v := ⟨v 0, v 3, v 1, v 2, by ext i; fin_cases i <;> simp⟩

@[simp] lemma spectatorPlaneFour_e₁ : spectatorPlaneFour.e₁ = ![0, 1, 0, 0] := (rfl)

@[simp] lemma spectatorPlaneFour_e₂ : spectatorPlaneFour.e₂ = ![0, 0, 1, 0] := (rfl)

/-- The spectator component of the witness parity-odd tensor: `aFour e₁ e₂ = 1` for
the spectator directions `e₁ = (0, 1, 0, 0)` and `e₂ = (0, 0, 1, 0)` of `spectatorPlaneFour`.
-/
lemma aFour_e₁_e₂ : aFour spectatorPlaneFour.e₁ spectatorPlaneFour.e₂ = 1 := by
  simp

/-- The witness parity-odd tensor is non-zero. -/
lemma aFour_ne_zero : aFour ≠ 0 := fun h => by
  simpa [h] using aFour_e₁_e₂

/-- **The parity-odd sector of the witness is one-dimensional.** Every parity-odd tensor on
the witness kinematics is a unique multiple of `aFour`. -/
theorem existsUnique_eq_smul_aFour {W : Bilin (Fin 4 → ℝ)}
    (hW : ParityOddAssumptions gFour kFour W) : ∃! c : ℝ, W = c • aFour :=
  hW.existsUnique_eq_smul gFour_isSymm spectatorPlaneFour
    (parityOddAssumptions_aOfAlt gFour (Pi.basisFun ℝ (Fin 4)).det (Pi.basisFun ℝ (Fin 4))
      kFour) aFour_ne_zero

/-- On the witness kinematics every non-zero spectator is non-null: the spectator subspace is
the spacelike plane of the coordinates `1` and `2`. -/
lemma gFour_self_ne_zero_of_spectator {u : Fin 4 → ℝ}
    (hq : gFour kFour.q u = 0) (hT : gFour (pTransverse gFour kFour) u = 0)
    (hu : u ≠ 0) : gFour u u ≠ 0 := by
  obtain ⟨a, b, c₁, c₂, rfl⟩ := spectatorPlaneFour.span u
  simp only [gFour_apply, kFour_q, pTransverse_kFour, spectatorPlaneFour_e₁,
    spectatorPlaneFour_e₂] at hq hT ⊢
  have h₀ : a = 0 := by simpa using hT
  have h₃ : b = 0 := by simpa using hq
  have h₁₂ : c₁ ≠ 0 ∨ c₂ ≠ 0 := by
    by_contra! h
    rcases h with ⟨hc₁, hc₂⟩
    apply hu
    simp [h₀, h₃, hc₁, hc₂]
  subst h₀ h₃
  simp only [zero_smul, zero_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero, mul_one]
  rcases h₁₂ with h | h <;> nlinarith [sq_pos_of_ne_zero h]

/-- **Proper covariance is strictly weaker than full covariance.** The properly covariant,
non-zero tensor `aFour` is not `IsLorentzCovariant`. -/
lemma not_isLorentzCovariant_aFour : ¬ IsLorentzCovariant gFour kFour aFour := fun h =>
  aFour_ne_zero ((parityOddAssumptions_aOfAlt gFour (Pi.basisFun ℝ (Fin 4)).det
      (Pi.basisFun ℝ (Fin 4)) kFour).eq_zero_of_isLorentzCovariant gFour_isSymm
    spectatorPlaneFour.toSpectatorSplitting
    (fun _ hq hT hu => gFour_self_ne_zero_of_spectator hq hT hu) h)

end Witness

end Hadronic

end Tensors
end DIS
end Scattering
end QFT
end EpsilonEridani
