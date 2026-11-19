/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Tensors.ParityOdd

/-!
# The three invariant coefficients of the hadronic tensor

For an unpolarized spin-half target probed by a vector/axial-vector current, the inclusive
hadronic tensor is fixed by three invariant functions:

  `W^{μν} = F₁ (-g^{μν} + q^μ q^ν / q²) + (F₂ / (p·q)) p_T^μ p_T^ν + c ε^{μναβ} p_α q_β`,

where the coefficient `c` of the parity-odd structure is the literature's `F₃ / (2 p·q)`, up to
the normalization of `ε` (Devenish & Cooper-Sarkar, *Deep Inelastic Scattering* (2004), ch. 3;
Halzen & Martin, *Quarks and Leptons* (1984), ch. 8). This module proves that statement for the
real bilinear forms of `Tensors.Basic`: covariance under the proper kinematic stabilizer and
current conservation leave exactly the transverse pair `fromF1F2` and one parity-odd structure
`A`, and the three coefficients are determined by the tensor. As in `fromF1F2`, the Lean
coefficient `F₂` is the literature's `F₂ / (p·q)`; the Lean `F₁` is the literature's `F₁`. It
is the statement that licenses reading three structure functions off a measured cross section.

No symmetry hypothesis is placed on `W`. The symmetric part comes out as the parity-even pair and
the antisymmetric part as the parity-odd term (`inv_two_smul_fromF1F2_add_smul_add_flip`,
`inv_two_smul_fromF1F2_add_smul_sub_flip`): in the real model this split is what hermiticity of
the complex tensor means.

## Proper covariance on a spectator plane

The input is a `SpectatorPlane` `e₁`, `e₂` whose two norms have the same sign. Rescaling `e₂`
(`SpectatorPlane.equalizeNorms`) makes the norms equal, and then, besides the half-turn
`exists_half_turn`, which reverses both spectators, the proper stabilizer contains the
quarter-turn `e₁ ↦ e₂ ↦ -e₁` of `exists_quarter_turn` (both in `Tensors.Spectators`). These two
elements alone cut a conserved, properly covariant tensor down to three components,
`W(p_T, p_T)`, `W(e₁, e₁)` and `W(e₁, e₂)` (`IsProperLorentzCovariant.apply_eq_of_spectatorPair`).
For Minkowski space with `p` timelike and `q` spacelike the spectator plane is spacelike, and any
orthogonal basis of it qualifies.

## Main results

- `IsProperLorentzCovariant.eq_fromF1F2_add_div_smul`, `exists_eq_fromF1F2_add_smul`: every
  conserved, properly covariant `W` is `fromF1F2 g K F₁ F₂ + c • A` for a fixed non-zero
  parity-odd `A`, with the coefficients read off on `(p_T, p_T)`, `(e₁, e₁)` and `(e₁, e₂)`.
- `fromF1F2_add_smul_injective`: the coefficients `(F₁, F₂, c)` are determined by the tensor.
- `existsUnique_eq_fromF1F2_add_smul`: the two together.
- `inv_two_smul_fromF1F2_add_smul_add_flip`, `inv_two_smul_fromF1F2_add_smul_sub_flip`: the
  symmetric and antisymmetric parts of such a tensor are the parity-even pair and the parity-odd
  term.
- `exists_eq_fromF1F2_add_smul_iff`: a tensor is such a combination exactly when it is conserved
  and properly covariant.
- `Witness.existsUnique_eq_fromF1F2_add_smul_aFour`: on Minkowski space `ℝ⁴` at the witness
  kinematics of `Tensors.ParityOdd`, with `A = ε(·, ·, p, q)`, the hypotheses hold.
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

variable {g : Bilin V} {K : DisKinematics V}

/-!
## Three components
-/

/-- **A conserved, properly covariant tensor has three components.** On the span of `p_T`, `q`
and a `SpectatorPair` `e₁`, `e₂` of equal norm, such a tensor is determined by `W(p_T, p_T)`,
`W(e₁, e₁)` and `W(e₁, e₂)`: it has no mixed `p_T`-spectator components, and its spectator
block is `W(e₁, e₁)` times the identity plus `W(e₁, e₂)` times the `2 × 2` determinant. -/
lemma IsProperLorentzCovariant.apply_eq_of_spectatorPair {W : Bilin V} (hSymm : g.IsSymm)
    (hP : SpectatorPair g K) (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂)
    (hW : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) (a b c₁ c₂ a' b' d₁ d₂ : ℝ) :
    W (a • pTransverse g K + b • K.q + c₁ • hP.e₁ + c₂ • hP.e₂)
        (a' • pTransverse g K + b' • K.q + d₁ • hP.e₁ + d₂ • hP.e₂) =
      a * a' * W (pTransverse g K) (pTransverse g K) + (c₁ * d₁ + c₂ * d₂) * W hP.e₁ hP.e₁
        + (c₁ * d₂ - c₂ * d₁) * W hP.e₁ hP.e₂ := by
  -- The half-turn removes the mixed `p_T`-spectator components.
  obtain ⟨f, hf, hdet, hf₁, hf₂⟩ := hP.exists_half_turn hSymm
  have hT₁ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₁
  have hT₂ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₂
  have h₁T := hW.apply_pTransverse_right_eq_zero_of_apply_eq_neg hf hdet hf₁
  have h₂T := hW.apply_pTransverse_right_eq_zero_of_apply_eq_neg hf hdet hf₂
  -- The quarter-turn relates the four spectator components.
  obtain ⟨r, hr, hrdet, hr₁, hr₂⟩ := hP.exists_quarter_turn hSymm hnorm
  have h₂₂ : W hP.e₂ hP.e₂ = W hP.e₁ hP.e₁ := by
    rw [← hr₁, hW r hr hrdet]
  have h₂₁ : W hP.e₂ hP.e₁ = -W hP.e₁ hP.e₂ := by
    have h := hW r hr hrdet hP.e₁ hP.e₂
    rw [hr₁, hr₂, map_neg] at h
    linarith
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hleft,
    hright, hT₁, hT₂, h₁T, h₂T, h₂₂, h₂₁]
  ring

/-- Two conserved, properly covariant tensors that agree on `(p_T, p_T)`, `(e₁, e₁)` and
`(e₁, e₂)`, for a `SpectatorPlane` whose two norms have the same sign, are equal. -/
lemma IsProperLorentzCovariant.eq_of_apply_eq {W W' : Bilin V} (hSymm : g.IsSymm)
    (hP : SpectatorPlane g K) (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂)
    (hW : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) (hW' : IsProperLorentzCovariant g K W')
    (hleft' : ∀ v : V, W' K.q v = 0) (hright' : ∀ v : V, W' v K.q = 0)
    (hTT : W (pTransverse g K) (pTransverse g K) = W' (pTransverse g K) (pTransverse g K))
    (h₁₁ : W hP.e₁ hP.e₁ = W' hP.e₁ hP.e₁) (h₁₂ : W hP.e₁ hP.e₂ = W' hP.e₁ hP.e₂) :
    W = W' := by
  -- Work in the plane with `e₂` rescaled to the norm of `e₁`.
  have hN := hP.toSpectatorPair.equalizeNorms_self_eq hsign
  have h₁₂' :
      W (hP.toSpectatorPair.equalizeNorms hsign).e₁
          (hP.toSpectatorPair.equalizeNorms hsign).e₂ =
        W' (hP.toSpectatorPair.equalizeNorms hsign).e₁
          (hP.toSpectatorPair.equalizeNorms hsign).e₂ := by
    simp only [SpectatorPair.equalizeNorms_e₁, SpectatorPair.equalizeNorms_e₂, map_smul, h₁₂]
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨a, b, c₁, c₂, rfl⟩ := (hP.equalizeNorms hsign).span v
  obtain ⟨a', b', d₁, d₂, rfl⟩ := (hP.equalizeNorms hsign).span w
  simp only [SpectatorPlane.equalizeNorms_toSpectatorPair]
  rw [hW.apply_eq_of_spectatorPair hSymm _ hN hleft hright,
    hW'.apply_eq_of_spectatorPair hSymm _ hN hleft' hright', hTT, h₁₂',
    SpectatorPair.equalizeNorms_e₁, h₁₁]

/-!
## The transverse pair plus a parity-odd structure
-/

/-- The transverse pair plus a multiple of a properly covariant structure is properly
covariant. -/
lemma fromF1F2_add_smul_isProperLorentzCovariant {A : Bilin V}
    (hA : IsProperLorentzCovariant g K A) (F1 F2 c : ℝ) :
    IsProperLorentzCovariant g K (fromF1F2 g K F1 F2 + c • A) :=
  (fromF1F2_isLorentzCovariant g K F1 F2).isProperLorentzCovariant.add (hA.smul c)

/-- The transverse pair plus a multiple of a structure conserved in the first slot is
conserved in the first slot. -/
lemma fromF1F2_add_smul_conserved_left {A : Bilin V} (hQ2 : g K.q K.q ≠ 0)
    (hA : ∀ v : V, A K.q v = 0) (F1 F2 c : ℝ) (v : V) :
    (fromF1F2 g K F1 F2 + c • A) K.q v = 0 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, fromF1F2_conserved_left g K hQ2, hA,
    smul_zero, add_zero]

/-- The transverse pair plus a multiple of a structure conserved in the second slot is
conserved in the second slot. -/
lemma fromF1F2_add_smul_conserved_right {A : Bilin V} (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (hA : ∀ v : V, A v K.q = 0) (F1 F2 c : ℝ) (v : V) :
    (fromF1F2 g K F1 F2 + c • A) v K.q = 0 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    fromF1F2_conserved_right g K hSymm hQ2, hA, smul_zero, add_zero]

/-- On `(p_T, p_T)` the transverse pair plus a multiple of an alternating structure takes the
value `-F₁ (p_T·p_T) + F₂ (p_T·p_T)²`. -/
lemma fromF1F2_add_smul_apply_pTransverse {A : Bilin V} (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
    (hA : A.IsAlt) (F1 F2 c : ℝ) :
    (fromF1F2 g K F1 F2 + c • A) (pTransverse g K) (pTransverse g K) =
      -(F1 * g (pTransverse g K) (pTransverse g K))
        + F2 * g (pTransverse g K) (pTransverse g K) ^ 2 := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [apply_pTransverse_self g K _ hSymm hQ2 F1 F2 (fromF1F2_isDecomposition g K F1 F2),
    hA.self_eq_zero, smul_zero, add_zero]
  ring

/-- On a spectator `e`, `(e, e)` sees only the transverse projector: the transverse pair plus a
multiple of an alternating structure takes the value `-F₁ (e·e)`. -/
lemma fromF1F2_add_smul_apply_self_of_spectator {A : Bilin V} (hA : A.IsAlt) {e : V}
    (heq : g K.q e = 0) (heT : g (pTransverse g K) e = 0) (F1 F2 c : ℝ) :
    (fromF1F2 g K F1 F2 + c • A) e e = -(F1 * g e e) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [apply_self_of_isF1F2Decomposition_of_spectator g K (fromF1F2_isDecomposition g K F1 F2) heq
      heT, hA.self_eq_zero, smul_zero, add_zero]
  ring

/-- On a spectator `e` and a vector `e'` orthogonal to it the transverse pair vanishes, so
`fromF1F2 g K F1 F2 + c • A` takes the value `c * A e e'`. -/
lemma fromF1F2_add_smul_apply_of_spectator (A : Bilin V) {e e' : V} (heq : g K.q e = 0)
    (heT : g (pTransverse g K) e = 0) (hee' : g e e' = 0) (F1 F2 c : ℝ) :
    (fromF1F2 g K F1 F2 + c • A) e e' = c * A e e' := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, fromF1F2_apply,
    transverseMetric_apply, heq, heT, hee', mul_zero, zero_mul, neg_zero, add_zero, zero_add]

/-- Exchanging the slots of the transverse pair plus a multiple of an alternating structure
reverses only the alternating term. -/
lemma fromF1F2_add_smul_flip {A : Bilin V} (hSymm : g.IsSymm) (hA : A.IsAlt) (F1 F2 c : ℝ) :
    (fromF1F2 g K F1 F2 + c • A).flip = fromF1F2 g K F1 F2 - c • A :=
  Bilin.flip_add_smul_of_isSymm_of_isAlt (fromF1F2_isSymm g K hSymm F1 F2) hA c

/-- The symmetric part of the transverse pair plus a multiple of an alternating structure is the
transverse pair. -/
theorem inv_two_smul_fromF1F2_add_smul_add_flip {A : Bilin V} (hSymm : g.IsSymm) (hA : A.IsAlt)
    (F1 F2 c : ℝ) :
    (2 : ℝ)⁻¹ • (fromF1F2 g K F1 F2 + c • A + (fromF1F2 g K F1 F2 + c • A).flip) =
      fromF1F2 g K F1 F2 := by
  rw [fromF1F2_add_smul_flip hSymm hA]
  module

/-- The antisymmetric part of the transverse pair plus a multiple of an alternating structure is
the alternating term. -/
theorem inv_two_smul_fromF1F2_add_smul_sub_flip {A : Bilin V} (hSymm : g.IsSymm) (hA : A.IsAlt)
    (F1 F2 c : ℝ) :
    (2 : ℝ)⁻¹ • (fromF1F2 g K F1 F2 + c • A - (fromF1F2 g K F1 F2 + c • A).flip) = c • A := by
  rw [fromF1F2_add_smul_flip hSymm hA]
  module

/-!
## Existence and uniqueness of the three coefficients
-/

/-- **The three coefficients, explicitly.** Under a `SpectatorPlane` whose two norms have the
same sign, with `Q² ≠ 0` and `p_T` non-null, every tensor conserved in both slots and properly
covariant is the transverse pair `fromF1F2 g K F₁ F₂` plus `c • A`, for a fixed non-zero
parity-odd structure `A`, with `F₁ = -W(e₁, e₁) / (e₁·e₁)`,
`F₂ = (W(p_T, p_T) + F₁ (p_T·p_T)) / (p_T·p_T)²` and `c = W(e₁, e₂) / A(e₁, e₂)`. No symmetry
of `W` is assumed. -/
theorem IsProperLorentzCovariant.eq_fromF1F2_add_div_smul {W A : Bilin V}
    (hcov : IsProperLorentzCovariant g K W) (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
    (hP : SpectatorPlane g K) (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) (hleft : ∀ v : V, W K.q v = 0) (hright : ∀ v : V, W v K.q = 0) :
    W = fromF1F2 g K (-(W hP.e₁ hP.e₁ / g hP.e₁ hP.e₁))
        ((W (pTransverse g K) (pTransverse g K)
          - W hP.e₁ hP.e₁ / g hP.e₁ hP.e₁ * g (pTransverse g K) (pTransverse g K))
          / g (pTransverse g K) (pTransverse g K) ^ 2)
      + (W hP.e₁ hP.e₂ / A hP.e₁ hP.e₂) • A := by
  have hA₁₂ := hA.apply_e₁_e₂_ne_zero hSymm hP hA0
  have he₁ := hP.e₁_self_ne_zero
  refine hcov.eq_of_apply_eq hSymm hP hsign hleft hright
    (fromF1F2_add_smul_isProperLorentzCovariant hA.proper_covariant _ _ _)
    (fromF1F2_add_smul_conserved_left hQ2 hA.conserved_left _ _ _)
    (fromF1F2_add_smul_conserved_right hSymm hQ2 hA.conserved_right _ _ _) ?_ ?_ ?_
  · -- The `(p_T, p_T)` component fixes `F₂` once `F₁` is known.
    rw [fromF1F2_add_smul_apply_pTransverse hSymm hQ2 hA.isAlt]
    field_simp [hTT, he₁]
    ring
  · -- The `(e₁, e₁)` component sees only the transverse projector.
    rw [fromF1F2_add_smul_apply_self_of_spectator hA.isAlt hP.q_orthogonal_e₁
      hP.pT_orthogonal_e₁]
    field_simp [he₁]
  · -- The `(e₁, e₂)` component sees only the parity-odd structure.
    rw [fromF1F2_add_smul_apply_of_spectator A hP.q_orthogonal_e₁ hP.pT_orthogonal_e₁
      hP.e₁_orthogonal_e₂]
    field_simp [hA₁₂]

/-- **Three structures are enough.** Under a `SpectatorPlane` whose two norms have the same
sign, with `Q² ≠ 0` and `p_T` non-null, every tensor conserved in both slots and properly
covariant is the transverse pair `fromF1F2 g K F1 F2` plus a multiple of a fixed non-zero
parity-odd structure `A`. No symmetry of `W` is assumed. -/
theorem exists_eq_fromF1F2_add_smul {W A : Bilin V} (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
    (hP : SpectatorPlane g K) (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) (hcov : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) :
    ∃ F1 F2 c : ℝ, W = fromF1F2 g K F1 F2 + c • A :=
  ⟨_, _, _, hcov.eq_fromF1F2_add_div_smul hSymm hQ2 hP hsign hTT hA hA0 hleft hright⟩

/-- **The three coefficients are determined by the tensor.** For a non-null spectator `e` and a
vector `e'` orthogonal to it with `A e e' ≠ 0`, and with `Q² ≠ 0` and `p_T` non-null, the map
`(F₁, F₂, c) ↦ fromF1F2 g K F₁ F₂ + c • A` is injective. -/
theorem fromF1F2_add_smul_injective {A : Bilin V} (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) {e e' : V} (heq : g K.q e = 0)
    (heT : g (pTransverse g K) e = 0) (he : g e e ≠ 0) (hee' : g e e' = 0)
    (hA : A e e' ≠ 0) :
    Function.Injective fun F : ℝ × ℝ × ℝ => fromF1F2 g K F.1 F.2.1 + F.2.2 • A := by
  rintro ⟨F1, F2, c⟩ ⟨F1', F2', c'⟩ h
  -- Only beta-reduces the lambda applied to the two triples.
  dsimp only at h
  -- The parity-odd coefficient is read off on `(e, e')`, where the transverse pair vanishes.
  have hee := LinearMap.congr_fun₂ h e e'
  rw [fromF1F2_add_smul_apply_of_spectator A heq heT hee',
    fromF1F2_add_smul_apply_of_spectator A heq heT hee'] at hee
  obtain rfl : c = c' := mul_right_cancel₀ hA hee
  -- The other two then follow from `decomposition_unique`.
  have hdec : IsF1F2Decomposition g K (fromF1F2 g K F1 F2) F1' F2' := fun v w => by
    have hvw := LinearMap.congr_fun₂ h v w
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_left_inj] at hvw
    rw [hvw, fromF1F2_apply]
  obtain ⟨rfl, rfl⟩ := decomposition_unique g K _ F1 F2 F1' F2'
    (fromF1F2_isDecomposition g K F1 F2) hdec
    (uniquenessAssumptionsOfSpectator hSymm hQ2 hTT heq heT he)
  rfl

/-- **The hadronic tensor has exactly three invariant coefficients.** Under a `SpectatorPlane`
whose two norms have the same sign, with `Q² ≠ 0` and `p_T` non-null, every tensor conserved in
both slots and properly covariant is `fromF1F2 g K F₁ F₂ + c • A` for a unique triple
`(F₁, F₂, c)`, where `A` is a fixed non-zero parity-odd structure. -/
theorem existsUnique_eq_fromF1F2_add_smul {W A : Bilin V} (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (hP : SpectatorPlane g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) (hcov : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) :
    ∃! F : ℝ × ℝ × ℝ, W = fromF1F2 g K F.1 F.2.1 + F.2.2 • A := by
  obtain ⟨F1, F2, c, hW⟩ :=
    exists_eq_fromF1F2_add_smul hSymm hQ2 hP hsign hTT hA hA0 hcov hleft hright
  exact ⟨(F1, F2, c), hW, fun F hF =>
    fromF1F2_add_smul_injective hSymm hQ2 hTT hP.q_orthogonal_e₁ hP.pT_orthogonal_e₁
      hP.e₁_self_ne_zero hP.e₁_orthogonal_e₂ (hA.apply_e₁_e₂_ne_zero hSymm hP hA0)
      (hF.symm.trans hW)⟩

/-- **Characterization of the hadronic tensor.** Under a `SpectatorPlane` whose two norms have
the same sign, with `Q² ≠ 0` and `p_T` non-null, a tensor is the transverse pair plus a
multiple of a fixed non-zero parity-odd structure `A` exactly when it is conserved in both
slots and properly covariant. -/
theorem exists_eq_fromF1F2_add_smul_iff {W A : Bilin V} (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (hP : SpectatorPlane g K)
    (hsign : 0 < g hP.e₁ hP.e₁ * g hP.e₂ hP.e₂)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) :
    (∃ F1 F2 c : ℝ, W = fromF1F2 g K F1 F2 + c • A) ↔
      IsProperLorentzCovariant g K W ∧ (∀ v : V, W K.q v = 0) ∧ ∀ v : V, W v K.q = 0 := by
  refine ⟨?_, fun ⟨hcov, hleft, hright⟩ =>
    exists_eq_fromF1F2_add_smul hSymm hQ2 hP hsign hTT hA hA0 hcov hleft hright⟩
  rintro ⟨F1, F2, c, rfl⟩
  exact ⟨fromF1F2_add_smul_isProperLorentzCovariant hA.proper_covariant F1 F2 c,
    fromF1F2_add_smul_conserved_left hQ2 hA.conserved_left F1 F2 c,
    fromF1F2_add_smul_conserved_right hSymm hQ2 hA.conserved_right F1 F2 c⟩

/-!
## The four-dimensional witness

On Minkowski space `ℝ⁴` at the witness kinematics `kFour` of `Tensors.ParityOdd`, the spectator
plane `spectatorPlaneFour` is orthonormal (`e₁·e₁ = e₂·e₂ = -1`), `Q² = 1` and `p_T·p_T = 1`, so
every hypothesis above holds with `A = aFour = ε(·, ·, p, q)`.
-/

namespace Witness

/-- **The three-coefficient decomposition on Minkowski space.** On the witness kinematics,
every tensor conserved in both slots and properly covariant is
`fromF1F2 gFour kFour F₁ F₂ + c • aFour` for a unique triple `(F₁, F₂, c)`. -/
theorem existsUnique_eq_fromF1F2_add_smul_aFour {W : Bilin (Fin 4 → ℝ)}
    (hcov : IsProperLorentzCovariant gFour kFour W) (hleft : ∀ v, W kFour.q v = 0)
    (hright : ∀ v, W v kFour.q = 0) :
    ∃! F : ℝ × ℝ × ℝ, W = fromF1F2 gFour kFour F.1 F.2.1 + F.2.2 • aFour :=
  existsUnique_eq_fromF1F2_add_smul gFour_isSymm (by simp) spectatorPlaneFour (by simp)
    (by simp) parityOddAssumptions_aFour aFour_ne_zero hcov hleft hright

end Witness

end Hadronic

end Tensors
end DIS
end Scattering
end QFT
end EpsilonEridani
