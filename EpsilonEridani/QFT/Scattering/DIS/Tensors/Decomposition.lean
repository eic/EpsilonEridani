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
`A`, and the three coefficients are determined by the tensor. It is the statement that licenses
reading three structure functions off a measured cross section.

No symmetry hypothesis is placed on `W`. The symmetric part comes out as the parity-even pair and
the antisymmetric part as the parity-odd term (`flip_fromF1F2_add_smul`): in the real model this
split is what hermiticity of the complex tensor means.

## Proper covariance on a normalized spectator plane

The input is a `SpectatorPlane` `e₁`, `e₂` of equal norm. Besides the half-turn
`exists_half_turn`, which reverses both spectators, the proper stabilizer then contains a
quarter-turn `e₁ ↦ e₂ ↦ -e₁`, the composite of the reflections in `e₁ - e₂` and in `e₁`
(`exists_quarter_turn`). These two elements alone cut a conserved, properly covariant tensor down
to three components, `W(p_T, p_T)`, `W(e₁, e₁)` and `W(e₁, e₂)`
(`IsProperLorentzCovariant.apply_eq_of_spectatorPair`). For Minkowski space with `p` timelike and
`q` spacelike the spectator plane is spacelike, and any orthonormal basis of it qualifies.

## Main results

- `exists_eq_fromF1F2_add_smul`: every conserved, properly covariant `W` is
  `fromF1F2 g K F₁ F₂ + c • A` for a fixed non-zero parity-odd `A`.
- `fromF1F2_add_smul_injective`: the coefficients `(F₁, F₂, c)` are determined by the tensor.
- `existsUnique_eq_fromF1F2_add_smul`: the two together.
- `exists_eq_fromF1F2_add_smul_iff`: conversely every such combination is conserved and properly
  covariant, so these tensors are exactly the conserved, properly covariant ones.
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
## The quarter-turn
-/

/-- Two orthogonal spectators `u` and `u'` of equal non-zero norm give a kinematic stabilizer
element of determinant one with `u ↦ u' ↦ -u`: the reflection in `u - u'` exchanges `u` and
`u'`, and the reflection in `u` then reverses `u`. -/
lemma exists_quarter_turn (hSymm : g.IsSymm) {u u' : V} (huq : g K.q u = 0)
    (huT : g (pTransverse g K) u = 0) (hu : g u u ≠ 0) (hu'q : g K.q u' = 0)
    (hu'T : g (pTransverse g K) u' = 0) (huu' : g u u' = 0) (hnorm : g u u = g u' u') :
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
  have h₁ := reflect_isKinematicStabilizer g K hSymm _ hu
    (apply_p_eq_zero_of_spectator g K hSymm huq huT) (by rw [hSymm.eq, huq])
  have h₂ := reflect_isKinematicStabilizer g K hSymm _ hdd0
    (apply_p_eq_zero_of_spectator g K hSymm hdq hdT) (by rw [hSymm.eq, hdq])
  -- The reflection in `u - u'` exchanges `u` and `u'`.
  have hc : 2 * (2 * g u u)⁻¹ * g u u = 1 := by field_simp
  have hsu : Bilin.reflect g (u - u') u = u' := by
    have h : g (u - u') u = g u u := by
      rw [map_sub, LinearMap.sub_apply, hu'u, sub_zero]
    rw [Bilin.reflect_apply, h, hdd, hc, one_smul]
    abel
  have hsu' : Bilin.reflect g (u - u') u' = u := by
    have h : g (u - u') u' = -g u u := by
      rw [map_sub, LinearMap.sub_apply, huu', ← hnorm, zero_sub]
    rw [Bilin.reflect_apply, h, hdd, mul_neg, hc, neg_smul, one_smul]
    abel
  refine ⟨Bilin.reflect g u ∘ₗ Bilin.reflect g (u - u'),
    ⟨fun v w => by simp only [LinearMap.comp_apply, h₁.isometry _ _, h₂.isometry _ _],
      by rw [LinearMap.comp_apply, h₂.fixes_p, h₁.fixes_p],
      by rw [LinearMap.comp_apply, h₂.fixes_q, h₁.fixes_q]⟩, ?_, ?_, ?_⟩
  · by_cases hfin : Module.Finite ℝ V
    · rw [LinearMap.det_comp, Bilin.det_reflect g hu, Bilin.det_reflect g hdd0]
      norm_num
    · -- Mathlib defines `LinearMap.det` to be `1` outside finite dimension, so this branch
      -- is vacuous and carries no geometric content.
      exact LinearMap.det_eq_one_of_not_module_finite hfin _
  · rw [LinearMap.comp_apply, hsu, Bilin.reflect_apply_of_orthogonal g _ _ huu']
  · rw [LinearMap.comp_apply, hsu', Bilin.reflect_apply_self g _ hu]

/-- The quarter-turn of a `SpectatorPair` whose directions have equal norm: a kinematic
stabilizer element of determinant one with `e₁ ↦ e₂ ↦ -e₁` (`exists_quarter_turn` applied to
`e₁`, `e₂`). -/
lemma SpectatorPair.exists_quarter_turn (hP : SpectatorPair g K) (hSymm : g.IsSymm)
    (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂) :
    ∃ f : V →ₗ[ℝ] V, IsKinematicStabilizer g K f ∧ LinearMap.det f = 1 ∧
      f hP.e₁ = hP.e₂ ∧ f hP.e₂ = -hP.e₁ :=
  Hadronic.exists_quarter_turn hSymm hP.q_orthogonal_e₁ hP.pT_orthogonal_e₁ hP.e₁_self_ne_zero
    hP.q_orthogonal_e₂ hP.pT_orthogonal_e₂ hP.e₁_orthogonal_e₂ hnorm

/-!
## Three components
-/

/-- **A conserved, properly covariant tensor has three components.** On the span of `p_T`, `q`
and a `SpectatorPair` `e₁`, `e₂` of equal norm, such a tensor is determined by `W(p_T, p_T)`,
`W(e₁, e₁)` and `W(e₁, e₂)`: the half-turn removes the mixed `p_T`-spectator components, and the
quarter-turn makes the spectator block a multiple of the identity plus a multiple of the
`2 × 2` determinant. -/
lemma IsProperLorentzCovariant.apply_eq_of_spectatorPair {W : Bilin V} (hSymm : g.IsSymm)
    (hP : SpectatorPair g K) (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂)
    (hW : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) (a b c₁ c₂ a' b' d₁ d₂ : ℝ) :
    W (a • pTransverse g K + b • K.q + c₁ • hP.e₁ + c₂ • hP.e₂)
        (a' • pTransverse g K + b' • K.q + d₁ • hP.e₁ + d₂ • hP.e₂) =
      a * a' * W (pTransverse g K) (pTransverse g K) + (c₁ * d₁ + c₂ * d₂) * W hP.e₁ hP.e₁
        + (c₁ * d₂ - c₂ * d₁) * W hP.e₁ hP.e₂ := by
  obtain ⟨f, hf, hdet, hf₁, hf₂⟩ := hP.exists_half_turn hSymm
  have hT₁ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₁
  have hT₂ := hW.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₂
  have h₁T : W hP.e₁ (pTransverse g K) = 0 :=
    hW.flip.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₁
  have h₂T : W hP.e₂ (pTransverse g K) = 0 :=
    hW.flip.apply_pTransverse_eq_zero_of_apply_eq_neg hf hdet hf₂
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
`(e₁, e₂)`, for a `SpectatorPlane` of equal norms, are equal. -/
lemma IsProperLorentzCovariant.eq_of_apply_eq {W W' : Bilin V} (hSymm : g.IsSymm)
    (hP : SpectatorPlane g K) (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂)
    (hW : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) (hW' : IsProperLorentzCovariant g K W')
    (hleft' : ∀ v : V, W' K.q v = 0) (hright' : ∀ v : V, W' v K.q = 0)
    (hTT : W (pTransverse g K) (pTransverse g K) = W' (pTransverse g K) (pTransverse g K))
    (h₁₁ : W hP.e₁ hP.e₁ = W' hP.e₁ hP.e₁) (h₁₂ : W hP.e₁ hP.e₂ = W' hP.e₁ hP.e₂) :
    W = W' := by
  refine LinearMap.ext₂ fun v w => ?_
  obtain ⟨a, b, c₁, c₂, rfl⟩ := hP.span v
  obtain ⟨a', b', d₁, d₂, rfl⟩ := hP.span w
  rw [hW.apply_eq_of_spectatorPair hSymm hP.toSpectatorPair hnorm hleft hright,
    hW'.apply_eq_of_spectatorPair hSymm hP.toSpectatorPair hnorm hleft' hright', hTT, h₁₁, h₁₂]

/-!
## The transverse pair plus a parity-odd structure
-/

/-- The transverse pair plus a multiple of a properly covariant structure is properly
covariant. -/
lemma isProperLorentzCovariant_fromF1F2_add_smul {A : Bilin V}
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

/-- **Exchanging the slots reverses only the parity-odd term.** The transverse pair is the
symmetric part of `fromF1F2 g K F1 F2 + c • A` and `c • A` its antisymmetric part. -/
lemma flip_fromF1F2_add_smul {A : Bilin V} (hSymm : g.IsSymm) (hA : A.IsAlt)
    (F1 F2 c : ℝ) :
    (fromF1F2 g K F1 F2 + c • A).flip = fromF1F2 g K F1 F2 - c • A := by
  refine LinearMap.ext₂ fun v w => ?_
  simp only [LinearMap.BilinForm.flip_apply, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, (fromF1F2_isSymm g K hSymm F1 F2).eq w v]
  rw [← hA.neg_eq v w]
  ring

/-- The probe pairs of `UniquenessAssumptions` supplied by a spectator pair: `(e₁, e₁)` sees only
the transverse projector, and `(p_T + e₁, p_T - (p_T·p_T / e₁·e₁) e₁)` sees only
`p_T ⊗ p_T`, which needs `p_T` to be non-null. -/
noncomputable def SpectatorPair.uniquenessAssumptions (hP : SpectatorPair g K)
    (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
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

/-!
## Existence and uniqueness of the three coefficients
-/

/-- **Three structures are enough.** Under a `SpectatorPlane` of equal norms, with `Q² ≠ 0` and
`p_T` non-null, every tensor conserved in both slots and properly covariant is the transverse
pair `fromF1F2 g K F1 F2` plus a multiple of a fixed non-zero parity-odd structure `A`. No
symmetry of `W` is assumed. -/
theorem exists_eq_fromF1F2_add_smul {W A : Bilin V} (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
    (hP : SpectatorPlane g K) (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) (hcov : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) :
    ∃ F1 F2 c : ℝ, W = fromF1F2 g K F1 F2 + c • A := by
  have hA₁₂ := hA.apply_e₁_e₂_ne_zero hSymm hP hA0
  have he₁ := hP.e₁_self_ne_zero
  have hqT : g K.q (pTransverse g K) = 0 := by rw [hSymm.eq, pTransverse_orthogonal_q g K hQ2]
  refine ⟨-(W hP.e₁ hP.e₁ / g hP.e₁ hP.e₁), (W (pTransverse g K) (pTransverse g K)
      - W hP.e₁ hP.e₁ / g hP.e₁ hP.e₁ * g (pTransverse g K) (pTransverse g K))
      / g (pTransverse g K) (pTransverse g K) ^ 2, W hP.e₁ hP.e₂ / A hP.e₁ hP.e₂,
    hcov.eq_of_apply_eq hSymm hP hnorm hleft hright
      (isProperLorentzCovariant_fromF1F2_add_smul hA.proper_covariant _ _ _)
      (fromF1F2_add_smul_conserved_left hQ2 hA.conserved_left _ _ _)
      (fromF1F2_add_smul_conserved_right hSymm hQ2 hA.conserved_right _ _ _) ?_ ?_ ?_⟩ <;>
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, fromF1F2_apply,
    transverseMetric_apply, hA.isAlt.self_eq_zero, hqT, hP.q_orthogonal_e₁,
    hP.q_orthogonal_e₂, hP.pT_orthogonal_e₁, hP.pT_orthogonal_e₂, hP.e₁_orthogonal_e₂,
    mul_zero, zero_add, add_zero, neg_zero] <;>
  field_simp
  ring

/-- **The three coefficients are determined by the tensor.** Under a `SpectatorPlane`, with
`Q² ≠ 0` and `p_T` non-null, the map `(F₁, F₂, c) ↦ fromF1F2 g K F₁ F₂ + c • A` is injective for
a non-zero parity-odd `A`. The parity-odd coefficient is read off on `(e₁, e₂)`, where the
transverse pair vanishes; the other two then follow from `decomposition_unique`. -/
theorem fromF1F2_add_smul_injective {A : Bilin V} (hSymm : g.IsSymm) (hQ2 : g K.q K.q ≠ 0)
    (hP : SpectatorPlane g K) (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0)
    (hA : ParityOddAssumptions g K A) (hA0 : A ≠ 0) :
    Function.Injective fun F : ℝ × ℝ × ℝ => fromF1F2 g K F.1 F.2.1 + F.2.2 • A := by
  rintro ⟨F1, F2, c⟩ ⟨F1', F2', c'⟩ h
  simp only at h
  have h₁₂ := LinearMap.congr_fun₂ h hP.e₁ hP.e₂
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, fromF1F2_apply,
    transverseMetric_apply, hP.q_orthogonal_e₁, hP.pT_orthogonal_e₁, hP.e₁_orthogonal_e₂,
    mul_zero, zero_mul, neg_zero, add_zero, zero_add] at h₁₂
  obtain rfl : c = c' := mul_right_cancel₀ (hA.apply_e₁_e₂_ne_zero hSymm hP hA0) h₁₂
  have hdec : IsF1F2Decomposition g K (fromF1F2 g K F1 F2) F1' F2' := fun v w => by
    have hvw := LinearMap.congr_fun₂ h v w
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, add_left_inj] at hvw
    rw [hvw, fromF1F2_apply]
  obtain ⟨rfl, rfl⟩ := decomposition_unique g K _ F1 F2 F1' F2'
    (fromF1F2_isDecomposition g K F1 F2) hdec (hP.uniquenessAssumptions hSymm hQ2 hTT)
  rfl

/-- **The hadronic tensor has exactly three invariant coefficients.** Under a `SpectatorPlane`
of equal norms, with `Q² ≠ 0` and `p_T` non-null, every tensor conserved in both slots and
properly covariant is `fromF1F2 g K F₁ F₂ + c • A` for a unique triple `(F₁, F₂, c)`, where `A`
is a fixed non-zero parity-odd structure. -/
theorem existsUnique_eq_fromF1F2_add_smul {W A : Bilin V} (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (hP : SpectatorPlane g K) (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) (hcov : IsProperLorentzCovariant g K W) (hleft : ∀ v : V, W K.q v = 0)
    (hright : ∀ v : V, W v K.q = 0) :
    ∃! F : ℝ × ℝ × ℝ, W = fromF1F2 g K F.1 F.2.1 + F.2.2 • A := by
  obtain ⟨F1, F2, c, hW⟩ :=
    exists_eq_fromF1F2_add_smul hSymm hQ2 hP hnorm hTT hA hA0 hcov hleft hright
  exact ⟨(F1, F2, c), hW, fun F hF =>
    fromF1F2_add_smul_injective hSymm hQ2 hP hTT hA hA0 (hF.symm.trans hW)⟩

/-- **Characterization of the hadronic tensor.** Under a `SpectatorPlane` of equal norms, with
`Q² ≠ 0` and `p_T` non-null, a tensor is conserved in both slots and properly covariant exactly
when it is the transverse pair plus a multiple of a fixed non-zero parity-odd structure `A`. -/
theorem exists_eq_fromF1F2_add_smul_iff {W A : Bilin V} (hSymm : g.IsSymm)
    (hQ2 : g K.q K.q ≠ 0) (hP : SpectatorPlane g K) (hnorm : g hP.e₁ hP.e₁ = g hP.e₂ hP.e₂)
    (hTT : g (pTransverse g K) (pTransverse g K) ≠ 0) (hA : ParityOddAssumptions g K A)
    (hA0 : A ≠ 0) :
    (IsProperLorentzCovariant g K W ∧ (∀ v : V, W K.q v = 0) ∧ ∀ v : V, W v K.q = 0) ↔
      ∃ F1 F2 c : ℝ, W = fromF1F2 g K F1 F2 + c • A := by
  refine ⟨fun ⟨hcov, hleft, hright⟩ =>
    exists_eq_fromF1F2_add_smul hSymm hQ2 hP hnorm hTT hA hA0 hcov hleft hright, ?_⟩
  rintro ⟨F1, F2, c, rfl⟩
  exact ⟨isProperLorentzCovariant_fromF1F2_add_smul hA.proper_covariant F1 F2 c,
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
