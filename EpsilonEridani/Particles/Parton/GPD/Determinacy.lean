/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.MomentDeterminacy
public import EpsilonEridani.Particles.Parton.GPD.Ambiguity
public import EpsilonEridani.Particles.Parton.GPD.Moments

/-!

# What the Mellin moments of a GPD determine

Polynomiality constrains the Mellin moments `∫_{-1}^{1} dx x^n H(x, ξ, t)` of a generalized
parton distribution. This module answers the converse question, which is the one that matters
for extracting a distribution from data: how much of `H` do its moments know?

Two answers, and they are opposite.

* At fixed skewness and momentum transfer, the *whole sequence* of moments determines
  `x ↦ H(x, ξ, t)` almost everywhere on the support interval `[-1, 1]`
  (`ae_eq_of_forall_mellinMomentGpd_eq`). The moment sequence is therefore a faithful
  coordinate system on the distribution, and integrability on `[-1, 1]` is the only hypothesis
  needed beyond the moments themselves — in particular the two distributions need not be
  continuous.
* *Finitely many* moments determine nothing: for every order `N` there are two GPD models,
  both satisfying `GPD.Assumptions`, whose moments of order `0, …, N` agree at every skewness
  while their distributions are not even almost everywhere equal on `[-1, 1]`
  (`exists_models_mellinMomentH_eq_and_H_not_ae_eq`). They already differ at a point of the
  DGLAP region at zero skewness, so the ambiguity is not an artefact of the central region.

The gap between the two is the reason an extraction of `H` from a finite set of measured moments
is an inverse problem rather than a computation: nothing is wrong with the moments, and nothing
in them pins the distribution down.

## Main results

- `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentGpd_eq`
- `EpsilonEridani.Particles.Parton.GPD.exists_models_mellinMomentH_eq_and_H_not_ae_eq`

-/

public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-- **A GPD is determined by its Mellin moments.** At fixed flavour, skewness and momentum
transfer, two distributions integrable on the support interval `[-1, 1]` with the same moments
of every order agree almost everywhere there.

Stated for a bare `GPD.Gpd`, so it applies to each component of a `GPD.Model` — `mellinMomentH M`
and `mellinMomentE M` are `mellinMomentGpd` of `M.H` and `M.E` by definition.

The integrability hypothesis is not implied by `GPD.Assumptions`, which postulates support but
no regularity, so it is carried explicitly. -/
theorem ae_eq_of_forall_mellinMomentGpd_eq {H₁ H₂ : Gpd Flavor} {i : Flavor} {xi t : ℝ}
    (h₁ : IntegrableOn (fun x => H₁ i x xi t) (Icc (-1) 1))
    (h₂ : IntegrableOn (fun x => H₂ i x xi t) (Icc (-1) 1))
    (hmom : ∀ n : ℕ, mellinMomentGpd H₁ n i xi t = mellinMomentGpd H₂ n i xi t) :
    (fun x => H₁ i x xi t) =ᵐ[volume.restrict (Icc (-1) 1)] fun x => H₂ i x xi t :=
  ae_eq_of_forall_setIntegral_Icc_pow_mul_eq h₁ h₂ hmom

/-! ### Finitely many moments determine nothing -/

/-- A GPD model carrying a single polynomial profile on the quark half `0 ≤ x ≤ 1`, switched off
outside physical skewness so that `GPD.Assumptions` holds. Used to exhibit the counterexamples of
`exists_models_mellinMomentH_eq_and_H_not_ae_eq`. -/
private def polynomialModel (p : Polynomial ℝ) (Flavor : Type) : Model Flavor where
  H := fun _ x xi _ => if 1 < |xi| then 0 else (Icc (0 : ℝ) 1).indicator (fun y => p.eval y) x
  E := fun _ _ _ _ => 0

private lemma assumptions_polynomialModel (p : Polynomial ℝ) (Flavor : Type) :
    Assumptions (polynomialModel p Flavor) where
  supportH := by
    intro i x xi t hx
    have hx' : x ∉ Icc (0 : ℝ) 1 := by
      rcases hx with hx | hx
      · exact fun h => absurd h.1 (by linarith)
      · exact fun h => absurd h.2 (by linarith)
    simp [polynomialModel, Set.indicator_of_notMem hx']
  supportE := by intro i x xi t _; rfl
  skewnessBound := by intro i x xi t hxi; simp [polynomialModel, hxi]

/-- At zero skewness and zero momentum transfer the profile of `polynomialModel p` on the quark
half `[0, 1]` is `p` itself. -/
private lemma polynomialModel_H_of_mem_Icc (p : Polynomial ℝ) (Flavor : Type) (i : Flavor)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    (polynomialModel p Flavor).H i x 0 0 = p.eval x := by
  simp [polynomialModel, Set.indicator_of_mem hx]

/-- The moments of `polynomialModel p` at physical skewness are the moments of `p` over the
quark half `[0, 1]`. -/
private lemma mellinMomentH_polynomialModel (p : Polynomial ℝ) (Flavor : Type) (n : ℕ)
    (i : Flavor) {xi : ℝ} (t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentH (polynomialModel p Flavor) n i xi t
      = ∫ x in Icc (0 : ℝ) 1, x ^ n * p.eval x := by
  have hxi' : ¬ 1 < |xi| := not_lt.mpr hxi
  have hpoint : ∀ x : ℝ, x ^ n * (polynomialModel p Flavor).H i x xi t
      = (Icc (0 : ℝ) 1).indicator (fun y => y ^ n * p.eval y) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp [polynomialModel, hxi', Set.indicator_of_mem hx]
    · simp [polynomialModel, hxi', Set.indicator_of_notMem hx]
  rw [mellinMomentH, mellinMomentGpd]
  simp_rw [hpoint]
  rw [setIntegral_indicator measurableSet_Icc]
  congr 1
  rw [Set.Icc_inter_Icc]
  norm_num

/-- **No finite set of Mellin moments determines a GPD.** For every order `N` there are two GPD
models, both satisfying `GPD.Assumptions`, whose moments of order `0, …, N` agree at every
flavour, every skewness and every momentum transfer, and whose distributions `H` nevertheless
fail to agree almost everywhere on the support interval, at every flavour.

The failure is exactly the negation of `ae_eq_of_forall_mellinMomentGpd_eq`, where the whole
moment sequence is used: the two models are not identified by the almost-everywhere relation
that all the moments do force. The last clause locates the disagreement in the DGLAP region at
zero skewness, so the ambiguity is not an artefact of the central region of
`GPD.InErblRegion`, where the D-term and the shadow GPDs of `GPD.Ambiguity` live. -/
theorem exists_models_mellinMomentH_eq_and_H_not_ae_eq [Nonempty Flavor] (N : ℕ) :
    ∃ M₁ M₂ : Model Flavor, Assumptions M₁ ∧ Assumptions M₂ ∧
      (∀ n ≤ N, ∀ (i : Flavor) (xi t : ℝ),
        mellinMomentH M₁ n i xi t = mellinMomentH M₂ n i xi t) ∧
      (∀ i : Flavor, ¬ (fun x => M₁.H i x 0 0) =ᵐ[volume.restrict (Icc (-1) 1)]
        fun x => M₂.H i x 0 0) ∧
      ∀ i : Flavor, ∃ x, InDglapRegion x 0 ∧ M₁.H i x 0 0 ≠ M₂.H i x 0 0 := by
  obtain ⟨p, -, -, hp0, hp⟩ :=
    exists_polynomial_ne_zero_setIntegral_Icc_pow_mul_eq_zero (a := 0) (b := 1)
      zero_lt_one N
  refine ⟨Model.zero Flavor, polynomialModel p Flavor, ?_, assumptions_polynomialModel p Flavor,
    ?_, ?_, ?_⟩
  · exact { supportH := by intro i x xi t _; rfl
            supportE := by intro i x xi t _; rfl
            skewnessBound := by intro i x xi t _; exact ⟨rfl, rfl⟩ }
  · intro n hn i xi t
    have hleft : mellinMomentH (Model.zero Flavor) n i xi t = 0 := by
      rw [mellinMomentH, mellinMomentGpd]
      simp
    rw [hleft]
    rcases le_or_gt |xi| 1 with hxi | hxi
    · rw [mellinMomentH_polynomialModel p Flavor n i t hxi]
      exact (hp n hn).symm
    · rw [mellinMomentH, mellinMomentGpd]
      simp [polynomialModel, hxi]
  · -- Agreement almost everywhere on `[-1, 1]` would force `p` to vanish almost everywhere on
    -- the quark half, which `p` does not.
    intro i hae
    have hsub : volume.restrict (Icc (0 : ℝ) 1) ≤ volume.restrict (Icc (-1 : ℝ) 1) :=
      Measure.restrict_mono (Icc_subset_Icc (by norm_num) le_rfl) le_rfl
    refine hp0 ?_
    filter_upwards [hae.filter_mono (ae_mono hsub), ae_restrict_mem measurableSet_Icc]
      with x hx hxmem
    rw [← polynomialModel_H_of_mem_Icc p Flavor i hxmem, ← hx, Model.zero_H]
    rfl
  · -- The same computation at a single point of the DGLAP region: every nonzero `x ∈ [0, 1]`
    -- lies there at zero skewness, and `p` cannot vanish at almost all of them.
    intro i
    by_contra hcon
    push Not at hcon
    refine hp0 ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      Measure.ae_ne (volume.restrict (Icc (0 : ℝ) 1)) 0] with x hxmem hx0
    have hxpos : 0 < x := lt_of_le_of_ne hxmem.1 (Ne.symm hx0)
    have hdglap : InDglapRegion x 0 := by
      simp only [InDglapRegion, abs_zero, abs_of_pos hxpos]
      exact ⟨hxpos, hxmem.2⟩
    rw [← polynomialModel_H_of_mem_Icc p Flavor i hxmem, ← hcon x hdglap, Model.zero_H]
    rfl

end GPD
end Parton
end Particles
end EpsilonEridani
