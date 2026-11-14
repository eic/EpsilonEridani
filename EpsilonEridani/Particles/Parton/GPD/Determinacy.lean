/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.MomentDeterminacy
public import EpsilonEridani.Particles.Parton.GPD.Moments

/-!

# What the Mellin moments of a GPD determine

Polynomiality constrains the Mellin moments `∫_{-1}^{1} dx x^n H(x, ξ, t)` of a generalized
parton distribution. This module answers the converse question, which is the one that matters
for extracting a distribution from data: how much of `H` do its moments know?

Two answers, and they are opposite.

* At fixed skewness and momentum transfer, the *whole sequence* of moments determines
  `x ↦ H(x, ξ, t)` almost everywhere on the support interval `[-1, 1]`
  (`ae_eq_of_forall_mellinMomentGpd_eq`, and for the components of a model
  `ae_eq_of_forall_mellinMomentH_eq` and `ae_eq_of_forall_mellinMomentE_eq`). The moment sequence
  is therefore a faithful coordinate system on the distribution, and integrability on `[-1, 1]` is
  the only hypothesis needed beyond the moments themselves — in particular the two distributions
  need not be continuous.
* *Finitely many* moments determine nothing: for every order `N` there are two GPD models,
  `Model.zero` and a `Model.ofPolynomial`, both satisfying `GPD.Assumptions` and integrable on
  `[-1, 1]`, whose moments of order `0, …, N` agree at every skewness and momentum transfer while,
  at every physical skewness, their distributions are not even almost everywhere equal on `[-1, 1]`
  (`exists_models_forall_le_mellinMomentH_eq_and_H_not_ae_eq`). At every skewness `|ξ| < 1` they
  already differ at a point of the DGLAP region, so the ambiguity is not confined to the central
  region.

The gap between the two is the reason an extraction of `H` from a finite set of measured moments
is an inverse problem rather than a computation: nothing is wrong with the moments, and nothing
in them pins the distribution down.

## Main results

- `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentGpd_eq`,
  `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentH_eq`,
  `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentE_eq`
- `EpsilonEridani.Particles.Parton.GPD.Model.ofPolynomial`
- `EpsilonEridani.Particles.Parton.GPD.exists_models_forall_le_mellinMomentH_eq_and_H_not_ae_eq`

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

Stated for a bare `GPD.Gpd`; `ae_eq_of_forall_mellinMomentH_eq` and
`ae_eq_of_forall_mellinMomentE_eq` are the two components of a `GPD.Model`.

The integrability hypothesis is not implied by `GPD.Assumptions`, which postulates support but
no regularity, so it is carried explicitly. -/
theorem ae_eq_of_forall_mellinMomentGpd_eq {H₁ H₂ : Gpd Flavor} {i : Flavor} {xi t : ℝ}
    (h₁ : IntegrableOn (fun x => H₁ i x xi t) (Icc (-1) 1))
    (h₂ : IntegrableOn (fun x => H₂ i x xi t) (Icc (-1) 1))
    (hmom : ∀ n : ℕ, mellinMomentGpd H₁ n i xi t = mellinMomentGpd H₂ n i xi t) :
    (fun x => H₁ i x xi t) =ᵐ[volume.restrict (Icc (-1) 1)] fun x => H₂ i x xi t :=
  ae_eq_of_forall_setIntegral_Icc_pow_mul_eq h₁ h₂ fun n => by
    simpa only [mellinMomentGpd_eq_integral] using hmom n

/-- **The `H` component of a GPD model is determined by its Mellin moments**, almost everywhere
on `[-1, 1]` at fixed flavour, skewness and momentum transfer. -/
theorem ae_eq_of_forall_mellinMomentH_eq {M₁ M₂ : Model Flavor} {i : Flavor} {xi t : ℝ}
    (h₁ : IntegrableOn (fun x => M₁.H i x xi t) (Icc (-1) 1))
    (h₂ : IntegrableOn (fun x => M₂.H i x xi t) (Icc (-1) 1))
    (hmom : ∀ n : ℕ, mellinMomentH M₁ n i xi t = mellinMomentH M₂ n i xi t) :
    (fun x => M₁.H i x xi t) =ᵐ[volume.restrict (Icc (-1) 1)] fun x => M₂.H i x xi t :=
  ae_eq_of_forall_mellinMomentGpd_eq h₁ h₂ hmom

/-- **The `E` component of a GPD model is determined by its Mellin moments**, almost everywhere
on `[-1, 1]` at fixed flavour, skewness and momentum transfer. -/
theorem ae_eq_of_forall_mellinMomentE_eq {M₁ M₂ : Model Flavor} {i : Flavor} {xi t : ℝ}
    (h₁ : IntegrableOn (fun x => M₁.E i x xi t) (Icc (-1) 1))
    (h₂ : IntegrableOn (fun x => M₂.E i x xi t) (Icc (-1) 1))
    (hmom : ∀ n : ℕ, mellinMomentE M₁ n i xi t = mellinMomentE M₂ n i xi t) :
    (fun x => M₁.E i x xi t) =ᵐ[volume.restrict (Icc (-1) 1)] fun x => M₂.E i x xi t :=
  ae_eq_of_forall_mellinMomentGpd_eq h₁ h₂ hmom

/-! ### Finitely many moments determine nothing -/

/-- The GPD model whose `H` is the polynomial profile `p` on the quark half `0 ≤ x ≤ 1`, at every
flavour, physical skewness and momentum transfer, and which vanishes outside physical skewness so
that `GPD.Assumptions` holds (`Model.assumptions_ofPolynomial`); its `E` is zero
(`Model.ofPolynomial_E`). Its moments are the moments of `p` over `[0, 1]`
(`mellinMomentH_ofPolynomial`), so taking `p` in the kernel of `polynomialMomentsIcc 0 1 N` gives
the counterexamples of `exists_models_forall_le_mellinMomentH_eq_and_H_not_ae_eq`. -/
def Model.ofPolynomial (p : Polynomial ℝ) (Flavor : Type) : Model Flavor where
  H := fun _ x xi _ => if 1 < |xi| then 0 else (Icc (0 : ℝ) 1).indicator (fun y => p.eval y) x
  E := fun _ _ _ _ => 0

@[simp]
lemma Model.ofPolynomial_E (p : Polynomial ℝ) (Flavor : Type) (i : Flavor) (x xi t : ℝ) :
    (Model.ofPolynomial p Flavor).E i x xi t = 0 :=
  (rfl)

/-- `Model.ofPolynomial p` satisfies the standing support and skewness assumptions. -/
lemma Model.assumptions_ofPolynomial (p : Polynomial ℝ) (Flavor : Type) :
    Assumptions (Model.ofPolynomial p Flavor) where
  supportH := by
    intro i x xi t hx
    have hx' : x ∉ Icc (0 : ℝ) 1 := by
      rcases hx with hx | hx
      · exact fun h => absurd h.1 (by linarith)
      · exact fun h => absurd h.2 (by linarith)
    simp [Model.ofPolynomial, Set.indicator_of_notMem hx']
  supportE i x xi t _ := Model.ofPolynomial_E p Flavor i x xi t
  skewnessBound := by intro i x xi t hxi; simp [Model.ofPolynomial, hxi]

/-- At physical skewness the profile of `Model.ofPolynomial p` on the quark half `[0, 1]` is `p`
itself, at every flavour and momentum transfer. -/
lemma Model.ofPolynomial_H_of_mem_Icc (p : Polynomial ℝ) (Flavor : Type) (i : Flavor)
    {x xi : ℝ} (t : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hxi : |xi| ≤ 1) :
    (Model.ofPolynomial p Flavor).H i x xi t = p.eval x := by
  simp [Model.ofPolynomial, not_lt.mpr hxi, Set.indicator_of_mem hx]

/-- The `H` of `Model.ofPolynomial p` is integrable in `x` at every flavour, skewness and
momentum transfer: it is a polynomial cut off to the compact interval `[0, 1]`, or zero. -/
lemma Model.integrable_ofPolynomial_H (p : Polynomial ℝ) (Flavor : Type) (i : Flavor)
    (xi t : ℝ) : Integrable (fun x => (Model.ofPolynomial p Flavor).H i x xi t) := by
  by_cases hxi : 1 < |xi|
  · simp [Model.ofPolynomial, hxi]
  · simpa [Model.ofPolynomial, hxi] using
      p.continuous.integrableOn_Icc.integrable_indicator (measurableSet_Icc (a := (0 : ℝ)) (b := 1))

/-- The moments of `Model.ofPolynomial p` at physical skewness are the moments of `p` over the
quark half `[0, 1]`. -/
lemma mellinMomentH_ofPolynomial (p : Polynomial ℝ) (Flavor : Type) (n : ℕ)
    (i : Flavor) {xi : ℝ} (t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentH (Model.ofPolynomial p Flavor) n i xi t
      = ∫ x in Icc (0 : ℝ) 1, x ^ n * p.eval x := by
  have hxi' : ¬ 1 < |xi| := not_lt.mpr hxi
  have hpoint : ∀ x : ℝ, x ^ n * (Model.ofPolynomial p Flavor).H i x xi t
      = (Icc (0 : ℝ) 1).indicator (fun y => y ^ n * p.eval y) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · simp [Model.ofPolynomial, hxi', Set.indicator_of_mem hx]
    · simp [Model.ofPolynomial, hxi', Set.indicator_of_notMem hx]
  rw [mellinMomentH_eq_integral]
  simp_rw [hpoint]
  rw [setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_self_of_subset_right (Icc_subset_Icc (by norm_num) le_rfl)]

/-- **No finite set of Mellin moments determines a GPD.** For every order `N` there are two GPD
models, both satisfying `GPD.Assumptions` and both with `H` integrable on the support interval at
every flavour, skewness and momentum transfer, whose moments of order `0, …, N` agree at every
flavour, every skewness and every momentum transfer, and whose distributions `H` nevertheless,
at every flavour, every physical skewness `|ξ| ≤ 1` and every momentum transfer, fail to agree
almost everywhere on the support interval.

The two models therefore satisfy every hypothesis of `ae_eq_of_forall_mellinMomentH_eq` except
the agreement of the moments of order above `N`, and the failure is exactly the negation of its
conclusion: they are not identified by the almost-everywhere relation that all the moments do
force. The last clause locates the disagreement in the DGLAP region `|ξ| < |x|` at every skewness
`|ξ| < 1`, so the ambiguity is not confined to the central region of `GPD.InErblRegion`, where
the D-term of `GPD.Ambiguity` lives. -/
theorem exists_models_forall_le_mellinMomentH_eq_and_H_not_ae_eq (N : ℕ) :
    ∃ M₁ M₂ : Model Flavor, Assumptions M₁ ∧ Assumptions M₂ ∧
      (∀ (i : Flavor) (xi t : ℝ), IntegrableOn (fun x => M₁.H i x xi t) (Icc (-1) 1) ∧
        IntegrableOn (fun x => M₂.H i x xi t) (Icc (-1) 1)) ∧
      (∀ n ≤ N, ∀ (i : Flavor) (xi t : ℝ),
        mellinMomentH M₁ n i xi t = mellinMomentH M₂ n i xi t) ∧
      (∀ (i : Flavor) (xi t : ℝ), |xi| ≤ 1 →
        ¬ (fun x => M₁.H i x xi t) =ᵐ[volume.restrict (Icc (-1) 1)] fun x => M₂.H i x xi t) ∧
      ∀ (i : Flavor) (xi t : ℝ), |xi| < 1 →
        ∃ x, InDglapRegion x xi ∧ M₁.H i x xi t ≠ M₂.H i x xi t := by
  obtain ⟨p, hp, -, hp0, hmom⟩ :=
    exists_polynomial_ne_zero_forall_le_setIntegral_Icc_pow_mul_eq_zero (a := 0) (b := 1)
      zero_lt_one N
  -- Wherever the two profiles agree on the quark half at physical skewness, `p` vanishes.
  have heval : ∀ (i : Flavor) (x xi t : ℝ), x ∈ Icc (0 : ℝ) 1 → |xi| ≤ 1 →
      (Model.zero Flavor).H i x xi t = (Model.ofPolynomial p Flavor).H i x xi t →
        p.eval x = 0 := fun i x xi t hx hxi h => by
    rw [← Model.ofPolynomial_H_of_mem_Icc p Flavor i t hx hxi, ← h, Model.zero_H]
  refine ⟨Model.zero Flavor, Model.ofPolynomial p Flavor, Model.assumptions_zero Flavor,
    Model.assumptions_ofPolynomial p Flavor,
    fun i xi t => ⟨by simp, (Model.integrable_ofPolynomial_H p Flavor i xi t).integrableOn⟩,
    ?_, ?_, ?_⟩
  · intro n hn i xi t
    rw [mellinMomentH_eq_integral]
    simp only [Model.zero_H, mul_zero, integral_zero]
    rcases le_or_gt |xi| 1 with hxi | hxi
    · rw [mellinMomentH_ofPolynomial p Flavor n i t hxi]
      exact (hmom n hn).symm
    · rw [mellinMomentH_eq_integral]
      simp [Model.ofPolynomial, hxi]
  · -- Agreement almost everywhere on `[-1, 1]` would force `p` to vanish almost everywhere on
    -- the quark half, which `p` does not.
    intro i xi t hxi hae
    have hsub : volume.restrict (Icc (0 : ℝ) 1) ≤ volume.restrict (Icc (-1 : ℝ) 1) :=
      Measure.restrict_mono (Icc_subset_Icc (by norm_num) le_rfl) le_rfl
    refine hp0 ?_
    filter_upwards [hae.filter_mono (ae_mono hsub), ae_restrict_mem measurableSet_Icc]
      with x hx hxmem
    rw [Pi.zero_apply]
    exact heval i x xi t hxmem hxi hx
  · -- The points of `(|ξ|, 1]` lie in the DGLAP region, and the nonzero `p` cannot vanish at
    -- almost all of them.
    intro i xi t hxi
    by_contra hcon
    push Not at hcon
    refine not_eval_ae_eq_zero_of_ne_zero hxi hp ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      Measure.ae_ne (volume.restrict (Icc |xi| 1)) |xi|] with x hxmem hxne
    have hlt : |xi| < x := lt_of_le_of_ne hxmem.1 (Ne.symm hxne)
    have hx0 : 0 < x := (abs_nonneg xi).trans_lt hlt
    have hdglap : InDglapRegion x xi := by
      simp only [InDglapRegion, abs_of_pos hx0]
      exact ⟨hlt, hxmem.2⟩
    rw [Pi.zero_apply]
    exact heval i x xi t ⟨hx0.le, hxmem.2⟩ hxi.le (hcon x hdglap)

end GPD
end Parton
end Particles
end EpsilonEridani
