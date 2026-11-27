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
* *Finitely many* moments determine nothing: for every GPD model `M₁` satisfying
  `GPD.Assumptions` and integrable on `[-1, 1]`, and every order `N`, there is a second such
  model `M₂`, obtained by adding a polynomial profile on the quark half
  (`Model.addQuarkPolynomialProfile`), whose moments of order `0, …, N` agree with those of `M₁`
  at every skewness and momentum transfer while, at every physical skewness, the two
  distributions are not even almost everywhere equal on `[-1, 1]`
  (`exists_model_forall_le_mellinMomentH_eq_and_H_not_ae_eq`). At every skewness `|ξ| < 1` they
  already differ at a point of the DGLAP region, so the ambiguity is not confined to the central
  region. No candidate distribution is singled out by finitely many of its moments.

The gap between the two is the reason an extraction of `H` from a finite set of measured moments
is an inverse problem rather than a computation: nothing is wrong with the moments, and nothing
in them pins the distribution down. This is the moment-level counterpart of the non-uniqueness
of GPDs reconstructed from exclusive data discussed by Moffat *et al.* (shadow GPDs) and by
Guo *et al.* (DGLAP-region knowledge up to a D-term); the statements here are proved from the
moment problem alone and make no use of those works' constructions.

## Main results

- `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentGpd_eq`,
  `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentH_eq`,
  `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentE_eq`
- `EpsilonEridani.Particles.Parton.GPD.Model.addQuarkPolynomialProfile`
- `EpsilonEridani.Particles.Parton.GPD.exists_model_forall_le_mellinMomentH_eq_and_H_not_ae_eq`

## References

* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41, §3.1–§3.2 and
  §4.3 (arXiv:hep-ph/0307382), for the support interval `[-1, 1]`, the DGLAP/ERBL regions and
  the Mellin moments `∫_{-1}^{1} dx x^n H(x, ξ, t)`.
* E. Moffat *et al.*, *Shedding light on shadow generalized parton distributions*,
  Phys. Rev. D **108** (2023) 036027 (arXiv:2303.12006).
* Y. Guo, X. Ji, M. G. Santiago, J. Yang and H.-C. Zhang (listing; primary source not
  consulted), *Unraveling Generalized Parton Distributions Through Lorentz Symmetry and
  Partial DGLAP Knowledge*, arXiv:2401.12013.
* N. I. Akhiezer, *The Classical Moment Problem*, Hafner (1965), Chapter 2, for the Hausdorff
  moment problem underlying `EpsilonEridani.Mathematics.MomentDeterminacy`.

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

/-- The model `M` with the polynomial profile `p` added to its `H` on the quark half
`0 ≤ x ≤ 1`, at every flavour, physical skewness `|ξ| ≤ 1` and momentum transfer. Outside
physical skewness and outside `[0, 1]` its `H` is that of `M`, and its `E` is that of `M`, so
`GPD.Assumptions` is preserved (`Model.assumptions_addQuarkPolynomialProfile`). Its moments are
those of `M` plus the moments of `p` over `[0, 1]` (`mellinMomentH_addQuarkPolynomialProfile`),
so taking `p` in the kernel of `polynomialMomentsIcc 0 1 N` gives the counterexamples of
`exists_model_forall_le_mellinMomentH_eq_and_H_not_ae_eq`. -/
def Model.addQuarkPolynomialProfile (M : Model Flavor) (p : Polynomial ℝ) : Model Flavor where
  H := fun i x xi t =>
    M.H i x xi t + if 1 < |xi| then 0 else (Icc (0 : ℝ) 1).indicator (fun y => p.eval y) x
  E := M.E

/-- Unfolding lemma for the `H` of `Model.addQuarkPolynomialProfile`, whose body is not
exposed. -/
@[simp]
lemma Model.addQuarkPolynomialProfile_H (M : Model Flavor) (p : Polynomial ℝ) (i : Flavor)
    (x xi t : ℝ) :
    (M.addQuarkPolynomialProfile p).H i x xi t =
      M.H i x xi t + if 1 < |xi| then 0 else (Icc (0 : ℝ) 1).indicator (fun y => p.eval y) x :=
  (rfl)

/-- Unfolding lemma for the `E` of `Model.addQuarkPolynomialProfile`: it is the `E` of `M`. -/
@[simp]
lemma Model.addQuarkPolynomialProfile_E (M : Model Flavor) (p : Polynomial ℝ) (i : Flavor)
    (x xi t : ℝ) : (M.addQuarkPolynomialProfile p).E i x xi t = M.E i x xi t :=
  (rfl)

/-- Outside physical skewness `Model.addQuarkPolynomialProfile` leaves `H` unchanged. -/
lemma Model.addQuarkPolynomialProfile_H_of_one_lt_abs (M : Model Flavor) (p : Polynomial ℝ)
    {i : Flavor} {x xi t : ℝ} (hxi : 1 < |xi|) :
    (M.addQuarkPolynomialProfile p).H i x xi t = M.H i x xi t := by
  simp [hxi]

/-- Outside the quark half `[0, 1]` `Model.addQuarkPolynomialProfile` leaves `H` unchanged. -/
lemma Model.addQuarkPolynomialProfile_H_of_notMem_Icc (M : Model Flavor) (p : Polynomial ℝ)
    {i : Flavor} {x xi t : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    (M.addQuarkPolynomialProfile p).H i x xi t = M.H i x xi t := by
  simp [Set.indicator_of_notMem hx]

/-- On the quark half `[0, 1]` and at physical skewness, `Model.addQuarkPolynomialProfile` adds
`p` itself to `H`, at every flavour and momentum transfer. -/
lemma Model.addQuarkPolynomialProfile_H_of_mem_Icc_of_abs_le_one (M : Model Flavor)
    (p : Polynomial ℝ) {i : Flavor} {x xi t : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) (hxi : |xi| ≤ 1) :
    (M.addQuarkPolynomialProfile p).H i x xi t = M.H i x xi t + p.eval x := by
  simp [not_lt.mpr hxi, Set.indicator_of_mem hx]

/-- `Model.addQuarkPolynomialProfile` preserves the standing support and skewness
assumptions. -/
lemma Model.assumptions_addQuarkPolynomialProfile {M : Model Flavor} (hM : Assumptions M)
    (p : Polynomial ℝ) : Assumptions (M.addQuarkPolynomialProfile p) where
  supportH i x xi t hx := by
    have hx' : x ∉ Icc (0 : ℝ) 1 := fun h => by rcases hx with hx | hx <;> linarith [h.1, h.2]
    rw [M.addQuarkPolynomialProfile_H_of_notMem_Icc p hx', hM.supportH i x xi t hx]
  supportE i x xi t hx := by
    rw [Model.addQuarkPolynomialProfile_E, hM.supportE i x xi t hx]
  skewnessBound i x xi t hxi := by
    rw [M.addQuarkPolynomialProfile_H_of_one_lt_abs p hxi, Model.addQuarkPolynomialProfile_E]
    exact hM.skewnessBound i x xi t hxi

/-- `Model.addQuarkPolynomialProfile` preserves integrability of `H` on the support interval:
the added term is a polynomial cut off to the compact interval `[0, 1]`, or zero. -/
lemma Model.integrableOn_addQuarkPolynomialProfile_H {M : Model Flavor} (p : Polynomial ℝ)
    {i : Flavor} {xi t : ℝ} (hM : IntegrableOn (fun x => M.H i x xi t) (Icc (-1) 1)) :
    IntegrableOn (fun x => (M.addQuarkPolynomialProfile p).H i x xi t) (Icc (-1) 1) := by
  by_cases hxi : 1 < |xi|
  · exact hM.congr_fun (fun x _ => (M.addQuarkPolynomialProfile_H_of_one_lt_abs p hxi).symm)
      measurableSet_Icc
  · have hp : Integrable ((Icc (0 : ℝ) 1).indicator fun y => p.eval y) :=
      p.continuous.integrableOn_Icc.integrable_indicator measurableSet_Icc
    exact (hM.add hp.integrableOn).congr_fun (fun x _ => by simp [hxi]) measurableSet_Icc

/-- At physical skewness the moments of `Model.addQuarkPolynomialProfile M p` are those of `M`
plus the moments of `p` over the quark half `[0, 1]`. -/
lemma mellinMomentH_addQuarkPolynomialProfile {M : Model Flavor} (p : Polynomial ℝ) (n : ℕ)
    {i : Flavor} {xi t : ℝ} (hM : IntegrableOn (fun x => M.H i x xi t) (Icc (-1) 1))
    (hxi : |xi| ≤ 1) :
    mellinMomentH (M.addQuarkPolynomialProfile p) n i xi t
      = mellinMomentH M n i xi t + ∫ x in Icc (0 : ℝ) 1, x ^ n * p.eval x := by
  have hpoint : ∀ x : ℝ, x ^ n * (M.addQuarkPolynomialProfile p).H i x xi t
      = x ^ n * M.H i x xi t + (Icc (0 : ℝ) 1).indicator (fun y => y ^ n * p.eval y) x := by
    intro x
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · rw [M.addQuarkPolynomialProfile_H_of_mem_Icc_of_abs_le_one p hx hxi,
        Set.indicator_of_mem hx, mul_add]
    · rw [M.addQuarkPolynomialProfile_H_of_notMem_Icc p hx, Set.indicator_of_notMem hx, add_zero]
  have hind : IntegrableOn ((Icc (0 : ℝ) 1).indicator fun y => y ^ n * p.eval y) (Icc (-1) 1) :=
    ((integrableOn_Icc_pow_mul p.continuous.integrableOn_Icc n).integrable_indicator
      measurableSet_Icc).integrableOn
  rw [mellinMomentH_eq_integral, mellinMomentH_eq_integral]
  simp_rw [hpoint]
  rw [integral_add (integrableOn_Icc_pow_mul hM n) hind, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_self_of_subset_right (Icc_subset_Icc (by norm_num) le_rfl)]

/-- Outside physical skewness the moments of `Model.addQuarkPolynomialProfile M p` are those
of `M`. -/
lemma mellinMomentH_addQuarkPolynomialProfile_of_one_lt_abs (M : Model Flavor)
    (p : Polynomial ℝ) (n : ℕ) {i : Flavor} {xi t : ℝ} (hxi : 1 < |xi|) :
    mellinMomentH (M.addQuarkPolynomialProfile p) n i xi t = mellinMomentH M n i xi t := by
  simp only [mellinMomentH_eq_integral, M.addQuarkPolynomialProfile_H_of_one_lt_abs p hxi]

/-- **No finite set of Mellin moments determines a GPD.** For every GPD model `M₁` satisfying
`GPD.Assumptions` with `H` integrable on the support interval at every flavour, skewness and
momentum transfer, and every order `N`, there is a second such model `M₂` whose moments of order
`0, …, N` agree with those of `M₁` at every flavour, every skewness and every momentum transfer,
and whose distribution `H` nevertheless, at every flavour, every physical skewness `|ξ| ≤ 1` and
every momentum transfer, fails to agree with that of `M₁` almost everywhere on the support
interval.

The two models therefore satisfy every hypothesis of `ae_eq_of_forall_mellinMomentH_eq` except
the agreement of the moments of order above `N`, and the failure is exactly the negation of its
conclusion: they are not identified by the almost-everywhere relation that all the moments do
force. The last clause locates the disagreement in the DGLAP region `|ξ| < |x|` at every skewness
`|ξ| < 1`, so the ambiguity is not confined to the central region of `GPD.InErblRegion`, where
the D-term of `GPD.Ambiguity` lives.

The witness is `Model.addQuarkPolynomialProfile M₁ p` for a nonzero `p` of degree at most
`N + 1` whose moments of order `0, …, N` on `[0, 1]` vanish. -/
theorem exists_model_forall_le_mellinMomentH_eq_and_H_not_ae_eq {M₁ : Model Flavor}
    (hM₁ : Assumptions M₁)
    (hint : ∀ (i : Flavor) (xi t : ℝ), IntegrableOn (fun x => M₁.H i x xi t) (Icc (-1) 1))
    (N : ℕ) :
    ∃ M₂ : Model Flavor, Assumptions M₂ ∧
      (∀ (i : Flavor) (xi t : ℝ), IntegrableOn (fun x => M₂.H i x xi t) (Icc (-1) 1)) ∧
      (∀ n ≤ N, ∀ (i : Flavor) (xi t : ℝ),
        mellinMomentH M₁ n i xi t = mellinMomentH M₂ n i xi t) ∧
      (∀ (i : Flavor) (xi t : ℝ), |xi| ≤ 1 →
        ¬ (fun x => M₁.H i x xi t) =ᵐ[volume.restrict (Icc (-1) 1)] fun x => M₂.H i x xi t) ∧
      ∀ (i : Flavor) (xi t : ℝ), |xi| < 1 →
        ∃ x, InDglapRegion x xi ∧ M₁.H i x xi t ≠ M₂.H i x xi t := by
  obtain ⟨p, hp, -, hp0, hmom⟩ :=
    exists_polynomial_not_ae_eq_zero_forall_le_setIntegral_Icc_pow_mul_eq_zero (a := 0) (b := 1)
      zero_lt_one N
  -- Wherever the two profiles agree on the quark half at physical skewness, `p` vanishes.
  have heval : ∀ (i : Flavor) (x xi t : ℝ), x ∈ Icc (0 : ℝ) 1 → |xi| ≤ 1 →
      M₁.H i x xi t = (M₁.addQuarkPolynomialProfile p).H i x xi t → p.eval x = 0 :=
    fun i x xi t hx hxi h => by
      rw [M₁.addQuarkPolynomialProfile_H_of_mem_Icc_of_abs_le_one p hx hxi] at h
      linarith
  refine ⟨M₁.addQuarkPolynomialProfile p, Model.assumptions_addQuarkPolynomialProfile hM₁ p,
    fun i xi t => Model.integrableOn_addQuarkPolynomialProfile_H p (hint i xi t), ?_, ?_, ?_⟩
  · intro n hn i xi t
    rcases le_or_gt |xi| 1 with hxi | hxi
    · rw [mellinMomentH_addQuarkPolynomialProfile p n (hint i xi t) hxi, hmom n hn, add_zero]
    · rw [mellinMomentH_addQuarkPolynomialProfile_of_one_lt_abs M₁ p n hxi]
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
