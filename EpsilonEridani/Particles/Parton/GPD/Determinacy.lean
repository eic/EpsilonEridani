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
  while their distributions differ (`exists_models_mellinMomentH_eq_and_H_ne`). The
  counterexample is supported in the DGLAP half `0 ≤ x ≤ 1`, so it is not an artefact of the
  central region.

The gap between the two is the reason an extraction of `H` from a finite set of measured moments
is an inverse problem rather than a computation: nothing is wrong with the moments, and nothing
in them pins the distribution down.

## Main results

- `EpsilonEridani.Particles.Parton.GPD.ae_eq_of_forall_mellinMomentGpd_eq`
- `EpsilonEridani.Particles.Parton.GPD.exists_models_mellinMomentH_eq_and_H_ne`

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
`exists_models_mellinMomentH_eq_and_H_ne`. -/
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
differ.

Contrast `ae_eq_of_forall_mellinMomentGpd_eq`, where the whole moment sequence is used. The
witness is supported in `0 ≤ x ≤ 1`, hence entirely inside the DGLAP region at zero skewness, so
the ambiguity is not confined to the central region of `GPD.InErblRegion`. -/
theorem exists_models_mellinMomentH_eq_and_H_ne [Nonempty Flavor] (N : ℕ) :
    ∃ M₁ M₂ : Model Flavor, Assumptions M₁ ∧ Assumptions M₂ ∧
      (∀ n ≤ N, ∀ (i : Flavor) (xi t : ℝ),
        mellinMomentH M₁ n i xi t = mellinMomentH M₂ n i xi t) ∧
      M₁.H ≠ M₂.H := by
  obtain ⟨p, -, -, ⟨x₀, hx₀, hx₀ne⟩, hp⟩ :=
    exists_polynomial_ne_zero_setIntegral_Icc_pow_mul_eq_zero (a := 0) (b := 1)
      zero_lt_one N
  refine ⟨Model.zero Flavor, polynomialModel p Flavor, ?_, assumptions_polynomialModel p Flavor,
    ?_, ?_⟩
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
  · intro hH
    refine hx₀ne ?_
    have h := congrFun (congrFun (congrFun (congrFun hH (Classical.arbitrary Flavor)) x₀) 0) 0
    simpa [Model.zero, polynomialModel, Set.indicator_of_mem hx₀] using h.symm

end GPD
end Parton
end Particles
end EpsilonEridani
