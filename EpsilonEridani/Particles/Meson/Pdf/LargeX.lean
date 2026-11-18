/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Pdf.Basic
public import EpsilonEridani.Particles.Parton.PDF.LargeX

/-!
# The large-`x` exponent of a meson's valence density, and the counting-rule hypothesis

The exponent with which a meson's valence density vanishes as the momentum fraction approaches
one is not a consequence of the sum rules. Quark-counting arguments with helicity retention
predict that the pion's valence density falls as `(1 - x)^2` at a low reference scale, while
leading-order analyses of Drell–Yan data found a roughly linear fall-off; the exponent is a
hypothesis about the density, not a theorem about it.

This module states it as one. `PseudoscalarMeson.CountingRuleHypothesis M f Q0` says that the
valence density `q(x, Q0) - qbar(x, Q0)` of the flavour of `M`'s valence quark has large-`x`
exponent two (`PDF.HasLargeXExponent`) at the reference scale `Q0`. The hypothesis is then shown
to be independent of the valence and momentum sum rules: there are densities carrying the valence
numbers of `M` and obeying the momentum sum rule, with the density assumptions, both with and
without it (`not_forall_countingRuleHypothesis_of_sumRules`,
`not_forall_not_countingRuleHypothesis_of_sumRules`).

The witnesses are a pair of densities with the same number and momentum moments (the Mellin
moments `n = 0` and `n = 1`) at every species and every scale and with different large-`x`
exponents. The valence model `valenceModelPdf` carries the shape `1 - x` on its populated species
and has exponent one (`hasLargeXExponent_valenceModelPdf`). The counting-rule model
`countingRuleModelPdf` carries instead the shape `(2/3) (1 - x)^2 (1 + 5 x)`, the combination of
the beta shapes `(1 - x)^2` and `x (1 - x)^2` that has the moments `1/2` and `1/6` of `1 - x`
(`mellinMoment_countingRuleModelPdf_of_le_one`), and has exponent two
(`hasLargeXExponent_countingRuleModelPdf`). The sum rules see only those two moments, so they
cannot see the exponent.

## Main definitions

* `PseudoscalarMeson.CountingRuleHypothesis`: the valence density of the valence-quark flavour has
  large-`x` exponent two at a reference scale.
* `PseudoscalarMeson.countingRuleModelPdf`: a density with the number and momentum moments of the
  valence model and large-`x` exponent two.

## Main results

* `PseudoscalarMeson.mellinMoment_countingRuleModelPdf_of_le_one`: the counting-rule model and the
  valence model have the same moments `n = 0` and `n = 1`.
* `PseudoscalarMeson.hasLargeXExponent_valenceModelPdf`,
  `PseudoscalarMeson.hasLargeXExponent_countingRuleModelPdf`: their valence densities have
  exponents one and two.
* `PseudoscalarMeson.not_forall_countingRuleHypothesis_of_sumRules`,
  `PseudoscalarMeson.not_forall_not_countingRuleHypothesis_of_sumRules`: the sum rules neither
  imply nor exclude the counting-rule hypothesis.

## References

* G. R. Farrar and D. R. Jackson, *Pion and nucleon structure functions near x = 1*,
  Phys. Rev. Lett. 35 (1975) 1416.
* E. L. Berger and S. J. Brodsky, *Quark structure functions of mesons and the Drell-Yan
  process*, Phys. Rev. Lett. 42 (1979) 940.
* M. Aicher, A. Schäfer and W. Vogelsang, *Soft-gluon resummation and the valence parton
  distribution function of the pion*, Phys. Rev. Lett. 105 (2010) 252003.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Meson

open Parton

namespace PseudoscalarMeson

variable {Flavor : Type} (M : PseudoscalarMeson Flavor)

/-! ### The counting-rule hypothesis -/

/-- **The counting-rule hypothesis** for a density `f` of the meson `M` at the reference scale
`Q0`: the valence density `q(x, Q0) - qbar(x, Q0)` of the flavour of `M`'s valence quark has
large-`x` exponent two, behaving as `c (1 - x)^2` with `0 < c` as `x → 1⁻`. For the positive pion
this is the prediction `u_v(x) ~ (1 - x)^2` of quark counting with helicity retention. -/
def CountingRuleHypothesis (f : PDF.Pdf (Species Flavor)) (Q0 : ℝ) : Prop :=
  PDF.HasLargeXExponent
    (fun x => f (.quark M.valenceQuark) x Q0 - f (.antiquark M.valenceQuark) x Q0) 2

theorem countingRuleHypothesis_iff (f : PDF.Pdf (Species Flavor)) (Q0 : ℝ) :
    M.CountingRuleHypothesis f Q0 ↔ PDF.HasLargeXExponent
      (fun x => f (.quark M.valenceQuark) x Q0 - f (.antiquark M.valenceQuark) x Q0) 2 :=
  Iff.rfl

variable [DecidableEq Flavor]

/-! ### The valence model has exponent one -/

/-- **The valence density of the valence model has large-`x` exponent one**: for a flavoured meson
it is `2 (1 - x)` on the unit interval, at every scale. -/
theorem hasLargeXExponent_valenceModelPdf (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q2 : ℝ) :
    PDF.HasLargeXExponent (fun x => M.valenceModelPdf (.quark M.valenceQuark) x Q2 -
      M.valenceModelPdf (.antiquark M.valenceQuark) x Q2) 1 := by
  have h := (PDF.hasLargeXExponent_modelPdf (Species Flavor) 0 1
    (.quark M.valenceQuark) Q2).const_mul two_pos
  rw [Nat.cast_one] at h
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [hM]

/-- The valence model violates the counting-rule hypothesis at every scale: its valence density
falls linearly at the endpoint, not quadratically. -/
theorem not_countingRuleHypothesis_valenceModelPdf (hM : M.valenceQuark ≠ M.valenceAntiquark)
    (Q0 : ℝ) : ¬M.CountingRuleHypothesis M.valenceModelPdf Q0 := fun h => by
  have h12 := (M.hasLargeXExponent_valenceModelPdf hM Q0).unique h
  norm_num at h12

/-! ### A model with the same sum rules and exponent two -/

/-- **The counting-rule model of the meson `M`**: the valence model with the shape `1 - x` replaced
by `(2/3) (1 - x)^2 + (10/3) x (1 - x)^2 = (2/3) (1 - x)^2 (1 + 5 x)`, which has the same number
and momentum moments `1/2` and `1/6` (`mellinMoment_countingRuleModelPdf_of_le_one`) but vanishes
quadratically at `x = 1` (`hasLargeXExponent_countingRuleModelPdf`). -/
def countingRuleModelPdf : PDF.Pdf (Species Flavor) :=
  PDF.weight ((2 / 3 : ℝ) • M.valenceModelWeight) (PDF.modelPdf (Species Flavor) 0 2) +
    PDF.weight ((10 / 3 : ℝ) • M.valenceModelWeight) (PDF.modelPdf (Species Flavor) 1 2)

@[simp]
theorem countingRuleModelPdf_apply (s : Species Flavor) (x Q2 : ℝ) :
    M.countingRuleModelPdf s x Q2 =
      M.valenceModelWeight s * (2 / 3 * PDF.modelPdf (Species Flavor) 0 2 s x Q2 +
        10 / 3 * PDF.modelPdf (Species Flavor) 1 2 s x Q2) := by
  simp only [countingRuleModelPdf, Pi.add_apply, PDF.weight_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem smul_valenceModelWeight_nonneg {c : ℝ} (hc : 0 ≤ c) (s : Species Flavor) :
    0 ≤ (c • M.valenceModelWeight) s :=
  mul_nonneg hc (M.valenceModelWeight_nonneg s)

/-- The counting-rule model satisfies the density assumptions `PDF.Assumptions`: it is a sum of
non-negative weightings of model densities. -/
theorem assumptions_countingRuleModelPdf : PDF.Assumptions M.countingRuleModelPdf :=
  ((PDF.assumptions_modelPdf _ 0 2).weight (M.smul_valenceModelWeight_nonneg (by norm_num))).add
    ((PDF.assumptions_modelPdf _ 1 2).weight (M.smul_valenceModelWeight_nonneg (by norm_num)))

/-- **The counting-rule model has the number and momentum moments of the valence model**, at every
species and every scale: the shape `(2/3) (1 - x)^2 (1 + 5 x)` integrates to `1/2` and carries
momentum fraction `1/6`, as `1 - x` does. -/
theorem mellinMoment_countingRuleModelPdf_of_le_one {n : ℕ} (hn : n ≤ 1) (s : Species Flavor)
    (Q2 : ℝ) :
    PDF.mellinMoment M.countingRuleModelPdf n s Q2 = PDF.mellinMoment M.valenceModelPdf n s Q2 := by
  rw [countingRuleModelPdf, PDF.mellinMoment_add
    ((PDF.regularity_modelPdf _ 0 2).weight _) ((PDF.regularity_modelPdf _ 1 2).weight _),
    PDF.mellinMoment_weight, PDF.mellinMoment_weight, PDF.mellinMoment_modelPdf,
    PDF.mellinMoment_modelPdf, mellinMoment_valenceModelPdf]
  simp only [Pi.smul_apply, smul_eq_mul]
  interval_cases n <;> norm_num [Nat.factorial] <;> ring

/-- **The counting-rule model has the valence numbers of its meson**, since the valence numbers
are its moments `n = 0`, which are those of the valence model. -/
theorem hasValenceNumbers_countingRuleModelPdf : M.HasValenceNumbers M.countingRuleModelPdf := by
  rw [hasValenceNumbers_iff]
  intro i Q2
  rw [PDF.valenceNumber_def, M.mellinMoment_countingRuleModelPdf_of_le_one zero_le_one,
    M.mellinMoment_countingRuleModelPdf_of_le_one zero_le_one, ← PDF.valenceNumber_def]
  exact hasValenceNumbers_iff.1 M.hasValenceNumbers_valenceModelPdf i Q2

/-- **The momentum sum rule for the counting-rule model**, the momentum moment of each species
being that of the valence model. -/
theorem sum_mellinMoment_one_countingRuleModelPdf [Fintype Flavor] (Q2 : ℝ) :
    ∑ s, PDF.mellinMoment M.countingRuleModelPdf 1 s Q2 = 1 := by
  simp only [M.mellinMoment_countingRuleModelPdf_of_le_one le_rfl]
  exact M.sum_mellinMoment_one_valenceModelPdf Q2

/-- **The valence density of the counting-rule model has large-`x` exponent two**: for a flavoured
meson it is `(4/3) (1 - x)^2 (1 + 5 x)` on the unit interval, at every scale. -/
theorem hasLargeXExponent_countingRuleModelPdf (hM : M.valenceQuark ≠ M.valenceAntiquark)
    (Q2 : ℝ) :
    PDF.HasLargeXExponent (fun x => M.countingRuleModelPdf (.quark M.valenceQuark) x Q2 -
      M.countingRuleModelPdf (.antiquark M.valenceQuark) x Q2) 2 := by
  have h := ((PDF.hasLargeXExponent_modelPdf (Species Flavor) 0 2 (.quark M.valenceQuark)
    Q2).const_mul (k := 4 / 3) (by norm_num)).add
      ((PDF.hasLargeXExponent_modelPdf (Species Flavor) 1 2 (.quark M.valenceQuark)
        Q2).const_mul (k := 20 / 3) (by norm_num))
  rw [Nat.cast_ofNat] at h
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [countingRuleModelPdf_apply, valenceModelWeight_quark, valenceModelWeight_antiquark,
    hM, ↓reduceIte]
  ring

/-- The counting-rule model satisfies the counting-rule hypothesis at every scale. -/
theorem countingRuleHypothesis_countingRuleModelPdf (hM : M.valenceQuark ≠ M.valenceAntiquark)
    (Q0 : ℝ) : M.CountingRuleHypothesis M.countingRuleModelPdf Q0 :=
  M.hasLargeXExponent_countingRuleModelPdf hM Q0

/-! ### Independence from the sum rules -/

/-- **The sum rules do not imply the counting-rule hypothesis.** For a flavoured meson, some
density with the density assumptions, the valence numbers of the meson and the momentum sum rule
has a valence density that does not fall as `(1 - x)^2`: the valence model. -/
theorem not_forall_countingRuleHypothesis_of_sumRules [Fintype Flavor]
    (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q0 : ℝ) :
    ¬∀ f : PDF.Pdf (Species Flavor), PDF.Assumptions f → M.HasValenceNumbers f →
      (∀ Q2, ∑ s, PDF.mellinMoment f 1 s Q2 = 1) → M.CountingRuleHypothesis f Q0 :=
  fun h => M.not_countingRuleHypothesis_valenceModelPdf hM Q0
    (h _ M.assumptions_valenceModelPdf M.hasValenceNumbers_valenceModelPdf
      M.sum_mellinMoment_one_valenceModelPdf)

/-- **The sum rules do not exclude the counting-rule hypothesis.** For a flavoured meson, some
density with the density assumptions, the valence numbers of the meson and the momentum sum rule
satisfies it: the counting-rule model. -/
theorem not_forall_not_countingRuleHypothesis_of_sumRules [Fintype Flavor]
    (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q0 : ℝ) :
    ¬∀ f : PDF.Pdf (Species Flavor), PDF.Assumptions f → M.HasValenceNumbers f →
      (∀ Q2, ∑ s, PDF.mellinMoment f 1 s Q2 = 1) → ¬M.CountingRuleHypothesis f Q0 :=
  fun h => h _ M.assumptions_countingRuleModelPdf M.hasValenceNumbers_countingRuleModelPdf
    M.sum_mellinMoment_one_countingRuleModelPdf
    (M.countingRuleHypothesis_countingRuleModelPdf hM Q0)

end PseudoscalarMeson

end Meson
end Particles
end EpsilonEridani
