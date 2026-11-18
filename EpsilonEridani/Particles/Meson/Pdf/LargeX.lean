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
valence density `q(x, Q0) - qbar(x, Q0)` (`PDF.valenceDensity`) of the flavour of `M`'s valence
quark has large-`x` exponent two (`PDF.HasLargeXExponent`) at the reference scale `Q0`. For a
flavoured meson, whose valence quark and valence antiquark have different flavours, the hypothesis
is then shown to be independent of the sum rules: there are densities with the density
assumptions, the valence numbers of `M` and the sum-rule bundle `PDF.SumRuleAssumptions`, both
with and without it (`not_forall_sumRules_imp_countingRuleHypothesis`,
`not_forall_sumRules_imp_not_countingRuleHypothesis`).

The witnesses are a pair of densities with the same number and momentum moments (the Mellin
moments `n = 0` and `n = 1`) at every species and every scale and with different large-`x`
exponents. The valence model `valenceModelPdf` rescales the shape `1 - x` by the species weight
`valenceModelWeight`, and for a flavoured meson its valence density is `2 (1 - x)`, of exponent one
(`hasLargeXExponent_valenceDensity_valenceModelPdf`). The counting-rule model
`countingRuleModelPdf` rescales by the same weight instead the shape `(2/3) (1 - x)^2 (1 + 5 x)`
of `PDF.exponentTwoModelPdf`, whose moments `n = 0` and `n = 1` are the moments `1/2` and `1/6`
of `1 - x` (`mellinMoment_countingRuleModelPdf_eq_mellinMoment_valenceModelPdf_of_le_one`), and
for a flavoured meson its valence density is `(4/3) (1 - x)^2 (1 + 5 x)`, of exponent two
(`hasLargeXExponent_valenceDensity_countingRuleModelPdf`). The sum rules see only those two
moments, so they cannot see the exponent.

## Main definitions

* `PseudoscalarMeson.CountingRuleHypothesis`: the valence density of the valence-quark flavour has
  large-`x` exponent two at a reference scale.
* `PseudoscalarMeson.countingRuleModelPdf`: a density with the number and momentum moments of the
  valence model and large-`x` exponent two.
* `PseudoscalarMeson.sumRuleAssumptionsCountingRuleModelPdf`: its sum-rule bundle.

## Main results

* `PseudoscalarMeson.mellinMoment_countingRuleModelPdf`: the moments of the counting-rule model.
* `PseudoscalarMeson.mellinMoment_countingRuleModelPdf_eq_mellinMoment_valenceModelPdf_of_le_one`:
  the counting-rule model and the valence model have the same moments `n = 0` and `n = 1`.
* `PseudoscalarMeson.valenceDensity_valenceModelPdf`,
  `PseudoscalarMeson.valenceDensity_countingRuleModelPdf`: for a flavoured meson the valence
  densities of the two models are twice their shapes.
* `PseudoscalarMeson.hasLargeXExponent_valenceDensity_valenceModelPdf`,
  `PseudoscalarMeson.hasLargeXExponent_valenceDensity_countingRuleModelPdf`: for a flavoured meson
  their valence densities have exponents one and two.
* `PseudoscalarMeson.not_forall_sumRules_imp_countingRuleHypothesis`,
  `PseudoscalarMeson.not_forall_sumRules_imp_not_countingRuleHypothesis`: for a flavoured meson the
  sum rules neither imply nor exclude the counting-rule hypothesis.

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
  PDF.HasLargeXExponent (PDF.valenceDensity f M.valenceQuark Q0) 2

theorem countingRuleHypothesis_iff (f : PDF.Pdf (Species Flavor)) (Q0 : ℝ) :
    M.CountingRuleHypothesis f Q0 ↔
      PDF.HasLargeXExponent (PDF.valenceDensity f M.valenceQuark Q0) 2 :=
  Iff.rfl

variable [DecidableEq Flavor]

/-! ### The valence model has exponent one -/

/-- For a flavoured meson, the valence density of the valence model is twice the shape `1 - x` on
the unit interval, at every scale: the valence quark has weight two and its antiquark weight
zero. -/
theorem valenceDensity_valenceModelPdf (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q2 x : ℝ) :
    PDF.valenceDensity M.valenceModelPdf M.valenceQuark Q2 x =
      2 * PDF.modelPdf (Species Flavor) 0 1 (.quark M.valenceQuark) x Q2 := by
  simp [hM]

/-- **The valence density of the valence model has large-`x` exponent one**: for a flavoured meson
it is `2 (1 - x)` on the unit interval, at every scale. -/
theorem hasLargeXExponent_valenceDensity_valenceModelPdf
    (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q2 : ℝ) :
    PDF.HasLargeXExponent (PDF.valenceDensity M.valenceModelPdf M.valenceQuark Q2) 1 := by
  have h := (PDF.hasLargeXExponent_modelPdf (Species Flavor) 0 1
    (.quark M.valenceQuark) Q2).const_mul two_pos
  rw [Nat.cast_one] at h
  exact h.congr fun x => (M.valenceDensity_valenceModelPdf hM Q2 x).symm

/-- For a flavoured meson, the valence model violates the counting-rule hypothesis at every scale:
its valence density falls linearly at the endpoint, not quadratically. -/
theorem not_countingRuleHypothesis_valenceModelPdf (hM : M.valenceQuark ≠ M.valenceAntiquark)
    (Q0 : ℝ) : ¬M.CountingRuleHypothesis M.valenceModelPdf Q0 := fun h => by
  have h12 := (M.hasLargeXExponent_valenceDensity_valenceModelPdf hM Q0).unique
    ((M.countingRuleHypothesis_iff _ _).1 h)
  norm_num at h12

/-! ### A model with the same sum rules and exponent two -/

/-- **The counting-rule model of the meson `M`**: the valence model with the shape `1 - x` replaced
by the shape `(2/3) (1 - x)^2 (1 + 5 x)` of `PDF.exponentTwoModelPdf`, at the same species
weights. It has the same number and momentum moments
(`mellinMoment_countingRuleModelPdf_eq_mellinMoment_valenceModelPdf_of_le_one`) but its valence
density vanishes quadratically at `x = 1` (`hasLargeXExponent_valenceDensity_countingRuleModelPdf`).
-/
def countingRuleModelPdf : PDF.Pdf (Species Flavor) :=
  PDF.weight M.valenceModelWeight (PDF.exponentTwoModelPdf (Species Flavor))

@[simp]
theorem countingRuleModelPdf_apply (s : Species Flavor) (x Q2 : ℝ) :
    M.countingRuleModelPdf s x Q2 =
      M.valenceModelWeight s * PDF.exponentTwoModelPdf (Species Flavor) s x Q2 :=
  (rfl)

/-- The counting-rule model satisfies the density assumptions `PDF.Assumptions`: it is a
non-negative weighting, species by species, of a density that does. -/
theorem assumptions_countingRuleModelPdf : PDF.Assumptions M.countingRuleModelPdf :=
  (PDF.assumptions_exponentTwoModelPdf (Species Flavor)).weight M.valenceModelWeight_nonneg

/-- The Mellin moments of the counting-rule model: the species weight times the moment
`4 (2 n + 3) / ((n + 1) (n + 2) (n + 3) (n + 4))` of the shape `(2/3) (1 - x)^2 (1 + 5 x)`. -/
@[simp]
theorem mellinMoment_countingRuleModelPdf (n : ℕ) (s : Species Flavor) (Q2 : ℝ) :
    PDF.mellinMoment M.countingRuleModelPdf n s Q2 =
      M.valenceModelWeight s * (4 * (2 * (n : ℝ) + 3) /
        (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4))) := by
  rw [countingRuleModelPdf, PDF.mellinMoment_weight, PDF.mellinMoment_exponentTwoModelPdf]

/-- **The counting-rule model has the number and momentum moments of the valence model**, at every
species and every scale: the shape `(2/3) (1 - x)^2 (1 + 5 x)` integrates to `1/2` and carries
momentum fraction `1/6`, as `1 - x` does. -/
theorem mellinMoment_countingRuleModelPdf_eq_mellinMoment_valenceModelPdf_of_le_one {n : ℕ}
    (hn : n ≤ 1) (s : Species Flavor) (Q2 : ℝ) :
    PDF.mellinMoment M.countingRuleModelPdf n s Q2 = PDF.mellinMoment M.valenceModelPdf n s Q2 := by
  rw [mellinMoment_countingRuleModelPdf, mellinMoment_valenceModelPdf]
  interval_cases n <;> norm_num

/-- **The counting-rule model has the valence numbers of its meson**, since the valence numbers
are differences of its moments `n = 0`, which are those of the valence model. -/
theorem hasValenceNumbers_countingRuleModelPdf : M.HasValenceNumbers M.countingRuleModelPdf := by
  rw [hasValenceNumbers_iff]
  intro i Q2
  rw [PDF.valenceNumber_def,
    M.mellinMoment_countingRuleModelPdf_eq_mellinMoment_valenceModelPdf_of_le_one zero_le_one,
    M.mellinMoment_countingRuleModelPdf_eq_mellinMoment_valenceModelPdf_of_le_one zero_le_one,
    ← PDF.valenceNumber_def]
  exact hasValenceNumbers_iff.1 M.hasValenceNumbers_valenceModelPdf i Q2

/-- **The momentum sum rule for the counting-rule model**: as in the valence model, the valence
quark, the valence antiquark and the gluon carry a third of the meson's momentum each. The sum
runs over all species, the gluon included. -/
theorem sum_mellinMoment_one_countingRuleModelPdf [Fintype Flavor] (Q2 : ℝ) :
    ∑ s, PDF.mellinMoment M.countingRuleModelPdf 1 s Q2 = 1 :=
  PDF.sum_mellinMoment_one_weight (fun _ _ => by norm_num) M.sum_valenceModelWeight Q2

/-- **The counting-rule model carries the sum-rule bundle**, with the valence targets of the
valence model, each species' target being half its weight. This is the bundle
`PDF.sumRuleAssumptionsWeight` of the shape `(2/3) (1 - x)^2 (1 + 5 x)` at the valence model's
weight, from which `sumRuleAssumptionsValenceModelPdf` also comes. -/
def sumRuleAssumptionsCountingRuleModelPdf [Fintype Flavor] :
    PDF.SumRuleAssumptions M.countingRuleModelPdf :=
  PDF.sumRuleAssumptionsWeight (fun _ _ => by norm_num) (fun _ _ => by norm_num)
    M.sum_valenceModelWeight

@[simp]
theorem sumRuleAssumptionsCountingRuleModelPdf_valenceTarget [Fintype Flavor]
    (s : Species Flavor) :
    (M.sumRuleAssumptionsCountingRuleModelPdf).valenceTarget s = M.valenceModelWeight s / 2 :=
  PDF.sumRuleAssumptionsWeight_valenceTarget _ _ M.sum_valenceModelWeight s

/-- For a flavoured meson, the valence density of the counting-rule model is twice the shape
`(2/3) (1 - x)^2 (1 + 5 x)` on the unit interval, at every scale: the valence quark has weight
two and its antiquark weight zero. -/
theorem valenceDensity_countingRuleModelPdf (hM : M.valenceQuark ≠ M.valenceAntiquark)
    (Q2 x : ℝ) :
    PDF.valenceDensity M.countingRuleModelPdf M.valenceQuark Q2 x =
      2 * PDF.exponentTwoModelPdf (Species Flavor) (.quark M.valenceQuark) x Q2 := by
  simp only [PDF.valenceDensity_apply, countingRuleModelPdf_apply, valenceModelWeight_quark,
    valenceModelWeight_antiquark, hM, ↓reduceIte]
  ring

/-- **The valence density of the counting-rule model has large-`x` exponent two**: for a flavoured
meson it is `(4/3) (1 - x)^2 (1 + 5 x)` on the unit interval, at every scale. -/
theorem hasLargeXExponent_valenceDensity_countingRuleModelPdf
    (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q2 : ℝ) :
    PDF.HasLargeXExponent (PDF.valenceDensity M.countingRuleModelPdf M.valenceQuark Q2) 2 :=
  ((PDF.hasLargeXExponent_exponentTwoModelPdf (Species Flavor) (.quark M.valenceQuark)
    Q2).const_mul two_pos).congr fun x => (M.valenceDensity_countingRuleModelPdf hM Q2 x).symm

/-! ### Independence from the sum rules -/

/-- **The sum rules do not imply the counting-rule hypothesis.** For a flavoured meson, some
density with the density assumptions, the valence numbers of the meson and the sum-rule bundle
has a valence density that does not fall as `(1 - x)^2`: the valence model. -/
theorem not_forall_sumRules_imp_countingRuleHypothesis [Fintype Flavor]
    (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q0 : ℝ) :
    ¬∀ f : PDF.Pdf (Species Flavor), PDF.Assumptions f → M.HasValenceNumbers f →
      PDF.SumRuleAssumptions f → M.CountingRuleHypothesis f Q0 :=
  fun h => M.not_countingRuleHypothesis_valenceModelPdf hM Q0
    (h _ M.assumptions_valenceModelPdf M.hasValenceNumbers_valenceModelPdf
      M.sumRuleAssumptionsValenceModelPdf)

/-- **The sum rules do not exclude the counting-rule hypothesis.** For a flavoured meson, some
density with the density assumptions, the valence numbers of the meson and the sum-rule bundle
satisfies it: the counting-rule model. -/
theorem not_forall_sumRules_imp_not_countingRuleHypothesis [Fintype Flavor]
    (hM : M.valenceQuark ≠ M.valenceAntiquark) (Q0 : ℝ) :
    ¬∀ f : PDF.Pdf (Species Flavor), PDF.Assumptions f → M.HasValenceNumbers f →
      PDF.SumRuleAssumptions f → ¬M.CountingRuleHypothesis f Q0 :=
  fun h => h _ M.assumptions_countingRuleModelPdf M.hasValenceNumbers_countingRuleModelPdf
    M.sumRuleAssumptionsCountingRuleModelPdf
    ((M.countingRuleHypothesis_iff _ _).2
      (M.hasLargeXExponent_valenceDensity_countingRuleModelPdf hM Q0))

end PseudoscalarMeson

end Meson
end Particles
end EpsilonEridani
