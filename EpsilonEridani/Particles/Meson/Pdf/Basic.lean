/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.Particles.Parton.PDF.ChargeConjugation
public import EpsilonEridani.Particles.Parton.PDF.Isospin
public import EpsilonEridani.Particles.Parton.PDF.Model

/-!
# Parton densities of a pseudoscalar meson and their valence sum rules

A parton density of a pseudoscalar meson is a collinear density
`EpsilonEridani.Particles.Parton.PDF.Pdf` over the parton species
`EpsilonEridani.Particles.Parton.Species Flavor` of the meson's flavour type, satisfying the
general `PDF.Assumptions`; the support condition, the non-negativity on the unit interval and
the integrability of the Mellin moments are then the statements of that bundle and are not
restated here. The momentum sum rule and the sum rule for each species are likewise the
species-level bundle `PDF.SumRuleAssumptions`, instantiated rather than restated.

What is specific to a meson is the *valence assignment*. The net number of quarks of flavour `i`
that a density carries at a scale is `PDF.valenceNumber`, and `PseudoscalarMeson.valenceNumber` is
the net valence number the meson's valence pair prescribes. A density has the valence numbers of a
meson, `PseudoscalarMeson.HasValenceNumbers`, when the two agree at every flavour and every scale.
For a flavoured meson this is the conjunction of exactly three sum rules
(`hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark`): one net quark of the valence quark's
flavour, one net antiquark of the valence antiquark's flavour, and no net quarks of any other
flavour. When the valence flavours coincide it is the vanishing of every valence integral
(`hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark`), as for any density whose quark and
antiquark densities of each flavour agree on the unit interval
(`hasValenceNumbers_of_valenceQuark_eq_valenceAntiquark_of_quark_eq_antiquark`). Against a density
that carries the sum-rule bundle `PDF.SumRuleAssumptions`, the assignment is a condition on the
bundle's valence targets alone (`hasValenceNumbers_iff_valenceTarget`, the meson instance of the
general `PDF.forall_valenceNumber_eq_iff_valenceTarget`), so it suffices to check it at one scale,
the valence numbers being the scale-independent target differences of
`PDF.valenceNumber_eq_sub_valenceTarget`.

Two consequences fix what the assignment means. Both are statements at a single scale, so they are
stated for a density carrying the meson's valence numbers at that scale, with the forms for
`HasValenceNumbers` as corollaries. The charge-weighted valence numbers of the density are the
charge difference of the valence pair (`sum_mul_pdfValenceNumber`), which recovers the meson's
electric charge whenever the charge is the one carried by that pair
(`sum_mul_pdfValenceNumber_eq_charge`), and the valence content of a flavoured meson is determined
by any density carrying its valence numbers
(`valenceQuark_eq_and_valenceAntiquark_eq_of_pdfValenceNumber_eq`); the three sum rules themselves
fix the valence integrals.

That the assignment is consistent with the sum-rule bundle — that the two can be imposed
together — is exhibited rather than assumed. `PseudoscalarMeson.valenceModelPdf` is the
`PDF.weight` rescaling that carries the shape `2 (1 - x)` on the valence quark, on the valence
antiquark and on the gluon and vanishes on every other species; it satisfies `PDF.Assumptions`, it
has the valence numbers of its meson, and its three populated species carry a third of the momentum
each, so the momentum sum rule holds with the gluon included. Its sum-rule bundle is the general
one of a rescaled shape `1 - x`, `PDF.sumRuleAssumptionsWeightModelPdfZeroOne`. Conjugating the
meson conjugates the model (`chargeConj_valenceModelPdf`).

An assignment `F` of a density to each meson is charge-conjugation covariant,
`IsChargeConjCovariant F`, when the densities of the charge-conjugate meson are the charge
conjugates of the meson's densities; the valence model is
(`isChargeConjCovariant_valenceModelPdf`). Exchanging two flavours `i`, `j` of the meson
(`PseudoscalarMeson.swapFlavor`) likewise exchanges them over the species in its valence model
(`swapFlavor_valenceModelPdf`), and the two exchanges together preserve the valence assignment
(`hasValenceNumbers_swapFlavor_speciesSwapFlavor_iff`). An assignment `F` with
`F (M.swapFlavor e i j) = PDF.speciesSwapFlavor i j (F M)` for every meson `M` is
`IsSwapFlavorCovariant e i j F`, covariant under the exchange of `i` and `j` at the charges `e`;
the valence model is (`isSwapFlavorCovariant_valenceModelPdf`). For a meson whose exchange of
`i` and `j` is its charge conjugate, the two covariances together make its densities invariant
under charge conjugation composed with the exchange
(`IsSwapFlavorCovariant.eq_chargeConj_speciesSwapFlavor`).

## Main definitions

* `PseudoscalarMeson.HasValenceNumbers`: the density carries the meson's net valence numbers at
  every scale.
* `PseudoscalarMeson.valenceModelWeight`, `PseudoscalarMeson.valenceModelPdf`: the weight the
  valence model gives each parton species, and the valence model density of a meson.
* `PseudoscalarMeson.sumRuleAssumptionsValenceModelPdf`: the sum-rule bundle
  `PDF.SumRuleAssumptions` of the valence model.
* `IsChargeConjCovariant`, `IsSwapFlavorCovariant`: covariance of an assignment of densities to
  mesons under charge conjugation and under the exchange of two flavours.

## Main results

* `PseudoscalarMeson.hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark`: the three valence
  sum rules of a flavoured meson.
* `PseudoscalarMeson.hasValenceNumbers_iff_valenceTarget`: against the sum-rule bundle,
  the valence assignment is a condition on the valence targets.
* `PseudoscalarMeson.sum_mul_pdfValenceNumber_eq_charge`: the charge-weighted valence numbers at a
  scale sum to the meson's charge.
* `PseudoscalarMeson.valenceQuark_eq_and_valenceAntiquark_eq_of_pdfValenceNumber_eq`: the valence
  content of a flavoured meson is determined by any density carrying its valence numbers at one
  scale.
* `PseudoscalarMeson.hasValenceNumbers_valenceModelPdf`,
  `PseudoscalarMeson.sum_mellinMoment_one_valenceModelPdf`: the valence model has the valence
  numbers of its meson and obeys the momentum sum rule.

## References

* J. S. Conway et al., *Experimental study of muon pairs produced by 252-GeV pions on tungsten*,
  Phys. Rev. D 39 (1989) 92: what a pion density is fitted to.
* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), ch. 6.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Meson

open Parton

namespace PseudoscalarMeson

variable {Flavor : Type} [DecidableEq Flavor]

/-! ### The valence assignment -/

/-- The density `f` of the parton species over `Flavor` **has the valence numbers of the meson
`M`** when, at every flavour and every scale, the net number of quarks of that flavour it carries
is the net valence number of that flavour in `M`. For a flavoured meson this is the conjunction of
the three valence sum rules of `hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark`. -/
def HasValenceNumbers (M : PseudoscalarMeson Flavor) (f : PDF.Pdf (Species Flavor)) : Prop :=
  ∀ i Q2, PDF.valenceNumber f i Q2 = (M.valenceNumber i : ℝ)

variable {M M' : PseudoscalarMeson Flavor} {f : PDF.Pdf (Species Flavor)}

/-- The valence assignment spelled out, flavour by flavour and scale by scale. -/
theorem hasValenceNumbers_iff :
    M.HasValenceNumbers f ↔ ∀ i Q2, PDF.valenceNumber f i Q2 = (M.valenceNumber i : ℝ) :=
  Iff.rfl

/-- **The three valence sum rules of a flavoured meson.** A density has the valence numbers of a
meson whose valence quark and valence antiquark differ exactly when it carries one net quark of
the valence quark's flavour, one net antiquark of the valence antiquark's flavour — a net quark
number `-1` — and no net quarks of any other flavour, at every scale. -/
theorem hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark (M : PseudoscalarMeson Flavor)
    (f : PDF.Pdf (Species Flavor)) (h : M.valenceQuark ≠ M.valenceAntiquark) :
    M.HasValenceNumbers f ↔
      (∀ Q2, PDF.valenceNumber f M.valenceQuark Q2 = 1) ∧
        (∀ Q2, PDF.valenceNumber f M.valenceAntiquark Q2 = -1) ∧
          ∀ i, i ≠ M.valenceQuark → i ≠ M.valenceAntiquark →
            ∀ Q2, PDF.valenceNumber f i Q2 = 0 := by
  refine ⟨fun hf => ⟨fun Q2 => ?_, fun Q2 => ?_, fun i hq ha Q2 => ?_⟩, fun hf i Q2 => ?_⟩
  · rw [hf M.valenceQuark Q2, M.valenceNumber_valenceQuark h, Int.cast_one]
  · rw [hf M.valenceAntiquark Q2, M.valenceNumber_valenceAntiquark h, Int.cast_neg, Int.cast_one]
  · rw [hf i Q2, M.valenceNumber_apply_eq_zero_of_ne hq ha, Int.cast_zero]
  · by_cases hq : i = M.valenceQuark
    · subst hq
      rw [hf.1 Q2, M.valenceNumber_valenceQuark h, Int.cast_one]
    · by_cases ha : i = M.valenceAntiquark
      · subst ha
        rw [hf.2.1 Q2, M.valenceNumber_valenceAntiquark h, Int.cast_neg, Int.cast_one]
      · rw [hf.2.2 i hq ha Q2, M.valenceNumber_apply_eq_zero_of_ne hq ha, Int.cast_zero]

/-- **The valence assignment in terms of the bundle's valence targets.** For a density carrying
the bundle, having the valence numbers of `M` is a condition on the bundle's valence targets
alone: the target of the quark of each flavour minus that of its antiquark is the net valence
number of that flavour. In particular the assignment constrains no other datum of the bundle. That
the two can be imposed together at all is
`sumRuleAssumptionsValenceModelPdf`. This is the meson instance of
`PDF.forall_valenceNumber_eq_iff_valenceTarget`. -/
theorem hasValenceNumbers_iff_valenceTarget [Fintype Flavor] (M : PseudoscalarMeson Flavor)
    {f : PDF.Pdf (Species Flavor)} (h : PDF.SumRuleAssumptions f) :
    M.HasValenceNumbers f ↔
      ∀ i, h.valenceTarget (.quark i) - h.valenceTarget (.antiquark i)
        = (M.valenceNumber i : ℝ) :=
  PDF.forall_valenceNumber_eq_iff_valenceTarget h _

/-- **Charge conjugation.** The charge-conjugate density has the valence numbers of the
charge-conjugate meson exactly when the density has those of the meson: conjugating the hadron and
conjugating its densities are the same operation on the valence assignment. -/
@[simp]
theorem hasValenceNumbers_chargeConj_iff (M : PseudoscalarMeson Flavor)
    (f : PDF.Pdf (Species Flavor)) :
    M.chargeConj.HasValenceNumbers (PDF.chargeConj f) ↔ M.HasValenceNumbers f := by
  simp only [hasValenceNumbers_iff, PDF.valenceNumber_chargeConj, chargeConj_valenceNumber,
    Pi.neg_apply, Int.cast_neg, neg_inj]

/-- **Exchanging two flavours.** Exchanging the flavours `i` and `j` in both the meson and the
density preserves the valence assignment: the exchanged density has the valence numbers of the
exchanged meson exactly when the density has those of the meson. -/
@[simp]
theorem hasValenceNumbers_swapFlavor_speciesSwapFlavor_iff (M : PseudoscalarMeson Flavor)
    (e : Flavor → ℝ) (i j : Flavor) (f : PDF.Pdf (Species Flavor)) :
    (M.swapFlavor e i j).HasValenceNumbers (PDF.speciesSwapFlavor i j f)
      ↔ M.HasValenceNumbers f := by
  simp only [hasValenceNumbers_iff, PDF.valenceNumber_speciesSwapFlavor,
    swapFlavor_valenceNumber, Function.comp_apply]
  exact ⟨fun h k Q2 => by simpa using h (Equiv.swap i j k) Q2, fun h k Q2 => h _ Q2⟩

/-- **The charge-weighted valence integrals.** The valence numbers of any density carrying the
meson's net valence numbers at the scale `Q2`, weighted by arbitrary flavour charges, sum there to
the charge of the valence quark minus that of the valence antiquark. -/
theorem sum_mul_pdfValenceNumber [Fintype Flavor] {Q2 : ℝ}
    (hf : ∀ i, PDF.valenceNumber f i Q2 = (M.valenceNumber i : ℝ)) (e : Flavor → ℝ) :
    ∑ i, e i * PDF.valenceNumber f i Q2 = e M.valenceQuark - e M.valenceAntiquark := by
  simp only [hf]
  exact_mod_cast M.sum_mul_valenceNumber e

/-- **The meson charge from the valence integrals.** For a meson whose charge is the one carried
by its valence pair, the valence numbers of any density carrying the meson's net valence numbers at
the scale `Q2`, weighted by the quark charges, sum there to the meson's charge. -/
theorem sum_mul_pdfValenceNumber_eq_charge [Fintype Flavor] {e : Flavor → ℝ} {Q2 : ℝ}
    (hf : ∀ i, PDF.valenceNumber f i Q2 = (M.valenceNumber i : ℝ)) (he : M.IsChargeConsistent e) :
    ∑ i, e i * PDF.valenceNumber f i Q2 = M.charge :=
  (sum_mul_pdfValenceNumber hf e).trans ((M.isChargeConsistent_iff e).1 he).symm

/-- `sum_mul_pdfValenceNumber` at every scale, for a density carrying the meson's valence
assignment. -/
theorem HasValenceNumbers.sum_mul_pdfValenceNumber [Fintype Flavor]
    (hf : M.HasValenceNumbers f) (e : Flavor → ℝ) (Q2 : ℝ) :
    ∑ i, e i * PDF.valenceNumber f i Q2 = e M.valenceQuark - e M.valenceAntiquark :=
  PseudoscalarMeson.sum_mul_pdfValenceNumber (hf · Q2) e

/-- `sum_mul_pdfValenceNumber_eq_charge` at every scale, for a density carrying the meson's valence
assignment. -/
theorem HasValenceNumbers.sum_mul_pdfValenceNumber_eq_charge [Fintype Flavor] {e : Flavor → ℝ}
    (hf : M.HasValenceNumbers f) (he : M.IsChargeConsistent e) (Q2 : ℝ) :
    ∑ i, e i * PDF.valenceNumber f i Q2 = M.charge :=
  PseudoscalarMeson.sum_mul_pdfValenceNumber_eq_charge (hf · Q2) he

/-- **The net valence numbers of a meson are determined by any density carrying them.** Two mesons
whose net valence numbers one density carries at a common scale have the same net valence
numbers. -/
theorem valenceNumber_eq_of_pdfValenceNumber_eq {Q2 : ℝ}
    (hM : ∀ i, PDF.valenceNumber f i Q2 = (M.valenceNumber i : ℝ))
    (hM' : ∀ i, PDF.valenceNumber f i Q2 = (M'.valenceNumber i : ℝ)) :
    M.valenceNumber = M'.valenceNumber := by
  funext i
  exact Int.cast_injective ((hM i).symm.trans (hM' i))

/-- **The valence content of a flavoured meson is determined by its densities.** Any density
carrying, at a common scale, the net valence numbers of a flavoured meson and of a second meson
forces the two to share their valence quark and valence antiquark. -/
theorem valenceQuark_eq_and_valenceAntiquark_eq_of_pdfValenceNumber_eq {Q2 : ℝ}
    (hM : ∀ i, PDF.valenceNumber f i Q2 = (M.valenceNumber i : ℝ))
    (hM' : ∀ i, PDF.valenceNumber f i Q2 = (M'.valenceNumber i : ℝ))
    (h : M.valenceQuark ≠ M.valenceAntiquark) :
    M.valenceQuark = M'.valenceQuark ∧ M.valenceAntiquark = M'.valenceAntiquark :=
  M.valenceQuark_eq_and_valenceAntiquark_eq_of_valenceNumber_eq M'
    (valenceNumber_eq_of_pdfValenceNumber_eq hM hM') h

/-- `valenceNumber_eq_of_pdfValenceNumber_eq` for two mesons whose valence assignments one density
carries. -/
theorem valenceNumber_eq_of_hasValenceNumbers (hM : M.HasValenceNumbers f)
    (hM' : M'.HasValenceNumbers f) : M.valenceNumber = M'.valenceNumber :=
  valenceNumber_eq_of_pdfValenceNumber_eq (hM · 0) (hM' · 0)

/-- `valenceQuark_eq_and_valenceAntiquark_eq_of_pdfValenceNumber_eq` for two mesons whose valence
assignments one density carries. -/
theorem valenceQuark_eq_and_valenceAntiquark_eq_of_hasValenceNumbers
    (hM : M.HasValenceNumbers f) (hM' : M'.HasValenceNumbers f)
    (h : M.valenceQuark ≠ M.valenceAntiquark) :
    M.valenceQuark = M'.valenceQuark ∧ M.valenceAntiquark = M'.valenceAntiquark :=
  valenceQuark_eq_and_valenceAntiquark_eq_of_pdfValenceNumber_eq (hM · 0) (hM' · 0) h

/-- **The flavour-neutral case.** A density has the valence numbers of a meson whose valence quark
and valence antiquark share a flavour exactly when every valence integral vanishes, those valence
numbers all being zero. Only the valence integrals vanish: the individual quark and antiquark
densities need not. -/
theorem hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark (M : PseudoscalarMeson Flavor)
    (f : PDF.Pdf (Species Flavor)) (h : M.valenceQuark = M.valenceAntiquark) :
    M.HasValenceNumbers f ↔ ∀ i Q2, PDF.valenceNumber f i Q2 = 0 := by
  have hM : M.valenceNumber = 0 := M.valenceNumber_eq_zero_iff.2 h
  simp only [hasValenceNumbers_iff, hM, Pi.zero_apply, Int.cast_zero]

/-- A density whose quark and antiquark densities of each flavour coincide on the unit interval at
every scale has the valence numbers of every meson whose valence quark and valence antiquark share
a flavour: a case of `hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark`. -/
theorem hasValenceNumbers_of_valenceQuark_eq_valenceAntiquark_of_quark_eq_antiquark
    (M : PseudoscalarMeson Flavor) {f : PDF.Pdf (Species Flavor)}
    (h : M.valenceQuark = M.valenceAntiquark)
    (hf : ∀ i Q2, Set.EqOn (f (.quark i) · Q2) (f (.antiquark i) · Q2) (Set.Icc 0 1)) :
    M.HasValenceNumbers f :=
  (M.hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark f h).2
    fun i Q2 => PDF.valenceNumber_eq_zero_of_quark_eq_antiquark (hf i Q2)

/-- A charge-conjugation invariant density has the valence numbers of every meson whose valence
quark and valence antiquark share a flavour: the C-invariant case of
`hasValenceNumbers_of_valenceQuark_eq_valenceAntiquark_of_quark_eq_antiquark`, through
`PDF.valenceNumber_eq_zero_of_chargeConj_eq`. -/
theorem hasValenceNumbers_of_valenceQuark_eq_valenceAntiquark_of_chargeConj_eq
    (M : PseudoscalarMeson Flavor) {f : PDF.Pdf (Species Flavor)}
    (h : M.valenceQuark = M.valenceAntiquark)
    (hf : PDF.chargeConj f = f) : M.HasValenceNumbers f :=
  (M.hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark f h).2
    fun i Q2 => PDF.valenceNumber_eq_zero_of_chargeConj_eq hf i Q2

/-! ### A valence model density

The valence assignment and the sum-rule bundle `PDF.SumRuleAssumptions` can be imposed on one
density at once.
`valenceModelPdf` is the witness: the `EpsilonEridani.Particles.Parton.PDF.weight` rescaling of the
shape `1 - x` of `EpsilonEridani.Particles.Parton.PDF.modelPdf` that carries `2 (1 - x)` on the
valence quark, the valence antiquark and the gluon, and nothing on any other species. -/

/-- The weight the valence model of `M` gives each parton species: two on the quark of the valence
quark's flavour, on the antiquark of the valence antiquark's flavour, and on the gluon, and zero on
every other species. -/
def valenceModelWeight (M : PseudoscalarMeson Flavor) : Species Flavor → ℝ
  | .quark i => if i = M.valenceQuark then 2 else 0
  | .antiquark i => if i = M.valenceAntiquark then 2 else 0
  | .gluon => 2

variable (M)

@[simp]
theorem valenceModelWeight_quark (i : Flavor) :
    M.valenceModelWeight (.quark i) = if i = M.valenceQuark then 2 else 0 := (rfl)

@[simp]
theorem valenceModelWeight_antiquark (i : Flavor) :
    M.valenceModelWeight (.antiquark i) = if i = M.valenceAntiquark then 2 else 0 := (rfl)

@[simp]
theorem valenceModelWeight_gluon : M.valenceModelWeight (Species.gluon) = 2 := (rfl)

theorem valenceModelWeight_nonneg (s : Species Flavor) : 0 ≤ M.valenceModelWeight s := by
  cases s with
  | quark i => rw [valenceModelWeight_quark]; split_ifs <;> norm_num
  | antiquark i => rw [valenceModelWeight_antiquark]; split_ifs <;> norm_num
  | gluon => rw [valenceModelWeight_gluon]; norm_num

/-- The weight of the charge-conjugate meson is the weight of the meson at the conjugate species:
conjugating the meson exchanges the valence quark with the valence antiquark, and `Species.conj`
exchanges the species that carry them. -/
@[simp]
theorem chargeConj_valenceModelWeight :
    M.chargeConj.valenceModelWeight = M.valenceModelWeight ∘ Species.conj := by
  funext s
  cases s with
  | quark i => rw [valenceModelWeight_quark, Function.comp_apply, Species.conj_quark,
      valenceModelWeight_antiquark, chargeConj_valenceQuark]
  | antiquark i => rw [valenceModelWeight_antiquark, Function.comp_apply, Species.conj_antiquark,
      valenceModelWeight_quark, chargeConj_valenceAntiquark]
  | gluon => rw [valenceModelWeight_gluon, Function.comp_apply, Species.conj_gluon,
      valenceModelWeight_gluon]

/-- The weights of the valence model sum to six over all species: two each for the valence quark,
the valence antiquark and the gluon, whether or not the valence flavours coincide. -/
@[simp]
theorem sum_valenceModelWeight [Fintype Flavor] : ∑ s, M.valenceModelWeight s = 6 := by
  rw [Species.sum_univ]
  norm_num

/-- **A valence model density of the meson `M`**: the shape `2 (1 - x)` on the quark of the valence
quark's flavour, on the antiquark of the valence antiquark's flavour and on the gluon, and zero on
every other species, at every scale. It satisfies the density assumptions
`PDF.Assumptions` (`assumptions_valenceModelPdf`), has the valence numbers of `M`
(`hasValenceNumbers_valenceModelPdf`) and obeys the momentum sum rule
(`sum_mellinMoment_one_valenceModelPdf`), its three populated species carrying a third of the
momentum each. -/
def valenceModelPdf (M : PseudoscalarMeson Flavor) : PDF.Pdf (Species Flavor) :=
  PDF.weight M.valenceModelWeight (PDF.modelPdf (Species Flavor) 0 1)

@[simp]
theorem valenceModelPdf_apply (s : Species Flavor) (x Q2 : ℝ) :
    M.valenceModelPdf s x Q2 = M.valenceModelWeight s * PDF.modelPdf (Species Flavor) 0 1 s x Q2 :=
  (rfl)

/-- The valence model satisfies the density assumptions `PDF.Assumptions`: it is a non-negative
weighting, species by species, of a density that does. -/
theorem assumptions_valenceModelPdf : PDF.Assumptions M.valenceModelPdf :=
  (PDF.assumptions_modelPdf (Species Flavor) 0 1).weight M.valenceModelWeight_nonneg

/-- **The valence model of the charge-conjugate meson is the charge conjugate of the valence
model.** Conjugating the hadron and conjugating its densities agree on the valence model, the
flavour-independent shape being invariant and the weight conjugating by
`chargeConj_valenceModelWeight`. -/
@[simp]
theorem chargeConj_valenceModelPdf :
    M.chargeConj.valenceModelPdf = PDF.chargeConj M.valenceModelPdf := by
  rw [valenceModelPdf, valenceModelPdf, PDF.chargeConj_weight, PDF.chargeConj_eq_comap,
    PDF.comap_modelPdf, chargeConj_valenceModelWeight]

/-- The weight of the meson with two flavours exchanged is the weight of the meson at the species
with those flavours exchanged. -/
@[simp]
theorem swapFlavor_valenceModelWeight (e : Flavor → ℝ) (i j : Flavor) :
    (M.swapFlavor e i j).valenceModelWeight
      = M.valenceModelWeight ∘ Species.map (Equiv.swap i j) := by
  funext s
  cases s <;> simp [Equiv.swap_apply_eq_iff]

/-- **The valence model of the meson with two flavours exchanged is the valence model with those
flavours exchanged over the species**: the shape is flavour-independent and the weight relabels by
`swapFlavor_valenceModelWeight`. At the light-quark charges and up, down this is the isospin
covariance of the valence model, whatever the quark masses. -/
@[simp]
theorem swapFlavor_valenceModelPdf (e : Flavor → ℝ) (i j : Flavor) :
    (M.swapFlavor e i j).valenceModelPdf = PDF.speciesSwapFlavor i j M.valenceModelPdf := by
  rw [valenceModelPdf, valenceModelPdf, PDF.speciesSwapFlavor_weight,
    PDF.speciesSwapFlavor_eq_comap, PDF.comap_modelPdf, swapFlavor_valenceModelWeight]

/-- The Mellin moments of the valence model: the species weight times the moment
`1 / ((n + 1) (n + 2))` of the shape `1 - x`. -/
@[simp]
theorem mellinMoment_valenceModelPdf (n : ℕ) (s : Species Flavor) (Q2 : ℝ) :
    PDF.mellinMoment M.valenceModelPdf n s Q2
      = M.valenceModelWeight s * (((n : ℝ) + 1) * ((n : ℝ) + 2))⁻¹ := by
  rw [valenceModelPdf, PDF.mellinMoment_weight, PDF.mellinMoment_modelPdf_zero_one]

/-- **The valence model has the valence numbers of its meson**: for a flavoured meson the valence
quark contributes one net quark of its flavour, the valence antiquark one net antiquark of its own,
and no other flavour is populated; when the two valence flavours coincide their contributions
cancel and every valence integral vanishes. -/
theorem hasValenceNumbers_valenceModelPdf : M.HasValenceNumbers M.valenceModelPdf := by
  intro i Q2
  rw [PDF.valenceNumber_def, mellinMoment_valenceModelPdf, mellinMoment_valenceModelPdf,
    valenceModelWeight_quark, valenceModelWeight_antiquark, M.valenceNumber_apply]
  push_cast
  split_ifs <;> norm_num

/-- **The momentum sum rule for the valence model**: the valence quark, the valence antiquark and
the gluon carry a third of the meson's momentum each. The sum runs over all species, the gluon
included. -/
theorem sum_mellinMoment_one_valenceModelPdf [Fintype Flavor] (Q2 : ℝ) :
    ∑ s, PDF.mellinMoment M.valenceModelPdf 1 s Q2 = 1 :=
  PDF.sum_mellinMoment_one_weight_modelPdf_zero_one M.sum_valenceModelWeight Q2

/-- **The valence assignment and the sum-rule bundle are consistent**: the valence model
of `M` carries the bundle, each species' valence target being half its weight, and has the valence
numbers of `M` by `hasValenceNumbers_valenceModelPdf`. This is the bundle
`PDF.sumRuleAssumptionsWeightModelPdfZeroOne` of the rescaled shape at the valence model's
weight. -/
def sumRuleAssumptionsValenceModelPdf [Fintype Flavor] :
    PDF.SumRuleAssumptions M.valenceModelPdf :=
  PDF.sumRuleAssumptionsWeightModelPdfZeroOne M.sum_valenceModelWeight

@[simp]
theorem sumRuleAssumptionsValenceModelPdf_valenceTarget [Fintype Flavor] (s : Species Flavor) :
    (M.sumRuleAssumptionsValenceModelPdf).valenceTarget s = M.valenceModelWeight s / 2 :=
  (rfl)

end PseudoscalarMeson

/-! ### Covariance of a density assignment -/

section Covariance

variable {Flavor : Type} {F : PseudoscalarMeson Flavor → PDF.Pdf (Species Flavor)}

/-- **Charge-conjugation covariance** of an assignment `F` of parton densities to mesons: the
densities of the charge-conjugate meson are the charge conjugates of the meson's densities. It
expresses the charge-conjugation invariance of the strong interaction, and is not conditioned on
the quark masses. -/
def IsChargeConjCovariant (F : PseudoscalarMeson Flavor → PDF.Pdf (Species Flavor)) : Prop :=
  ∀ M, F M.chargeConj = PDF.chargeConj (F M)

theorem isChargeConjCovariant_iff :
    IsChargeConjCovariant F ↔ ∀ M, F M.chargeConj = PDF.chargeConj (F M) :=
  Iff.rfl

/-- Under charge-conjugation covariance, the density of species `s` in the charge-conjugate meson
is the density of the conjugate species in the meson. -/
theorem IsChargeConjCovariant.chargeConj_apply (hF : IsChargeConjCovariant F)
    (M : PseudoscalarMeson Flavor) (s : Species Flavor) (x Q2 : ℝ) :
    F M.chargeConj s x Q2 = F M s.conj x Q2 := by
  rw [hF M, PDF.chargeConj_apply]

/-- The valence model is charge-conjugation covariant. -/
theorem isChargeConjCovariant_valenceModelPdf [DecidableEq Flavor] :
    IsChargeConjCovariant (PseudoscalarMeson.valenceModelPdf (Flavor := Flavor)) :=
  PseudoscalarMeson.chargeConj_valenceModelPdf

variable [DecidableEq Flavor]

/-- **Covariance under the exchange of the flavours `i` and `j`** of an assignment `F` of parton
densities to mesons: the densities of the meson with `i` and `j` exchanged (its charge shifted by
the charges `e`) are the meson's densities with `i` and `j` exchanged over the species. At the
light-quark charges and up, down it is isospin covariance. -/
def IsSwapFlavorCovariant (e : Flavor → ℝ) (i j : Flavor)
    (F : PseudoscalarMeson Flavor → PDF.Pdf (Species Flavor)) : Prop :=
  ∀ M, F (M.swapFlavor e i j) = PDF.speciesSwapFlavor i j (F M)

theorem isSwapFlavorCovariant_iff (e : Flavor → ℝ) (i j : Flavor) :
    IsSwapFlavorCovariant e i j F ↔ ∀ M, F (M.swapFlavor e i j) = PDF.speciesSwapFlavor i j (F M) :=
  Iff.rfl

/-- Under covariance under the exchange of `i` and `j`, the density of species `s` in the meson
with `i` and `j` exchanged is the density in the meson of the species with them exchanged. -/
theorem IsSwapFlavorCovariant.swapFlavor_apply {e : Flavor → ℝ} {i j : Flavor}
    (hF : IsSwapFlavorCovariant e i j F) (M : PseudoscalarMeson Flavor) (s : Species Flavor)
    (x Q2 : ℝ) : F (M.swapFlavor e i j) s x Q2 = F M (s.map (Equiv.swap i j)) x Q2 := by
  rw [hF M, PDF.speciesSwapFlavor_apply]

/-- The valence model is covariant under the exchange of any two flavours. -/
theorem isSwapFlavorCovariant_valenceModelPdf (e : Flavor → ℝ) (i j : Flavor) :
    IsSwapFlavorCovariant e i j (PseudoscalarMeson.valenceModelPdf (Flavor := Flavor)) :=
  fun M => M.swapFlavor_valenceModelPdf e i j

/-- **A meson whose flavour exchange is its charge conjugate.** If exchanging `i` and `j` in `M`
gives the charge-conjugate meson, as up and down do for the positive pion, then under both
covariances the densities of `M` are invariant under charge conjugation composed with the exchange
of `i` and `j`. -/
theorem IsSwapFlavorCovariant.eq_chargeConj_speciesSwapFlavor {e : Flavor → ℝ} {i j : Flavor}
    (hC : IsChargeConjCovariant F) (hS : IsSwapFlavorCovariant e i j F)
    {M : PseudoscalarMeson Flavor} (hM : M.swapFlavor e i j = M.chargeConj) :
    F M = PDF.chargeConj (PDF.speciesSwapFlavor i j (F M)) := by
  conv_lhs => rw [← M.chargeConj_chargeConj]
  rw [isChargeConjCovariant_iff.1 hC, ← hM, (isSwapFlavorCovariant_iff e i j).1 hS]

/-- The species form of `IsSwapFlavorCovariant.eq_chargeConj_speciesSwapFlavor`: the density of
species `s` is the density of the species obtained from `s` by exchanging `i` and `j` and then
quark and antiquark. -/
theorem IsSwapFlavorCovariant.apply_eq_apply_conj_map {e : Flavor → ℝ} {i j : Flavor}
    (hC : IsChargeConjCovariant F) (hS : IsSwapFlavorCovariant e i j F)
    {M : PseudoscalarMeson Flavor} (hM : M.swapFlavor e i j = M.chargeConj) (s : Species Flavor)
    (x Q2 : ℝ) : F M s x Q2 = F M (s.conj.map (Equiv.swap i j)) x Q2 := by
  conv_lhs => rw [hS.eq_chargeConj_speciesSwapFlavor hC hM]
  rw [PDF.chargeConj_apply, PDF.speciesSwapFlavor_apply]

/-- Under both covariances, for a meson whose exchange of `i` and `j` is its charge conjugate, the
quark density of each flavour `k` is the antiquark density of `Equiv.swap i j k`. -/
theorem IsSwapFlavorCovariant.quark_eq_antiquark_swap {e : Flavor → ℝ} {i j : Flavor}
    (hC : IsChargeConjCovariant F) (hS : IsSwapFlavorCovariant e i j F)
    {M : PseudoscalarMeson Flavor} (hM : M.swapFlavor e i j = M.chargeConj) (k : Flavor) :
    F M (.quark k) = F M (.antiquark (Equiv.swap i j k)) := by
  funext x Q2
  rw [hS.apply_eq_apply_conj_map hC hM, Species.conj_quark, Species.map_antiquark]

/-- Under both covariances, for a meson whose exchange of `i` and `j` is its charge conjugate, the
valence number of each flavour `k` is minus that of `Equiv.swap i j k`, at every scale. -/
theorem IsSwapFlavorCovariant.pdfValenceNumber_eq_neg_swap {e : Flavor → ℝ} {i j : Flavor}
    (hC : IsChargeConjCovariant F) (hS : IsSwapFlavorCovariant e i j F)
    {M : PseudoscalarMeson Flavor} (hM : M.swapFlavor e i j = M.chargeConj) (k : Flavor)
    (Q2 : ℝ) : PDF.valenceNumber (F M) k Q2 = -PDF.valenceNumber (F M) (Equiv.swap i j k) Q2 := by
  conv_lhs => rw [hS.eq_chargeConj_speciesSwapFlavor hC hM]
  rw [PDF.valenceNumber_chargeConj, PDF.valenceNumber_speciesSwapFlavor]

end Covariance

/-! ### The charged pion and the charged kaon -/

/-- The charge-weighted valence numbers of the valence model of the positive pion sum to its
charge: `2/3` from the net up quark and `1/3` from the net down antiquark. -/
theorem sum_charge_mul_pdfValenceNumber_valenceModelPdf_piPlus (Q2 : ℝ) :
    ∑ i, LightFlavor.charge i * PDF.valenceNumber piPlus.valenceModelPdf i Q2 = 1 :=
  (piPlus.hasValenceNumbers_valenceModelPdf.sum_mul_pdfValenceNumber_eq_charge
    isChargeConsistent_piPlus Q2).trans piPlus_charge

/-- The same for the positive kaon, whose valence antiquark is strange: nothing in the valence
assignment depends on the flavour content. -/
theorem sum_charge_mul_pdfValenceNumber_valenceModelPdf_kPlus (Q2 : ℝ) :
    ∑ i, LightFlavor.charge i * PDF.valenceNumber kPlus.valenceModelPdf i Q2 = 1 :=
  (kPlus.hasValenceNumbers_valenceModelPdf.sum_mul_pdfValenceNumber_eq_charge
    isChargeConsistent_kPlus Q2).trans kPlus_charge

end Meson
end Particles
end EpsilonEridani
