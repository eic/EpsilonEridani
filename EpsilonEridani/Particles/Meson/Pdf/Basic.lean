/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.Particles.Parton.PDF.ChargeConjugation
public import EpsilonEridani.Particles.Parton.PDF.Model

/-!
# Parton densities of a pseudoscalar meson and their valence sum rules

A parton density of a pseudoscalar meson is a collinear density
`EpsilonEridani.Particles.Parton.PDF.Pdf` over the parton species
`EpsilonEridani.Particles.Parton.Species Flavor` of the meson's flavour type, satisfying the
upstream `PDF.Assumptions`; the support condition, the non-negativity on the unit interval and
the integrability of the Mellin moments are then the upstream statements and are not restated
here. The momentum sum rule and the sum rule for each species are likewise the upstream bundle
`PDF.SumRuleAssumptions`, instantiated rather than restated.

What is specific to a meson is the *valence assignment*. The net number of quarks of flavour `i`
that a density carries at a scale is `PDF.valenceNumber`, and `PseudoscalarMeson.valenceNumber` is
the net valence number the meson's valence pair prescribes. A density has the valence numbers of a
meson, `PseudoscalarMeson.HasValenceNumbers`, when the two agree at every flavour and every scale.
For a flavoured meson this is the conjunction of exactly three sum rules
(`hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark`): one net quark of the valence quark's
flavour, one net antiquark of the valence antiquark's flavour, and no net quarks of any other
flavour. When the valence flavours coincide it is the vanishing of every valence integral
(`hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark`). Against a density that carries the
upstream sum-rule bundle, the assignment is a condition on the bundle's valence targets alone
(`hasValenceNumbers_iff_valenceTarget`), so it suffices to impose it at one scale
(`hasValenceNumbers_of_forall_pdfValenceNumber_eq`); both are the meson instances of the general
`PDF.forall_valenceNumber_eq_iff_valenceTarget` and
`PDF.valenceNumber_eq_of_forall_valenceNumber_eq`.

Two consequences fix what the assignment means. The charge-weighted valence numbers of the density
recover the meson's electric charge whenever the charge is the one carried by the valence pair
(`HasValenceNumbers.sum_mul_pdfValenceNumber_eq_charge`), and the valence content of a flavoured
meson is determined by any density carrying its valence numbers
(`valenceQuark_eq_and_valenceAntiquark_eq_of_hasValenceNumbers`); the three sum rules themselves fix
the valence integrals.

That the assignment is consistent with the upstream sum-rule bundle — that the two can be imposed
together — is exhibited rather than assumed. `PseudoscalarMeson.valenceModelPdf` is the upstream
`PDF.weight` rescaling that carries the shape `2 (1 - x)` on the valence quark, on the valence
antiquark and on the gluon and vanishes on every other species; it satisfies `PDF.Assumptions`, it
has the valence numbers of its meson, and its three populated species carry a third of the momentum
each, so the momentum sum rule holds with the gluon included. Conjugating the meson conjugates the
model (`chargeConj_valenceModelPdf`).

## Main definitions

* `PseudoscalarMeson.HasValenceNumbers`: the density carries the meson's net valence numbers at
  every scale.
* `PseudoscalarMeson.valenceWeight`, `PseudoscalarMeson.valenceModelPdf`: the valence model
  density of a meson and the weight it gives each parton species.
* `PseudoscalarMeson.sumRuleAssumptionsValenceModelPdf`: the upstream sum-rule bundle of the
  valence model.

## Main results

* `PseudoscalarMeson.hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark`: the three valence
  sum rules of a flavoured meson.
* `PseudoscalarMeson.hasValenceNumbers_iff_valenceTarget`: against the upstream sum-rule bundle,
  the valence assignment is a condition on the valence targets.
* `PseudoscalarMeson.HasValenceNumbers.sum_mul_pdfValenceNumber_eq_charge`: the charge-weighted
  valence numbers sum to the meson's charge.
* `PseudoscalarMeson.valenceQuark_eq_and_valenceAntiquark_eq_of_hasValenceNumbers`: the valence
  content of a flavoured meson is determined by any density carrying its valence numbers.
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
number of that flavour. In particular the assignment constrains no other datum of the bundle, and
holds at every scale as soon as it holds at one. That the two can be imposed together at all is
`sumRuleAssumptionsValenceModelPdf`. This is the meson instance of
`PDF.forall_valenceNumber_eq_iff_valenceTarget`. -/
theorem hasValenceNumbers_iff_valenceTarget [Fintype Flavor] (M : PseudoscalarMeson Flavor)
    {f : PDF.Pdf (Species Flavor)} (h : PDF.SumRuleAssumptions f) :
    M.HasValenceNumbers f ↔
      ∀ i, h.valenceTarget (.quark i) - h.valenceTarget (.antiquark i)
        = (M.valenceNumber i : ℝ) :=
  PDF.forall_valenceNumber_eq_iff_valenceTarget h _

/-- **One scale is enough.** A density carrying the upstream sum-rule bundle has the valence
numbers of `M` at every scale as soon as it has them at a single scale `Q2₀`: by
`hasValenceNumbers_iff_valenceTarget` the assignment is a condition on the bundle's
scale-independent valence targets. This is the introduction rule of `HasValenceNumbers` from a
single scale: it carries the general `PDF.valenceNumber_eq_of_forall_valenceNumber_eq` across
`hasValenceNumbers_iff`, which a consumer outside this module cannot do by unfolding, the
definition of `HasValenceNumbers` not being exposed. -/
theorem hasValenceNumbers_of_forall_pdfValenceNumber_eq [Fintype Flavor]
    (M : PseudoscalarMeson Flavor) {f : PDF.Pdf (Species Flavor)}
    (h : PDF.SumRuleAssumptions f) (Q2₀ : ℝ)
    (hf : ∀ i, PDF.valenceNumber f i Q2₀ = (M.valenceNumber i : ℝ)) : M.HasValenceNumbers f :=
  hasValenceNumbers_iff.mpr (PDF.valenceNumber_eq_of_forall_valenceNumber_eq h hf)

/-- **Charge conjugation.** The charge-conjugate density has the valence numbers of the
charge-conjugate meson exactly when the density has those of the meson: conjugating the hadron and
conjugating its densities are the same operation on the valence assignment. -/
@[simp]
theorem hasValenceNumbers_chargeConj_iff (M : PseudoscalarMeson Flavor)
    (f : PDF.Pdf (Species Flavor)) :
    M.chargeConj.HasValenceNumbers (PDF.chargeConj f) ↔ M.HasValenceNumbers f := by
  simp only [hasValenceNumbers_iff, PDF.valenceNumber_chargeConj, chargeConj_valenceNumber,
    Pi.neg_apply, Int.cast_neg, neg_inj]

/-- **The meson charge from the valence integrals.** For a meson whose charge is the one carried
by its valence pair, the valence numbers of any density carrying the meson's valence assignment,
weighted by the quark charges, sum to the meson's charge at every scale. -/
theorem HasValenceNumbers.sum_mul_pdfValenceNumber_eq_charge [Fintype Flavor] {e : Flavor → ℝ}
    (hf : M.HasValenceNumbers f) (he : M.IsChargeConsistent e) (Q2 : ℝ) :
    ∑ i, e i * PDF.valenceNumber f i Q2 = M.charge := by
  simp only [hasValenceNumbers_iff.mp hf]
  exact he.sum_mul_valenceNumber

/-- **The net valence numbers of a meson are determined by any density carrying them.** Two mesons
whose valence numbers one density carries have the same net valence numbers. -/
theorem valenceNumber_eq_of_hasValenceNumbers (hM : M.HasValenceNumbers f)
    (hM' : M'.HasValenceNumbers f) : M.valenceNumber = M'.valenceNumber := by
  funext i
  exact Int.cast_injective ((hM i 0).symm.trans (hM' i 0))

/-- **The valence content of a flavoured meson is determined by its densities.** Any density
carrying the valence numbers of a flavoured meson and of a second meson forces the two to share
their valence quark and valence antiquark. -/
theorem valenceQuark_eq_and_valenceAntiquark_eq_of_hasValenceNumbers
    (hM : M.HasValenceNumbers f) (hM' : M'.HasValenceNumbers f)
    (h : M.valenceQuark ≠ M.valenceAntiquark) :
    M.valenceQuark = M'.valenceQuark ∧ M.valenceAntiquark = M'.valenceAntiquark :=
  M.valenceQuark_eq_and_valenceAntiquark_eq_of_valenceNumber_eq M'
    (valenceNumber_eq_of_hasValenceNumbers hM hM') h

/-- **The flavour-neutral case.** A density has the valence numbers of a meson whose valence quark
and valence antiquark share a flavour exactly when every valence integral vanishes, those valence
numbers all being zero. Only the valence integrals vanish: the individual quark and antiquark
densities need not. -/
theorem hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark (M : PseudoscalarMeson Flavor)
    (f : PDF.Pdf (Species Flavor)) (h : M.valenceQuark = M.valenceAntiquark) :
    M.HasValenceNumbers f ↔ ∀ i Q2, PDF.valenceNumber f i Q2 = 0 := by
  have hM : M.valenceNumber = 0 := M.valenceNumber_eq_zero_iff.2 h
  simp only [hasValenceNumbers_iff, hM, Pi.zero_apply, Int.cast_zero]

/-- A charge-conjugation invariant density has the valence numbers of every meson whose valence
quark and valence antiquark share a flavour: the C-invariant case of
`hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark`. -/
theorem hasValenceNumbers_of_chargeConj_eq (M : PseudoscalarMeson Flavor)
    {f : PDF.Pdf (Species Flavor)} (h : M.valenceQuark = M.valenceAntiquark)
    (hf : PDF.chargeConj f = f) : M.HasValenceNumbers f :=
  (M.hasValenceNumbers_iff_of_valenceQuark_eq_valenceAntiquark f h).2
    fun i Q2 => PDF.valenceNumber_eq_zero_of_chargeConj_eq hf i Q2

/-! ### A valence model density

The valence assignment and the upstream sum-rule bundle can be imposed on one density at once.
`valenceModelPdf` is the witness: the `EpsilonEridani.Particles.Parton.PDF.weight` rescaling of the
shape `1 - x` of `EpsilonEridani.Particles.Parton.PDF.modelPdf` that carries `2 (1 - x)` on the
valence quark, the valence antiquark and the gluon, and nothing on any other species. -/

/-- The weight the valence model of `M` gives each parton species: two on the quark of the valence
quark's flavour, on the antiquark of the valence antiquark's flavour, and on the gluon, and zero on
every other species. -/
def valenceWeight (M : PseudoscalarMeson Flavor) : Species Flavor → ℝ
  | .quark i => if i = M.valenceQuark then 2 else 0
  | .antiquark i => if i = M.valenceAntiquark then 2 else 0
  | .gluon => 2

variable (M)

@[simp]
theorem valenceWeight_quark (i : Flavor) :
    M.valenceWeight (.quark i) = if i = M.valenceQuark then 2 else 0 := (rfl)

@[simp]
theorem valenceWeight_antiquark (i : Flavor) :
    M.valenceWeight (.antiquark i) = if i = M.valenceAntiquark then 2 else 0 := (rfl)

@[simp]
theorem valenceWeight_gluon : M.valenceWeight (Species.gluon) = 2 := (rfl)

theorem valenceWeight_nonneg (s : Species Flavor) : 0 ≤ M.valenceWeight s := by
  cases s with
  | quark i => rw [valenceWeight_quark]; split_ifs <;> norm_num
  | antiquark i => rw [valenceWeight_antiquark]; split_ifs <;> norm_num
  | gluon => rw [valenceWeight_gluon]; norm_num

/-- The weight of the charge-conjugate meson is the weight of the meson at the conjugate species:
conjugating the meson exchanges the valence quark with the valence antiquark, and `Species.conj`
exchanges the species that carry them. -/
@[simp]
theorem chargeConj_valenceWeight : M.chargeConj.valenceWeight = M.valenceWeight ∘ Species.conj := by
  funext s
  cases s with
  | quark i => rw [valenceWeight_quark, Function.comp_apply, Species.conj_quark,
      valenceWeight_antiquark, chargeConj_valenceQuark]
  | antiquark i => rw [valenceWeight_antiquark, Function.comp_apply, Species.conj_antiquark,
      valenceWeight_quark, chargeConj_valenceAntiquark]
  | gluon => rw [valenceWeight_gluon, Function.comp_apply, Species.conj_gluon, valenceWeight_gluon]

/-- The weights of the valence model sum to six over all species: two each for the valence quark,
the valence antiquark and the gluon, whether or not the valence flavours coincide. -/
@[simp]
theorem sum_valenceWeight [Fintype Flavor] : ∑ s, M.valenceWeight s = 6 := by
  rw [Species.sum_univ]
  norm_num

/-- **A valence model density of the meson `M`**: the shape `2 (1 - x)` on the quark of the valence
quark's flavour, on the antiquark of the valence antiquark's flavour and on the gluon, and zero on
every other species, at every scale. It satisfies the upstream density assumptions
(`assumptions_valenceModelPdf`), has the valence numbers of `M`
(`hasValenceNumbers_valenceModelPdf`) and obeys the momentum sum rule
(`sum_mellinMoment_one_valenceModelPdf`), its three populated species carrying a third of the
momentum each. -/
def valenceModelPdf (M : PseudoscalarMeson Flavor) : PDF.Pdf (Species Flavor) :=
  PDF.weight M.valenceWeight (PDF.modelPdf (Species Flavor) 0 1)

@[simp]
theorem valenceModelPdf_apply (s : Species Flavor) (x Q2 : ℝ) :
    M.valenceModelPdf s x Q2 = M.valenceWeight s * PDF.modelPdf (Species Flavor) 0 1 s x Q2 :=
  (rfl)

/-- The valence model satisfies the upstream density assumptions: it is a non-negative weighting,
species by species, of a density that does. -/
theorem assumptions_valenceModelPdf : PDF.Assumptions M.valenceModelPdf :=
  (PDF.assumptions_modelPdf (Species Flavor) 0 1).weight M.valenceWeight_nonneg

/-- **The valence model of the charge-conjugate meson is the charge conjugate of the valence
model.** Conjugating the hadron and conjugating its densities agree on the valence model, the
flavour-independent shape being invariant and the weight conjugating by
`chargeConj_valenceWeight`. -/
@[simp]
theorem chargeConj_valenceModelPdf :
    PDF.chargeConj M.valenceModelPdf = M.chargeConj.valenceModelPdf := by
  have hshape : PDF.chargeConj (PDF.modelPdf (Species Flavor) 0 1)
      = PDF.modelPdf (Species Flavor) 0 1 := by
    funext s x Q2
    rw [PDF.chargeConj_apply, PDF.modelPdf_apply, PDF.modelPdf_apply]
  rw [valenceModelPdf, PDF.chargeConj_weight, hshape, valenceModelPdf, chargeConj_valenceWeight]

/-- The Mellin moments of the valence model: the species weight times the moment
`1 / ((n + 1) (n + 2))` of the shape `1 - x`. -/
@[simp]
theorem mellinMoment_valenceModelPdf (n : ℕ) (s : Species Flavor) (Q2 : ℝ) :
    PDF.mellinMoment M.valenceModelPdf n s Q2
      = M.valenceWeight s * (((n : ℝ) + 1) * ((n : ℝ) + 2))⁻¹ := by
  rw [valenceModelPdf, PDF.mellinMoment_weight, PDF.mellinMoment_modelPdf_zero_one]

/-- **The valence model has the valence numbers of its meson**: for a flavoured meson the valence
quark contributes one net quark of its flavour, the valence antiquark one net antiquark of its own,
and no other flavour is populated; when the two valence flavours coincide their contributions
cancel and every valence integral vanishes. -/
theorem hasValenceNumbers_valenceModelPdf : M.HasValenceNumbers M.valenceModelPdf := by
  intro i Q2
  rw [PDF.valenceNumber_def, mellinMoment_valenceModelPdf, mellinMoment_valenceModelPdf,
    valenceWeight_quark, valenceWeight_antiquark, M.valenceNumber_apply]
  push_cast
  split_ifs <;> norm_num

/-- **The momentum sum rule for the valence model**: the valence quark, the valence antiquark and
the gluon carry a third of the meson's momentum each. The sum runs over all species, the gluon
included. -/
theorem sum_mellinMoment_one_valenceModelPdf [Fintype Flavor] (Q2 : ℝ) :
    ∑ s, PDF.mellinMoment M.valenceModelPdf 1 s Q2 = 1 := by
  simp only [mellinMoment_valenceModelPdf, ← Finset.sum_mul, sum_valenceWeight]
  norm_num

/-- **The valence assignment and the upstream sum-rule bundle are consistent**: the valence model
of `M` carries the bundle, each species' valence target being half its weight, and has the valence
numbers of `M` by `hasValenceNumbers_valenceModelPdf`. -/
def sumRuleAssumptionsValenceModelPdf [Fintype Flavor] :
    PDF.SumRuleAssumptions M.valenceModelPdf where
  momentum Q2 := M.sum_mellinMoment_one_valenceModelPdf Q2
  valenceTarget s := M.valenceWeight s / 2
  valence s Q2 := by
    rw [mellinMoment_valenceModelPdf]
    push_cast
    ring

@[simp]
theorem sumRuleAssumptionsValenceModelPdf_valenceTarget [Fintype Flavor] (s : Species Flavor) :
    (M.sumRuleAssumptionsValenceModelPdf).valenceTarget s = M.valenceWeight s / 2 :=
  (rfl)

end PseudoscalarMeson

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
