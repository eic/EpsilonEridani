/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Meson.Pdf.Basic
public import EpsilonEridani.Particles.Parton.PDF.Isospin

/-!
# Isospin and charge conjugation among the charged-pion densities

The parton densities of the pseudoscalar mesons are recorded as an assignment
`F : PseudoscalarMeson LightFlavor → PDF.Pdf (Species LightFlavor)` of a density to each meson, the
densities of a world whose quark masses have the flavour-breaking data `b : FlavorBreaking`. Two
symmetries constrain such an assignment, and they are stated as two separate hypotheses.

* `IsChargeConjCovariant F`: the densities of the charge-conjugate meson are the charge conjugates
  of the meson's densities, `F M.chargeConj = PDF.chargeConj (F M)`. This is the
  charge-conjugation invariance of the strong interaction; it does not depend on the quark masses.
* `IsIsospinCovariantInLimit b F`: *if `b` is in the isospin limit*, the densities of the isospin
  conjugate `M.isospinConj` (up and down exchanged in the valence content) are the isospin
  conjugates of the meson's, `F M.isospinConj = PDF.speciesIsospinConj u d (F M)`. Away from the
  isospin limit it asserts nothing: the relation is a conditional on the vanishing of the
  isospin-breaking parameter, never an approximate equality.

From charge conjugation alone the negative pion's density of any species is the positive pion's
density of the conjugate species (`IsChargeConjCovariant.piMinus_apply`). In the isospin limit
the two symmetries combine, since isospin conjugation sends `π⁺` to `π⁻` and charge conjugation
sends `π⁻` back to `π⁺`: the positive pion's densities are invariant under charge conjugation
composed with the exchange of up and down (`piPlus_eq_chargeConj_speciesIsospinConj`). Read
species by species this gives `u^{π⁺} = dbar^{π⁺}` (`piPlus_quark_u_eq_antiquark_d`),
`d^{π⁺} = ubar^{π⁺}` and `s^{π⁺} = sbar^{π⁺}`, at every momentum fraction and every scale. For the
valence numbers it gives `n_d = -n_u` and `n_s = 0`, so of the three valence sum rules of the
positive pion only the up-quark one is independent (`hasValenceNumbers_piPlus_iff`).

The converse fails: the equality `u^{π⁺} = dbar^{π⁺}` does not force the isospin limit. The
valence model `PseudoscalarMeson.valenceModelPdf` is covariant under both symmetries at every
breaking (`isChargeConjCovariant_valenceModelPdf`, `swapFlavor_valenceModelPdf`), satisfies the
density assumptions, and has `u^{π⁺} = dbar^{π⁺}`, while the breaking data of the physical quark
masses are not in the isospin limit (`exists_not_isIsospinLimit_piPlus_quark_u_eq_antiquark_d`).
The relation is necessary for isospin symmetry and not sufficient: the equality alone does not
establish the isospin limit.

Exchanging any two flavours `i`, `j` of a meson (`PseudoscalarMeson.swapFlavor`) acts on the
valence model as the species-level exchange `PDF.speciesIsospinConj i j`
(`swapFlavor_valenceModelPdf`), and the two exchanges together preserve the valence assignment
(`hasValenceNumbers_swapFlavor_iff`); the isospin conjugate is the case of up and down.

The neutral pion, a superposition of `u ubar` and `d dbar`, has no single valence pair and is not a
`PseudoscalarMeson`, so the relation of its densities to those of the charged pions is not stated
here.

## Main definitions

* `EpsilonEridani.Particles.Meson.IsIsospinCovariantInLimit`: isospin covariance of a density
  assignment in the isospin limit of the breaking data.

## Main results

* `PseudoscalarMeson.swapFlavor_valenceModelPdf`: exchanging two flavours of a meson exchanges
  them in its valence model.
* `PseudoscalarMeson.hasValenceNumbers_swapFlavor_iff`: exchanging two flavours in both the meson
  and the density preserves the valence assignment.
* `IsChargeConjCovariant.piMinus_apply`: the negative pion's densities are the positive pion's at
  the conjugate species, with no isospin hypothesis.
* `piPlus_eq_chargeConj_speciesIsospinConj`: in the isospin limit the positive pion's densities
  are invariant under charge conjugation composed with the exchange of up and down.
* `piPlus_quark_u_eq_antiquark_d`, `piPlus_quark_d_eq_antiquark_u`,
  `piPlus_quark_s_eq_antiquark_s`: the resulting equalities of the positive pion's densities.
* `valenceNumber_piPlus_eq_neg_swap`: in the isospin limit the valence number of each flavour in
  the positive pion is minus that of its isospin partner.
* `hasValenceNumbers_piPlus_iff`: in the isospin limit the valence numbers of the positive pion
  reduce to the up-quark sum rule.
* `exists_not_isIsospinLimit_piPlus_quark_u_eq_antiquark_d`: the equality `u^{π⁺} = dbar^{π⁺}`
  holds for a density satisfying the assumptions and both covariances while the isospin-breaking
  parameter is non-zero.

## References

* J. F. Owens, *Q²-dependent parametrizations of pion parton distribution functions*,
  Phys. Rev. D 30 (1984) 943: the isospin and charge-conjugation relations among the pion
  densities.
* M. Glück, E. Reya and A. Vogt, *Pionic parton distributions*, Z. Phys. C 53 (1992) 651.
* S. Navas et al. (Particle Data Group), *Review of Particle Physics*, Phys. Rev. D 110 (2024)
  030001: the light-quark masses.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Meson

open Parton Parton.LightFlavor

/-! ### The valence model under an exchange of two flavours -/

namespace PseudoscalarMeson

variable {Flavor : Type} [DecidableEq Flavor] (M : PseudoscalarMeson Flavor) (e : Flavor → ℝ)
  (i j : Flavor)

/-- The weight of the meson with two flavours exchanged is the weight of the meson at the species
with those flavours exchanged. -/
@[simp]
theorem swapFlavor_valenceModelWeight :
    (M.swapFlavor e i j).valenceModelWeight
      = M.valenceModelWeight ∘ Species.map (Equiv.swap i j) := by
  funext s
  cases s <;> simp [Equiv.swap_apply_eq_iff]

/-- **The valence model of the meson with two flavours exchanged is the valence model with those
flavours exchanged over the species**, at every value of the quark masses: the shape is
flavour-independent and the weight relabels by `swapFlavor_valenceModelWeight`. Over the light
flavours with up and down this is the isospin covariance of the valence model. -/
@[simp]
theorem swapFlavor_valenceModelPdf :
    (M.swapFlavor e i j).valenceModelPdf = PDF.speciesIsospinConj i j M.valenceModelPdf := by
  rw [valenceModelPdf_eq_weight, valenceModelPdf_eq_weight, PDF.speciesIsospinConj_weight,
    PDF.speciesIsospinConj_eq_comap, PDF.comap_modelPdf, swapFlavor_valenceModelWeight]

/-- Exchanging two flavours in both the meson and the density preserves the valence assignment:
the exchanged density has the valence numbers of the exchanged meson exactly when the density has
those of the meson. -/
@[simp]
theorem hasValenceNumbers_swapFlavor_iff (f : PDF.Pdf (Species Flavor)) :
    (M.swapFlavor e i j).HasValenceNumbers (PDF.speciesIsospinConj i j f)
      ↔ M.HasValenceNumbers f := by
  simp only [hasValenceNumbers_iff, PDF.valenceNumber_speciesIsospinConj,
    swapFlavor_valenceNumber, Function.comp_apply]
  exact ⟨fun h k Q2 => by simpa using h (Equiv.swap i j k) Q2, fun h k Q2 => h _ Q2⟩

end PseudoscalarMeson

/-! ### Isospin covariance -/

/-- **Isospin covariance in the isospin limit of the breaking data `b`** of an assignment `F` of
parton densities to the mesons over the light flavours: if `b` is in the isospin limit, the
densities of the isospin-conjugate meson are the meson's densities with up and down exchanged.
Away from the isospin limit it asserts nothing. -/
def IsIsospinCovariantInLimit (b : FlavorBreaking)
    (F : PseudoscalarMeson LightFlavor → PDF.Pdf (Species LightFlavor)) : Prop :=
  b.IsIsospinLimit → ∀ M, F M.isospinConj = PDF.speciesIsospinConj u d (F M)

variable {b : FlavorBreaking} {F : PseudoscalarMeson LightFlavor → PDF.Pdf (Species LightFlavor)}

theorem isIsospinCovariantInLimit_iff :
    IsIsospinCovariantInLimit b F ↔
      b.IsIsospinLimit → ∀ M, F M.isospinConj = PDF.speciesIsospinConj u d (F M) :=
  Iff.rfl

/-- In the isospin limit, under isospin covariance, the density of species `s` in the
isospin-conjugate meson is the density in the meson of the species with up and down exchanged. -/
theorem IsIsospinCovariantInLimit.isospinConj_apply (hI : IsIsospinCovariantInLimit b F)
    (hb : b.IsIsospinLimit) (M : PseudoscalarMeson LightFlavor) (s : Species LightFlavor)
    (x Q2 : ℝ) : F M.isospinConj s x Q2 = F M (s.map (Equiv.swap u d)) x Q2 := by
  rw [hI hb M, PDF.speciesIsospinConj_apply]

/-- The valence model is isospin covariant in the isospin limit of any breaking data, its densities
being isospin covariant whatever the quark masses (`PseudoscalarMeson.swapFlavor_valenceModelPdf`).
-/
theorem isIsospinCovariantInLimit_valenceModelPdf (b : FlavorBreaking) :
    IsIsospinCovariantInLimit b PseudoscalarMeson.valenceModelPdf :=
  fun _ M => M.swapFlavor_valenceModelPdf _ _ _

/-! ### The charged pions -/

/-- **Charge conjugation relates the two charged pions**: the density of any species in the
negative pion is the density of the conjugate species in the positive pion. No isospin
hypothesis is needed. -/
theorem IsChargeConjCovariant.piMinus_apply (hF : IsChargeConjCovariant F) (s : Species LightFlavor)
    (x Q2 : ℝ) : F piMinus s x Q2 = F piPlus s.conj x Q2 := by
  rw [piMinus_eq_chargeConj_piPlus, hF.chargeConj_apply]

/-- In the isospin limit, the negative pion's densities are the positive pion's with up and down
exchanged. -/
theorem IsIsospinCovariantInLimit.piMinus_eq (hI : IsIsospinCovariantInLimit b F)
    (hb : b.IsIsospinLimit) : F piMinus = PDF.speciesIsospinConj u d (F piPlus) := by
  rw [← isospinConj_piPlus, hI hb]

/-- **The positive pion in the isospin limit**: its densities are invariant under charge
conjugation composed with the exchange of up and down, since isospin conjugation sends `π⁺` to
`π⁻` and charge conjugation sends `π⁻` back to `π⁺`. -/
theorem piPlus_eq_chargeConj_speciesIsospinConj (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) :
    F piPlus = PDF.chargeConj (PDF.speciesIsospinConj u d (F piPlus)) := by
  conv_lhs => rw [← PseudoscalarMeson.chargeConj_chargeConj piPlus,
    ← piMinus_eq_chargeConj_piPlus]
  rw [isChargeConjCovariant_iff.1 hC piMinus, hI.piMinus_eq hb]

/-- The species form of `piPlus_eq_chargeConj_speciesIsospinConj`: in the isospin limit the
positive pion's density of species `s` is its density of the species obtained from `s` by
exchanging up and down and then quark and antiquark. -/
theorem piPlus_apply_eq_apply_conj_map (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) (s : Species LightFlavor)
    (x Q2 : ℝ) : F piPlus s x Q2 = F piPlus (s.conj.map (Equiv.swap u d)) x Q2 := by
  conv_lhs => rw [piPlus_eq_chargeConj_speciesIsospinConj hC hI hb]
  rw [PDF.chargeConj_apply, PDF.speciesIsospinConj_apply]

/-- **The up-quark density of the positive pion is its down-antiquark density** in the isospin
limit, at every momentum fraction and every scale. -/
theorem piPlus_quark_u_eq_antiquark_d (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) :
    F piPlus (.quark u) = F piPlus (.antiquark d) := by
  funext x Q2
  rw [piPlus_apply_eq_apply_conj_map hC hI hb, Species.conj_quark, Species.map_antiquark,
    Equiv.swap_apply_left]

/-- The down-quark density of the positive pion is its up-antiquark density in the isospin
limit. -/
theorem piPlus_quark_d_eq_antiquark_u (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) :
    F piPlus (.quark d) = F piPlus (.antiquark u) := by
  funext x Q2
  rw [piPlus_apply_eq_apply_conj_map hC hI hb, Species.conj_quark, Species.map_antiquark,
    Equiv.swap_apply_right]

/-- The strange-quark density of the positive pion is its strange-antiquark density in the
isospin limit. -/
theorem piPlus_quark_s_eq_antiquark_s (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) :
    F piPlus (.quark s) = F piPlus (.antiquark s) := by
  funext x Q2
  rw [piPlus_apply_eq_apply_conj_map hC hI hb, Species.conj_quark, Species.map_antiquark,
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]

/-- In the isospin limit the valence number of each flavour in the positive pion is minus the
valence number of its isospin partner, at every scale. -/
theorem valenceNumber_piPlus_eq_neg_swap (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) (i : LightFlavor) (Q2 : ℝ) :
    PDF.valenceNumber (F piPlus) i Q2 = -PDF.valenceNumber (F piPlus) (Equiv.swap u d i) Q2 := by
  conv_lhs => rw [piPlus_eq_chargeConj_speciesIsospinConj hC hI hb]
  rw [PDF.valenceNumber_chargeConj, PDF.valenceNumber_speciesIsospinConj]

/-- In the isospin limit the positive pion carries as many net down antiquarks as net up quarks:
its down valence number is minus its up valence number, at every scale. -/
theorem valenceNumber_piPlus_d_eq_neg_u (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) (Q2 : ℝ) :
    PDF.valenceNumber (F piPlus) d Q2 = -PDF.valenceNumber (F piPlus) u Q2 := by
  rw [valenceNumber_piPlus_eq_neg_swap hC hI hb, Equiv.swap_apply_right]

/-- In the isospin limit the positive pion carries no net strangeness, at every scale. -/
theorem valenceNumber_piPlus_s_eq_zero (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) (Q2 : ℝ) :
    PDF.valenceNumber (F piPlus) s Q2 = 0 := by
  have h := valenceNumber_piPlus_eq_neg_swap hC hI hb s Q2
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  linarith

/-- **In the isospin limit the three valence sum rules of the positive pion reduce to one**: the
positive pion's densities have its valence numbers exactly when they carry one net up quark at
every scale; the down-antiquark and strangeness sum rules then follow. -/
theorem hasValenceNumbers_piPlus_iff (hC : IsChargeConjCovariant F)
    (hI : IsIsospinCovariantInLimit b F) (hb : b.IsIsospinLimit) :
    piPlus.HasValenceNumbers (F piPlus) ↔ ∀ Q2, PDF.valenceNumber (F piPlus) u Q2 = 1 := by
  rw [piPlus.hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark (F piPlus) (by simp),
    piPlus_valenceQuark, piPlus_valenceAntiquark]
  refine ⟨fun h => h.1, fun h => ⟨h, fun Q2 => ?_, fun i hu hd Q2 => ?_⟩⟩
  · rw [valenceNumber_piPlus_d_eq_neg_u hC hI hb, h]
  · cases i
    · exact absurd rfl hu
    · exact absurd rfl hd
    · exact valenceNumber_piPlus_s_eq_zero hC hI hb Q2

/-! ### The relation does not force the isospin limit -/

/-- **`u^{π⁺} = dbar^{π⁺}` is necessary for isospin symmetry and not sufficient.** The valence
model satisfies the density assumptions, is covariant under charge conjugation and, at every
breaking, under isospin conjugation, and its positive pion has equal up-quark and down-antiquark
densities at every scale; yet the breaking data of the physical light-quark masses
`m_u = 2.16`, `m_d = 4.70`, `m_s = 93.5` (in MeV) are not in the isospin limit. -/
theorem exists_not_isIsospinLimit_piPlus_quark_u_eq_antiquark_d :
    ∃ (b : FlavorBreaking) (F : PseudoscalarMeson LightFlavor → PDF.Pdf (Species LightFlavor)),
      ¬ b.IsIsospinLimit ∧ IsChargeConjCovariant F ∧
        (∀ M, F M.isospinConj = PDF.speciesIsospinConj u d (F M)) ∧
          (∀ M, PDF.Assumptions (F M)) ∧ F piPlus (.quark u) = F piPlus (.antiquark d) := by
  refine ⟨FlavorBreaking.ofMasses 2.16 4.70 93.5, PseudoscalarMeson.valenceModelPdf, ?_,
    isChargeConjCovariant_valenceModelPdf, fun M => M.swapFlavor_valenceModelPdf _ _ _,
    PseudoscalarMeson.assumptions_valenceModelPdf, ?_⟩
  · rw [FlavorBreaking.isIsospinLimit_ofMasses_iff]
    norm_num
  · exact piPlus_quark_u_eq_antiquark_d isChargeConjCovariant_valenceModelPdf
      (isIsospinCovariantInLimit_valenceModelPdf ⟨0, 0⟩)
      ((FlavorBreaking.isIsospinLimit_iff _).2 rfl)

end Meson
end Particles
end EpsilonEridani
