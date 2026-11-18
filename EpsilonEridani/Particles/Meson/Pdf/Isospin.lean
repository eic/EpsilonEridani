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
  of the meson's densities, `F M.chargeConj = PDF.chargeConj (F M)`. It expresses the
  charge-conjugation invariance of the strong interaction, and is not conditioned on `b`.
* `IsSwapFlavorCovariant LightFlavor.charge u d F`, isospin covariance: the densities of the
  isospin conjugate `M.swapFlavor LightFlavor.charge u d` (up and down exchanged in the valence
  content) are the meson's with up and down exchanged, `PDF.speciesSwapFlavor u d (F M)`. It is
  what the isospin limit provides, so the relations below are consequences of it alone; for
  breaking data `b` the hypothesis enters as the conditional
  `b.IsIsospinLimit → IsSwapFlavorCovariant LightFlavor.charge u d F`
  (`piPlus_quark_u_eq_antiquark_d_of_isIsospinLimit`), which asserts nothing away from the isospin
  limit, never an approximate equality.

From charge conjugation alone the negative pion's density of any species is the positive pion's
density of the conjugate species (`IsChargeConjCovariant.piMinus_apply`). Under isospin
covariance the two symmetries combine, since isospin conjugation sends `π⁺` to `π⁻` and charge
conjugation sends `π⁻` back to `π⁺`: the positive pion's densities are invariant under charge
conjugation composed with the exchange of up and down (`piPlus_eq_chargeConj_speciesSwapFlavor`).
Read species by species this gives `u^{π⁺} = dbar^{π⁺}` (`piPlus_quark_u_eq_antiquark_d`),
`d^{π⁺} = ubar^{π⁺}` and `s^{π⁺} = sbar^{π⁺}`, at every momentum fraction and every scale. For
the valence numbers it gives `n_d = -n_u` and `n_s = 0`, so of the three valence sum rules of the
positive pion only the up-quark one is independent (`hasValenceNumbers_piPlus_iff`).

The converse fails: the equality `u^{π⁺} = dbar^{π⁺}` does not force the isospin limit. The
valence model `PseudoscalarMeson.valenceModelPdf` is covariant under both symmetries at every
breaking (`isChargeConjCovariant_valenceModelPdf`, `isSwapFlavorCovariant_valenceModelPdf`),
satisfies the density assumptions, and has `u^{π⁺} = dbar^{π⁺}`, while the breaking data of the
physical quark masses are not in the isospin limit
(`exists_not_isIsospinLimit_piPlus_quark_u_eq_antiquark_d`).
The relation is necessary for isospin symmetry and not sufficient: the equality alone does not
establish the isospin limit.

The neutral pion, a superposition of `u ubar` and `d dbar`, has no single valence pair and is not a
`PseudoscalarMeson`, so the relation of its densities to those of the charged pions is not stated
here.

## Main results

* `IsChargeConjCovariant.piMinus_apply`: the negative pion's densities are the positive pion's at
  the conjugate species, with no isospin hypothesis.
* `piPlus_eq_chargeConj_speciesSwapFlavor`: under isospin covariance the positive pion's densities
  are invariant under charge conjugation composed with the exchange of up and down.
* `piPlus_quark_u_eq_antiquark_d`, `piPlus_quark_d_eq_antiquark_u`,
  `piPlus_quark_s_eq_antiquark_s`: the resulting equalities of the positive pion's densities.
* `piPlus_quark_u_eq_antiquark_d_of_isIsospinLimit`: in the isospin limit of the breaking data,
  `u^{π⁺} = dbar^{π⁺}`.
* `valenceNumber_piPlus_eq_neg_swap`: under isospin covariance the valence number of each flavour in
  the positive pion is minus that of its isospin partner.
* `hasValenceNumbers_piPlus_iff`: under isospin covariance the valence numbers of the positive pion
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
  030001: the light-quark masses, in the MS-bar scheme at `μ = 2 GeV`.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Meson

open Parton Parton.LightFlavor

variable {F : PseudoscalarMeson LightFlavor → PDF.Pdf (Species LightFlavor)}

/-! ### The charged pions -/

/-- **Charge conjugation relates the two charged pions**: the density of any species in the
negative pion is the density of the conjugate species in the positive pion. No isospin
hypothesis is needed. -/
theorem IsChargeConjCovariant.piMinus_apply (hF : IsChargeConjCovariant F) (s : Species LightFlavor)
    (x Q2 : ℝ) : F piMinus s x Q2 = F piPlus s.conj x Q2 := by
  rw [piMinus_eq_chargeConj_piPlus, hF.chargeConj_apply]

/-- Under isospin covariance, the negative pion's densities are the positive pion's with up and
down exchanged. -/
theorem piMinus_eq_speciesSwapFlavor_piPlus (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) :
    F piMinus = PDF.speciesSwapFlavor u d (F piPlus) := by
  rw [← piPlus_swapFlavor_u_d_eq_piMinus, (isSwapFlavorCovariant_iff _ _ _).1 hI]

/-- **The positive pion under isospin covariance**: its densities are invariant under charge
conjugation composed with the exchange of up and down, since isospin conjugation sends `π⁺` to
`π⁻` and charge conjugation sends `π⁻` back to `π⁺`. -/
theorem piPlus_eq_chargeConj_speciesSwapFlavor (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) :
    F piPlus = PDF.chargeConj (PDF.speciesSwapFlavor u d (F piPlus)) := by
  conv_lhs => rw [← PseudoscalarMeson.chargeConj_chargeConj piPlus,
    ← piMinus_eq_chargeConj_piPlus]
  rw [isChargeConjCovariant_iff.1 hC piMinus, piMinus_eq_speciesSwapFlavor_piPlus hI]

/-- The species form of `piPlus_eq_chargeConj_speciesSwapFlavor`: under isospin covariance
the positive pion's density of species `s` is its density of the species obtained from `s` by
exchanging up and down and then quark and antiquark. -/
theorem piPlus_apply_eq_apply_conj_map (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) (s : Species LightFlavor)
    (x Q2 : ℝ) : F piPlus s x Q2 = F piPlus (s.conj.map (Equiv.swap u d)) x Q2 := by
  conv_lhs => rw [piPlus_eq_chargeConj_speciesSwapFlavor hC hI]
  rw [PDF.chargeConj_apply, PDF.speciesSwapFlavor_apply]

/-- **The up-quark density of the positive pion is its down-antiquark density** under isospin
covariance, at every momentum fraction and every scale. -/
theorem piPlus_quark_u_eq_antiquark_d (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) :
    F piPlus (.quark u) = F piPlus (.antiquark d) := by
  funext x Q2
  rw [piPlus_apply_eq_apply_conj_map hC hI, Species.conj_quark, Species.map_antiquark,
    Equiv.swap_apply_left]

/-- The down-quark density of the positive pion is its up-antiquark density under isospin
covariance. -/
theorem piPlus_quark_d_eq_antiquark_u (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) :
    F piPlus (.quark d) = F piPlus (.antiquark u) := by
  funext x Q2
  rw [piPlus_apply_eq_apply_conj_map hC hI, Species.conj_quark, Species.map_antiquark,
    Equiv.swap_apply_right]

/-- The strange-quark density of the positive pion is its strange-antiquark density under isospin
covariance. -/
theorem piPlus_quark_s_eq_antiquark_s (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) :
    F piPlus (.quark s) = F piPlus (.antiquark s) := by
  funext x Q2
  rw [piPlus_apply_eq_apply_conj_map hC hI, Species.conj_quark, Species.map_antiquark,
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]

/-- **In the isospin limit, the up-quark density of the positive pion is its down-antiquark
density**: the form of `piPlus_quark_u_eq_antiquark_d` conditioned on the breaking data `b`, with
isospin covariance assumed only in the isospin limit. -/
theorem piPlus_quark_u_eq_antiquark_d_of_isIsospinLimit {b : FlavorBreaking}
    (hC : IsChargeConjCovariant F)
    (hI : b.IsIsospinLimit → IsSwapFlavorCovariant LightFlavor.charge u d F)
    (hb : b.IsIsospinLimit) : F piPlus (.quark u) = F piPlus (.antiquark d) :=
  piPlus_quark_u_eq_antiquark_d hC (hI hb)

/-- Under isospin covariance the valence number of each flavour in the positive pion is minus the
valence number of its isospin partner, at every scale. -/
theorem valenceNumber_piPlus_eq_neg_swap (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) (i : LightFlavor) (Q2 : ℝ) :
    PDF.valenceNumber (F piPlus) i Q2 = -PDF.valenceNumber (F piPlus) (Equiv.swap u d i) Q2 := by
  conv_lhs => rw [piPlus_eq_chargeConj_speciesSwapFlavor hC hI]
  rw [PDF.valenceNumber_chargeConj, PDF.valenceNumber_speciesSwapFlavor]

/-- Under isospin covariance the positive pion carries as many net down antiquarks as net up quarks:
its down valence number is minus its up valence number, at every scale. -/
theorem valenceNumber_piPlus_d_eq_neg_u (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) (Q2 : ℝ) :
    PDF.valenceNumber (F piPlus) d Q2 = -PDF.valenceNumber (F piPlus) u Q2 := by
  rw [valenceNumber_piPlus_eq_neg_swap hC hI, Equiv.swap_apply_right]

/-- Under isospin covariance the positive pion carries no net strangeness, at every scale. -/
theorem valenceNumber_piPlus_s_eq_zero (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) (Q2 : ℝ) :
    PDF.valenceNumber (F piPlus) s Q2 = 0 := by
  have h := valenceNumber_piPlus_eq_neg_swap hC hI s Q2
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)] at h
  linarith

/-- **Under isospin covariance the three valence sum rules of the positive pion reduce to one**: the
positive pion's densities have its valence numbers exactly when they carry one net up quark at
every scale; the down-antiquark and strangeness sum rules then follow. -/
theorem hasValenceNumbers_piPlus_iff (hC : IsChargeConjCovariant F)
    (hI : IsSwapFlavorCovariant LightFlavor.charge u d F) :
    piPlus.HasValenceNumbers (F piPlus) ↔ ∀ Q2, PDF.valenceNumber (F piPlus) u Q2 = 1 := by
  rw [piPlus.hasValenceNumbers_iff_of_valenceQuark_ne_valenceAntiquark (F piPlus) (by simp),
    piPlus_valenceQuark, piPlus_valenceAntiquark]
  refine ⟨fun h => h.1, fun h => ⟨h, fun Q2 => ?_, fun i hu hd Q2 => ?_⟩⟩
  · rw [valenceNumber_piPlus_d_eq_neg_u hC hI, h]
  · cases i
    · exact absurd rfl hu
    · exact absurd rfl hd
    · exact valenceNumber_piPlus_s_eq_zero hC hI Q2

/-! ### The relation does not force the isospin limit -/

/-- **`u^{π⁺} = dbar^{π⁺}` is necessary for isospin symmetry and not sufficient.** The valence
model satisfies the density assumptions, is covariant under charge conjugation and, at every
breaking, under isospin conjugation, and its positive pion has equal up-quark and down-antiquark
densities at every scale; yet the breaking data of the PDG MS-bar light-quark masses at
`μ = 2 GeV`, `m_u = 2.16`, `m_d = 4.70`, `m_s = 93.5` (in MeV), are not in the isospin limit. -/
theorem exists_not_isIsospinLimit_piPlus_quark_u_eq_antiquark_d :
    ∃ (b : FlavorBreaking) (F : PseudoscalarMeson LightFlavor → PDF.Pdf (Species LightFlavor)),
      ¬ b.IsIsospinLimit ∧ IsChargeConjCovariant F ∧
        IsSwapFlavorCovariant LightFlavor.charge u d F ∧
          (∀ M, PDF.Assumptions (F M)) ∧ F piPlus (.quark u) = F piPlus (.antiquark d) := by
  refine ⟨FlavorBreaking.ofMasses 2.16 4.70 93.5, PseudoscalarMeson.valenceModelPdf, ?_,
    isChargeConjCovariant_valenceModelPdf, isSwapFlavorCovariant_valenceModelPdf _ _ _,
    PseudoscalarMeson.assumptions_valenceModelPdf, ?_⟩
  · rw [FlavorBreaking.isIsospinLimit_ofMasses_iff]
    norm_num
  · exact piPlus_quark_u_eq_antiquark_d isChargeConjCovariant_valenceModelPdf
      (isSwapFlavorCovariant_valenceModelPdf _ _ _)

end Meson
end Particles
end EpsilonEridani
