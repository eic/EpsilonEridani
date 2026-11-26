/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.Flavor
public import EpsilonEridani.Particles.Parton.PDF.Positivity
public import EpsilonEridani.Particles.Parton.Species
public import EpsilonEridani.QFT.Scattering.DIS.Polarized.SumRules

/-!
# The parton-model polarized structure functions

In the parton model at leading order a longitudinally polarized nucleon is an incoherent sum of
free, massless quarks and antiquarks moving collinearly with it, and the spin-dependent structure
function `g₁` is the charge-weighted sum of their helicity densities,

`g₁(x, Q²) = (1/2) ∑_q e_q² (Δq(x, Q²) + Δqbar(x, Q²))`,

while `g₂` vanishes. This file builds that structure-function pair, `Polarized.partonModel`, from
a charge assignment `charge : Flavor → ℝ` on an arbitrary finite flavour type and a helicity
distribution `Δ : PDF.Pdf (Species Flavor)` over the quark, antiquark and gluon species. The
gluon helicity `Δ gluon` does not enter at this order.

The structure function and the densities are different objects: `partonModel_g1` is the place
where the structure function `StructureFunctions.g1` meets the charge-weighted sum of densities.
Since only the quark and antiquark entries of `Δ` enter, every hypothesis below constrains those
entries alone and leaves `Δ gluon` free.
When the quark and antiquark helicity distributions are read off families of spin-density
matrices (`PDF.helicityPdfOfSpinDensity`), the support and integrability fields of
`Polarized.Assumptions` are discharged rather than assumed
(`assumptions_partonModel_helicityPdfOfSpinDensity`), while measurability in `x` is supplied by
the user: support follows from helicity dominance `|Δq| ≤ q`, and integrability from domination
by the unpolarized density. The gluon entry of the spin-density family is unconstrained. This is the
polarized counterpart of `PDF.assumptions_pdfOfSpinDensity`, and it makes the moments of the
parton-model `g₁` integrals of integrable functions. A complex helicity-amplitude matrix family
`ρ` enters through its real part, `PDF.helicityPdfOfSpinDensity fun s x Q2 => (ρ s x Q2).re`,
whose entries are `(ρ s x Q2).deltaQ`.

The first moment of the parton-model `g₁` is the charge-weighted sum of the helicity charges
`∫₀¹ dx (Δq + Δqbar)` (`firstMomentG1_partonModel`). For the light flavours this is the
leading-order form of the flavour decomposition carried by `Polarized.EllisJaffeSumRule`, so the
parton model discharges its `moment_decomposition` field with vanishing perturbative correction,
and the Ellis–Jaffe sum rule holds for it exactly when the strange helicity charge vanishes
(`ellisJaffeSumRule_partonModel_iff`). Because `g₂` vanishes identically, its first moment
vanishes and the Burkhardt-Cottingham sum rule holds unconditionally (`firstMomentG2_partonModel`,
`burkhardtCottingham_partonModel`).

## Main definitions

* `Polarized.partonModel charge Δ`: the leading-order parton-model pair `(g₁, g₂)`.

## Main statements

* `Polarized.partonModel_g1`: `g₁ = (1/2) ∑_q e_q² (Δq + Δqbar)`.
* `Polarized.assumptions_partonModel`: support, measurability and integrability on `[0, 1]` of
  the quark and antiquark helicity distributions give `Polarized.Assumptions`.
* `Polarized.assumptions_partonModel_of_pdfRegularity`: the same, from the support postulate and
  a `PDF.Regularity` bundle of the helicity distribution.
* `Polarized.assumptions_partonModel_helicityPdfOfSpinDensity`: the same, with support and
  integrability discharged from the structural assumptions of the quark and antiquark
  spin-density families, and measurability of their helicity densities supplied.
* `Polarized.firstMomentG1_partonModel`: `Γ₁ = (1/2) ∑_q e_q² ∫₀¹ dx (Δq + Δqbar)`.
* `Polarized.firstMomentG2_partonModel`: `Γ₂ = 0`.
* `Polarized.burkhardtCottingham_partonModel`: the Burkhardt-Cottingham sum rule,
  unconditionally.
* `Polarized.ellisJaffeSumRule_partonModel_iff`: the light-flavour parton model satisfies the
  Ellis–Jaffe sum rule, with zero correction, exactly when the strange helicity charge vanishes.

## References

* M. Anselmino, A. Efremov and E. Leader, *The theory and phenomenology of polarized deep
  inelastic scattering*, Phys. Rept. **261** (1995) 1 (arXiv:hep-ph/9501369).
* B. Lampe and E. Reya, *Spin physics and polarized structure functions*, Phys. Rept. **332**
  (2000) 1 (arXiv:hep-ph/9810270).
* J. Ellis and R. Jaffe, *Sum rule for deep-inelastic electroproduction from polarized protons*,
  Phys. Rev. D **9** (1974) 1444.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

open EpsilonEridani.Particles.Parton
open EpsilonEridani.Particles.Parton.PDF (Pdf mellinMoment SpinDensity SpinDensityAssumptions
  helicityPdfOfSpinDensity)
open MeasureTheory

variable {Flavor : Type} [Fintype Flavor]

/-- The leading-order parton-model polarized structure functions of a target whose quark
flavours carry the electric charges `charge` (in units of the positron charge) and whose
species carry the helicity distribution `Δ`:

`g₁(x, Q²) = (1/2) ∑_q e_q² (Δq(x, Q²) + Δqbar(x, Q²))`, `g₂ = 0`.

This is the naive parton model of free, massless quarks collinear with the target, in which the
transverse-spin structure function `g₂` vanishes. -/
def partonModel (charge : Flavor → ℝ) (Δ : Pdf (Species Flavor)) : StructureFunctions where
  g1 x Q2 := (1 / 2) * ∑ f, charge f ^ 2 * (Δ (.quark f) x Q2 + Δ (.antiquark f) x Q2)
  g2 _ _ := 0

/-- **The parton-model expression for `g₁`**: the structure function is half the
charge-weighted sum over flavours of the quark and antiquark helicity densities. -/
@[simp]
theorem partonModel_g1 (charge : Flavor → ℝ) (Δ : Pdf (Species Flavor)) (x Q2 : ℝ) :
    (partonModel charge Δ).g1 x Q2 =
      (1 / 2) * ∑ f, charge f ^ 2 * (Δ (.quark f) x Q2 + Δ (.antiquark f) x Q2) :=
  (rfl)

/-- In the leading-order parton model `g₂` vanishes. -/
@[simp]
theorem partonModel_g2 (charge : Flavor → ℝ) (Δ : Pdf (Species Flavor)) (x Q2 : ℝ) :
    (partonModel charge Δ).g2 x Q2 = 0 :=
  (rfl)

/-- The parton-model pair is supported in the physical interval whenever the quark and
antiquark helicity distributions are; the gluon entry of `Δ` is unconstrained. -/
theorem hasPhysicalSupport_partonModel (charge : Flavor → ℝ) {Δ : Pdf (Species Flavor)}
    (hΔ : ∀ f x Q2, x < 0 ∨ 1 < x → Δ (.quark f) x Q2 = 0 ∧ Δ (.antiquark f) x Q2 = 0) :
    HasPhysicalSupport (partonModel charge Δ) where
  support_g1 x Q2 hx := by simp [(hΔ _ x Q2 hx).1, (hΔ _ x Q2 hx).2]
  support_g2 x Q2 _ := partonModel_g2 charge Δ x Q2

/-- The parton-model pair is regular whenever the quark and antiquark helicity distributions are
measurable and integrable on the physical interval at every scale; the gluon entry of `Δ` is
unconstrained. -/
theorem regularity_partonModel (charge : Flavor → ℝ) {Δ : Pdf (Species Flavor)}
    (hm : ∀ f Q2, AEStronglyMeasurable (fun x : ℝ => Δ (.quark f) x Q2) ∧
      AEStronglyMeasurable (fun x : ℝ => Δ (.antiquark f) x Q2))
    (hi : ∀ f Q2, IntegrableOn (fun x : ℝ => Δ (.quark f) x Q2) (Set.Icc 0 1) ∧
      IntegrableOn (fun x : ℝ => Δ (.antiquark f) x Q2) (Set.Icc 0 1)) :
    Regularity (partonModel charge Δ) where
  measurable_g1 Q2 := by
    simp only [partonModel_g1]
    exact (Finset.aestronglyMeasurable_fun_sum _ fun f _ =>
      ((hm f Q2).1.add (hm f Q2).2).const_mul _).const_mul _
  measurable_g2 Q2 := by
    simp only [partonModel_g2]
    exact aestronglyMeasurable_const
  integrableOn_g1 Q2 := by
    simp only [partonModel_g1]
    exact (integrable_finsetSum _ fun f _ => ((hi f Q2).1.add (hi f Q2).2).const_mul _).const_mul _
  integrableOn_g2 Q2 := by
    simp only [partonModel_g2]
    exact integrableOn_zero

/-- The parton-model pair satisfies the polarized structural assumptions whenever the quark and
antiquark helicity distributions are supported in the physical interval, measurable, and
integrable there; the gluon entry of `Δ` is unconstrained. -/
theorem assumptions_partonModel (charge : Flavor → ℝ) {Δ : Pdf (Species Flavor)}
    (hΔ : ∀ f x Q2, x < 0 ∨ 1 < x → Δ (.quark f) x Q2 = 0 ∧ Δ (.antiquark f) x Q2 = 0)
    (hm : ∀ f Q2, AEStronglyMeasurable (fun x : ℝ => Δ (.quark f) x Q2) ∧
      AEStronglyMeasurable (fun x : ℝ => Δ (.antiquark f) x Q2))
    (hi : ∀ f Q2, IntegrableOn (fun x : ℝ => Δ (.quark f) x Q2) (Set.Icc 0 1) ∧
      IntegrableOn (fun x : ℝ => Δ (.antiquark f) x Q2) (Set.Icc 0 1)) :
    Assumptions (partonModel charge Δ) :=
  assumptions_iff.2
    ⟨hasPhysicalSupport_partonModel charge hΔ, regularity_partonModel charge hm hi⟩

/-- The parton-model pair satisfies the polarized structural assumptions whenever the quark and
antiquark helicity distributions are supported in the physical interval and the helicity
distribution is regular: the support postulate is the physical half of `PDF.Assumptions`, and
`PDF.Regularity` its analytic half, supplying the measurability together with the integrability
on the physical support. A user holding a full `PDF.Assumptions` bundle reaches this through its
`support` field and `.regularity` projection. -/
theorem assumptions_partonModel_of_pdfRegularity (charge : Flavor → ℝ)
    {Δ : Pdf (Species Flavor)}
    (hΔ : ∀ f x Q2, x < 0 ∨ 1 < x → Δ (.quark f) x Q2 = 0 ∧ Δ (.antiquark f) x Q2 = 0)
    (hr : PDF.Regularity Δ) :
    Assumptions (partonModel charge Δ) :=
  assumptions_partonModel charge hΔ
    (fun f Q2 => ⟨hr.measurable (.quark f) Q2, hr.measurable (.antiquark f) Q2⟩)
    fun f Q2 => ⟨hr.integrableOn (.quark f) Q2, hr.integrableOn (.antiquark f) Q2⟩

/-- **The parton-model `g₁` built from spin-density matrices satisfies the polarized
assumptions**, with support and integrability discharged rather than assumed: they follow from
the structural assumptions of the quark and of the antiquark spin-density families through
helicity dominance `|Δq| ≤ q`. Only the measurability of their helicity densities in `x` is
supplied. The gluon entry `ρ gluon` is unconstrained: it does not enter `g₁`. This is the
polarized counterpart of `PDF.assumptions_pdfOfSpinDensity`. -/
theorem assumptions_partonModel_helicityPdfOfSpinDensity (charge : Flavor → ℝ)
    {ρ : Species Flavor → ℝ → ℝ → SpinDensity}
    (hq : SpinDensityAssumptions fun f => ρ (.quark f))
    (hqbar : SpinDensityAssumptions fun f => ρ (.antiquark f))
    (hm : ∀ f Q2, AEStronglyMeasurable (fun x : ℝ => helicityPdfOfSpinDensity ρ (.quark f) x Q2) ∧
      AEStronglyMeasurable (fun x : ℝ => helicityPdfOfSpinDensity ρ (.antiquark f) x Q2)) :
    Assumptions (partonModel charge (helicityPdfOfSpinDensity ρ)) := by
  have hA := PDF.assumptions_pdfOfSpinDensity _ hq
  have hAbar := PDF.assumptions_pdfOfSpinDensity _ hqbar
  have hr := PDF.regularity_helicityPdfOfSpinDensity hA.regularity fun f Q2 => by
    simpa only [PDF.helicityPdfOfSpinDensity_apply] using (hm f Q2).1
  have hrbar := PDF.regularity_helicityPdfOfSpinDensity hAbar.regularity fun f Q2 => by
    simpa only [PDF.helicityPdfOfSpinDensity_apply] using (hm f Q2).2
  refine assumptions_partonModel charge (fun f x Q2 hx => ⟨?_, ?_⟩) hm fun f Q2 => ⟨?_, ?_⟩
  · simpa only [PDF.helicityPdfOfSpinDensity_apply] using
      PDF.helicityPdfOfSpinDensity_eq_zero hA.support f x Q2 hx
  · simpa only [PDF.helicityPdfOfSpinDensity_apply] using
      PDF.helicityPdfOfSpinDensity_eq_zero hAbar.support f x Q2 hx
  · simpa only [PDF.helicityPdfOfSpinDensity_apply] using hr.integrableOn f Q2
  · simpa only [PDF.helicityPdfOfSpinDensity_apply] using hrbar.integrableOn f Q2

/-- **The first moment of the parton-model `g₁`** is half the charge-weighted sum of the helicity
charges `∫₀¹ dx (Δq + Δqbar)`, written as the zeroth Mellin moments of the quark and antiquark
helicity densities. Only the quark and antiquark densities need be integrable. -/
theorem firstMomentG1_partonModel (charge : Flavor → ℝ) {Δ : Pdf (Species Flavor)} {Q2 : ℝ}
    (hi : ∀ f, IntegrableOn (fun x : ℝ => Δ (.quark f) x Q2) (Set.Icc 0 1) ∧
      IntegrableOn (fun x : ℝ => Δ (.antiquark f) x Q2) (Set.Icc 0 1)) :
    firstMomentG1 (partonModel charge Δ) Q2 =
      (1 / 2) * ∑ f, charge f ^ 2 *
        (mellinMoment Δ 0 (.quark f) Q2 + mellinMoment Δ 0 (.antiquark f) Q2) := by
  simp only [firstMomentG1, partonModel_g1, mellinMoment, pow_zero, one_mul]
  rw [integral_const_mul, integral_finsetSum]
  · congr 1
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [integral_const_mul, integral_add (hi f).1 (hi f).2]
  · exact fun f _ => ((hi f).1.add (hi f).2).const_mul _

/-- For the light flavours with their physical charges, the first moment of the parton-model
`g₁` is `(1/2) ((4/9) Δu + (1/9) Δd + (1/9) Δs)` in the helicity charges
`Δq = ∫₀¹ dx (Δq + Δqbar)`. -/
theorem firstMomentG1_partonModel_lightFlavor {Δ : Pdf (Species LightFlavor)} {Q2 : ℝ}
    (hi : ∀ f, IntegrableOn (fun x : ℝ => Δ (.quark f) x Q2) (Set.Icc 0 1) ∧
      IntegrableOn (fun x : ℝ => Δ (.antiquark f) x Q2) (Set.Icc 0 1)) :
    firstMomentG1 (partonModel LightFlavor.charge Δ) Q2 =
      (1 / 2) *
        ((4 / 9) * (mellinMoment Δ 0 (.quark .u) Q2 + mellinMoment Δ 0 (.antiquark .u) Q2) +
          (1 / 9) * (mellinMoment Δ 0 (.quark .d) Q2 + mellinMoment Δ 0 (.antiquark .d) Q2) +
          (1 / 9) * (mellinMoment Δ 0 (.quark .s) Q2 + mellinMoment Δ 0 (.antiquark .s) Q2)) := by
  rw [firstMomentG1_partonModel _ hi, LightFlavor.sum_univ, LightFlavor.charge_u,
    LightFlavor.charge_d, LightFlavor.charge_s]
  ring

/-- **The first moment of the parton-model `g₂`** vanishes at every scale, unconditionally:
`g₂` is identically zero at leading order, so no integrability hypothesis is needed. -/
@[simp]
theorem firstMomentG2_partonModel (charge : Flavor → ℝ) (Δ : Pdf (Species Flavor)) (Q2 : ℝ) :
    firstMomentG2 (partonModel charge Δ) Q2 = 0 := by
  simp [firstMomentG2]

/-- **The parton model satisfies the Burkhardt-Cottingham sum rule**, unconditionally: `g₂`
vanishes identically at leading order, so its first moment vanishes at every scale. -/
theorem burkhardtCottingham_partonModel (charge : Flavor → ℝ) (Δ : Pdf (Species Flavor)) :
    BurkhardtCottingham (partonModel charge Δ) :=
  ⟨fun Q2 => firstMomentG2_partonModel charge Δ Q2⟩

/-- **The parton model and the Ellis–Jaffe sum rule.** For the light flavours, the leading-order
parton-model `g₁` carries the flavour decomposition of `EllisJaffeSumRule` with vanishing
perturbative correction, its helicity charges being `∫₀¹ dx (Δq + Δqbar)`. The sum rule therefore
holds if and only if the strange helicity charge vanishes at every scale: that is the one
hypothesis the parton model does not supply. -/
theorem ellisJaffeSumRule_partonModel_iff {Δ : Pdf (Species LightFlavor)}
    (hi : ∀ f Q2, IntegrableOn (fun x : ℝ => Δ (.quark f) x Q2) (Set.Icc 0 1) ∧
      IntegrableOn (fun x : ℝ => Δ (.antiquark f) x Q2) (Set.Icc 0 1)) :
    EllisJaffeSumRule (partonModel LightFlavor.charge Δ)
        (fun Q2 => mellinMoment Δ 0 (.quark .u) Q2 + mellinMoment Δ 0 (.antiquark .u) Q2)
        (fun Q2 => mellinMoment Δ 0 (.quark .d) Q2 + mellinMoment Δ 0 (.antiquark .d) Q2)
        (fun Q2 => mellinMoment Δ 0 (.quark .s) Q2 + mellinMoment Δ 0 (.antiquark .s) Q2)
        (fun _ => 0) ↔
      ∀ Q2, mellinMoment Δ 0 (.quark .s) Q2 + mellinMoment Δ 0 (.antiquark .s) Q2 = 0 := by
  refine ⟨fun h => h.strange_unpolarized, fun hs => ⟨fun Q2 => ?_, hs⟩⟩
  rw [firstMomentG1_partonModel_lightFlavor (hi · Q2), add_zero, mul_one]

end Polarized
end DIS
end Scattering
end QFT
end EpsilonEridani
