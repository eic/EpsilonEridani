/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.ChargeConjugation
public import EpsilonEridani.QFT.Scattering.DIS.Inclusive.Moment
public import EpsilonEridani.QFT.Scattering.DIS.Isospin

/-!
# The Gottfried sum rule

The Gottfried sum is the `dx / x` moment (`momentF` with the weight `1/x`) of the proton-neutron
difference of `F₂`,

  `S_G(Q²) = ∫₀¹ (dx / x) (F₂^p(x, Q²) - F₂^n(x, Q²))`.

In the quark-parton model, with the neutron the isospin conjugate of the proton, the integrand is
`(e_u² - e_d²) (u + ubar - d - dbar)` (`DIS.f2LO_sub_f2LO_isospinConj`), and splitting
`u + ubar - d - dbar = (u - ubar) - (d - dbar) + 2 (ubar - dbar)` turns the sum into the
integrals of the valence differences and of the light-sea asymmetry. For the light-quark charges,
`e_u² - e_d² = 1/3`, and a proton with `∫₀¹ (u - ubar) = 2` and `∫₀¹ (d - dbar) = 1` this is the
**Gottfried sum rule**

  `S_G = 1/3 + (2/3) ∫₀¹ (ubar - dbar) dx`.

It is an identity, not an approximation: the value is `1/3` exactly when the light sea is
flavour-symmetric in the sense `∫₀¹ (ubar - dbar) = 0`, and a measured departure from `1/3` is a
measurement of that integral rather than a failure of the parton model. Flavour symmetry of the
light sea is therefore never assumed here; it is the hypothesis of
`gottfriedSum_lightFlavorCharge_quarkAddAntiquark_eq_one_third_iff` only.

## Convergence

The `1/x` weight is the one that can fail to converge, and a sea that rises like `1/x` at small
`x` has no zeroth moment: it is not integrable on the unit interval. What the sum rule needs is
weaker: only the nonsinglet differences `u - ubar`, `d - dbar` and `ubar - dbar` have to be
integrable, and these are the fields of `GottfriedIntegrable`. Separately integrable densities
supply them (`PDF.Regularity.gottfriedIntegrable`), but they are strictly weaker:
`gottfriedModel` is a density whose every species rises like `1/x`, so that the up antiquark
density is not integrable and `PDF.Regularity` fails, while the differences are constants, the
convergence hypotheses hold and the sum rule evaluates the Gottfried sum to `1/3 - 2a/3` for the
sea asymmetry `dbar - ubar = a`.

## Main definitions

* `gottfriedSum`: the Gottfried sum `∫₀¹ (dx / x) (F₂^p - F₂^n)` of a quark plus antiquark
  density, with the neutron its isospin conjugate, as a `momentF`.
* `GottfriedIntegrable`: integrability of the three nonsinglet differences on the unit interval.
* `gottfriedModel`: a density with a `1/x` rise in every species and a sea asymmetry `a`.

## Main statements

* `gottfriedSum_eq_integral_sub`: the structure-function form is the density form,
  `S_G = (e_u² - e_d²) ∫₀¹ (q_u - q_d)`, with no hypothesis.
* `gottfriedSum_quarkAddAntiquark`: the general identity
  `S_G = (e_u² - e_d²) (∫(u - ubar) - ∫(d - dbar) + 2 ∫(ubar - dbar))`.
* `gottfriedSum_lightFlavorCharge_quarkAddAntiquark`: the Gottfried sum rule
  `S_G = 1/3 + (2/3) ∫(ubar - dbar)`, and
  `gottfriedSum_lightFlavorCharge_quarkAddAntiquark_eq_one_third_iff`: `S_G = 1/3` exactly for a
  flavour-symmetric light sea.
* `gottfriedSum_lightFlavorCharge_quarkAddAntiquark_of_regularity`: the same in terms of
  `PDF.valenceNumber` and `PDF.mellinMoment`, for separately integrable densities.
* `gottfriedSum_gottfriedModel`, `not_regularity_gottfriedModel`: the sum rule applies to a
  density without integrable antiquark densities.

## References

* K. Gottfried, *Sum rule for high-energy electron-proton scattering*,
  Phys. Rev. Lett. **18** (1967) 1174.
* New Muon Collaboration (P. Amaudruz et al.), *Gottfried sum from the ratio `F₂ⁿ/F₂ᵖ`*,
  Phys. Rev. Lett. **66** (1991) 2712.
* R. Devenish and A. Cooper-Sarkar, *Deep Inelastic Scattering*, Oxford University Press (2004),
  ch. 5.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Inclusive

open MeasureTheory
open Particles.Parton (Species LightFlavor)
open Particles.Parton.PDF (Pdf IsPartonDensity Regularity isospinConj mellinMoment
  mellinMoment_eq_intervalIntegral quarkAddAntiquark quarkAddAntiquark_apply valenceNumber
  valenceNumber_eq_intervalIntegral)

/-!
## The Gottfried sum of a quark plus antiquark density
-/

section General

variable {ι : Type}

/-- **The convergence hypotheses of the Gottfried sum rule.** The two valence differences
`u - ubar` and `d - dbar` and the light-sea asymmetry `ubar - dbar` of the density `f` are
integrable on the unit interval at the scale `Q2`. The hypotheses are on differences, not on the
densities: a sea rising like `1/x` in both `ubar` and `dbar` with an integrable difference
satisfies them (`gottfriedIntegrable_gottfriedModel`). -/
structure GottfriedIntegrable (f : Pdf (Species ι)) (u d : ι) (Q2 : ℝ) : Prop where
  /-- The up valence density `u - ubar` is integrable on the unit interval. -/
  valenceUp :
    IntervalIntegrable (fun x => f (.quark u) x Q2 - f (.antiquark u) x Q2) volume 0 1
  /-- The down valence density `d - dbar` is integrable on the unit interval. -/
  valenceDown :
    IntervalIntegrable (fun x => f (.quark d) x Q2 - f (.antiquark d) x Q2) volume 0 1
  /-- The light-sea asymmetry `ubar - dbar` is integrable on the unit interval. -/
  seaAsymmetry :
    IntervalIntegrable (fun x => f (.antiquark u) x Q2 - f (.antiquark d) x Q2) volume 0 1

/-- Separately integrable densities satisfy the convergence hypotheses of the Gottfried sum rule
at every scale. -/
theorem _root_.EpsilonEridani.Particles.Parton.PDF.Regularity.gottfriedIntegrable
    {f : Pdf (Species ι)} (h : Regularity f) (u d : ι) (Q2 : ℝ) :
    GottfriedIntegrable f u d Q2 where
  valenceUp := (h.intervalIntegrable _ Q2 0 1).sub (h.intervalIntegrable _ Q2 0 1)
  valenceDown := (h.intervalIntegrable _ Q2 0 1).sub (h.intervalIntegrable _ Q2 0 1)
  seaAsymmetry := (h.intervalIntegrable _ Q2 0 1).sub (h.intervalIntegrable _ Q2 0 1)

variable [Fintype ι] [DecidableEq ι]

/-- **The Gottfried sum** `S_G(Q²) = ∫₀¹ (dx / x) (F₂^p - F₂^n)` at the scale `Q2`, for the quark
charges `e`. Here `q` is the proton's quark plus antiquark density, `F₂ = DIS.f2LO`, and the
neutron is the proton under the isospin involution exchanging the flavours `u` and `d`. -/
def gottfriedSum (e : ι → ℝ) (u d : ι) (q : Pdf ι) (Q2 : ℝ) : ℝ :=
  momentF (fun x Q2 => f2LO e q x Q2 - f2LO e (isospinConj u d q) x Q2) (fun x => x⁻¹) Q2

theorem gottfriedSum_def (e : ι → ℝ) (u d : ι) (q : Pdf ι) (Q2 : ℝ) :
    gottfriedSum e u d q Q2
      = momentF (fun x Q2 => f2LO e q x Q2 - f2LO e (isospinConj u d q) x Q2) (fun x => x⁻¹) Q2 :=
  (rfl)

/-- **The Gottfried sum in terms of the densities.** Dividing the proton-neutron difference
`x (e_u² - e_d²) (q_u - q_d)` by `x` gives `S_G = (e_u² - e_d²) ∫₀¹ (q_u - q_d)`. No hypothesis is
needed: the two integrands agree on `(0, 1]`, so either both integrals exist or both are `0`. -/
theorem gottfriedSum_eq_integral_sub (e : ι → ℝ) (u d : ι) (q : Pdf ι) (Q2 : ℝ) :
    gottfriedSum e u d q Q2 = (e u ^ 2 - e d ^ 2) * ∫ x in (0 : ℝ)..1, (q u x Q2 - q d x Q2) := by
  rw [gottfriedSum_def, momentF_def, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => ?_)
  rw [Set.uIoc_of_le zero_le_one] at hx
  rw [f2LO_sub_f2LO_isospinConj]
  field_simp [hx.1.ne']

/-- **The Gottfried identity.** Under the convergence hypotheses, the Gottfried sum of a density
splits into the integrals of its valence differences and its light-sea asymmetry,
`S_G = (e_u² - e_d²) (∫₀¹ (u - ubar) - ∫₀¹ (d - dbar) + 2 ∫₀¹ (ubar - dbar))`. -/
theorem gottfriedSum_quarkAddAntiquark {f : Pdf (Species ι)} {u d : ι} {Q2 : ℝ}
    (h : GottfriedIntegrable f u d Q2) (e : ι → ℝ) :
    gottfriedSum e u d (quarkAddAntiquark f) Q2
      = (e u ^ 2 - e d ^ 2) *
          ((∫ x in (0 : ℝ)..1, (f (.quark u) x Q2 - f (.antiquark u) x Q2))
            - (∫ x in (0 : ℝ)..1, (f (.quark d) x Q2 - f (.antiquark d) x Q2))
            + 2 * ∫ x in (0 : ℝ)..1, (f (.antiquark u) x Q2 - f (.antiquark d) x Q2)) := by
  rw [gottfriedSum_eq_integral_sub]
  congr 1
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_sub h.valenceUp h.valenceDown,
    ← intervalIntegral.integral_add (h.valenceUp.sub h.valenceDown)
      (h.seaAsymmetry.const_mul 2)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [quarkAddAntiquark_apply]
  ring

end General

/-!
## The light flavours: the Gottfried sum rule
-/

section LightFlavor

open Particles.Parton.LightFlavor

variable {f : Pdf (Species LightFlavor)} {Q2 : ℝ}

/-- **The Gottfried sum rule.** For the light-quark charges and a proton with
`∫₀¹ (u - ubar) = 2` and `∫₀¹ (d - dbar) = 1`, under the convergence hypotheses on the nonsinglet
differences,
`∫₀¹ (dx / x) (F₂^p - F₂^n) = 1/3 + (2/3) ∫₀¹ (ubar - dbar)`. -/
theorem gottfriedSum_lightFlavorCharge_quarkAddAntiquark (h : GottfriedIntegrable f u d Q2)
    (hu : ∫ x in (0 : ℝ)..1, (f (.quark u) x Q2 - f (.antiquark u) x Q2) = 2)
    (hd : ∫ x in (0 : ℝ)..1, (f (.quark d) x Q2 - f (.antiquark d) x Q2) = 1) :
    gottfriedSum charge u d (quarkAddAntiquark f) Q2
      = 1 / 3 + 2 / 3 * ∫ x in (0 : ℝ)..1, (f (.antiquark u) x Q2 - f (.antiquark d) x Q2) := by
  rw [gottfriedSum_quarkAddAntiquark h, hu, hd, charge_u, charge_d]
  ring

/-- **The Gottfried sum is `1/3` exactly for a flavour-symmetric light sea.** Under the hypotheses
of the Gottfried sum rule, `S_G = 1/3` if and only if `∫₀¹ (ubar - dbar) = 0`. -/
theorem gottfriedSum_lightFlavorCharge_quarkAddAntiquark_eq_one_third_iff
    (h : GottfriedIntegrable f u d Q2)
    (hu : ∫ x in (0 : ℝ)..1, (f (.quark u) x Q2 - f (.antiquark u) x Q2) = 2)
    (hd : ∫ x in (0 : ℝ)..1, (f (.quark d) x Q2 - f (.antiquark d) x Q2) = 1) :
    gottfriedSum charge u d (quarkAddAntiquark f) Q2 = 1 / 3
      ↔ ∫ x in (0 : ℝ)..1, (f (.antiquark u) x Q2 - f (.antiquark d) x Q2) = 0 := by
  rw [gottfriedSum_lightFlavorCharge_quarkAddAntiquark h hu hd]
  constructor <;> intro h' <;> linarith

/-- **The Gottfried sum rule for separately integrable densities.** If every density is
integrable and the up and down valence numbers are `2` and `1`, the sea asymmetry is the
difference of the zeroth moments of the antiquark densities:
`S_G = 1/3 + (2/3) (∫₀¹ ubar - ∫₀¹ dbar)`. -/
theorem gottfriedSum_lightFlavorCharge_quarkAddAntiquark_of_regularity (h : Regularity f)
    (hu : valenceNumber f u Q2 = 2) (hd : valenceNumber f d Q2 = 1) :
    gottfriedSum charge u d (quarkAddAntiquark f) Q2
      = 1 / 3 + 2 / 3 *
          (mellinMoment f 0 (.antiquark u) Q2 - mellinMoment f 0 (.antiquark d) Q2) := by
  have hi : ∀ s, IntervalIntegrable (fun x => f s x Q2) volume 0 1 :=
    fun s => h.intervalIntegrable s Q2 0 1
  rw [valenceNumber_eq_intervalIntegral (hi _) (hi _)] at hu hd
  rw [gottfriedSum_lightFlavorCharge_quarkAddAntiquark (h.gottfriedIntegrable u d Q2) hu hd,
    mellinMoment_eq_intervalIntegral, mellinMoment_eq_intervalIntegral,
    ← intervalIntegral.integral_sub]
  · simp only [pow_zero, one_mul]
  all_goals simpa using hi _

/-!
## A density without integrable antiquark densities
-/

/-- **A density with a `1/x` sea.** Every species has the density `1/x` on the unit interval,
on top of which the up and down quarks carry `2` and `1 + a` and the down antiquark carries `a`.
The nonsinglet differences are constants there: `q_i - qbar_i` integrates to `2`, `1` and `0` on
the unit interval for `u`, `d` and `s`, and the light-sea asymmetry is `dbar - ubar = a`. The
densities themselves have no zeroth moment: they are not integrable on the unit interval. So
`PDF.valenceNumber` of this model, a difference of two zeroth `PDF.mellinMoment`s, is `0` for
every flavour, and `gottfriedSum_lightFlavorCharge_quarkAddAntiquark_of_regularity` does not
apply to it. -/
def gottfriedModel (a : ℝ) : Pdf (Species LightFlavor) := fun s x _ =>
  (Set.Icc (0 : ℝ) 1).indicator
    (fun x => x⁻¹ + match s with
      | .quark .u => 2
      | .quark .d => 1 + a
      | .antiquark .d => a
      | _ => 0) x

/-- For a nonnegative sea asymmetry `a`, `gottfriedModel a` is a parton density. -/
theorem isPartonDensity_gottfriedModel {a : ℝ} (ha : 0 ≤ a) :
    IsPartonDensity (gottfriedModel a) where
  support s x Q2 hx := by
    have : x ∉ Set.Icc (0 : ℝ) 1 := fun h => by rcases hx with hx | hx <;> linarith [h.1, h.2]
    simp only [gottfriedModel, Set.indicator_of_notMem this]
  nonneg s x Q2 h0 h1 := by
    simp only [gottfriedModel, Set.indicator_of_mem (Set.mem_Icc.2 ⟨h0, h1⟩)]
    have := inv_nonneg.2 h0
    rcases s with ((_ | _ | _) | (_ | _ | _) | _) <;> dsimp only <;> linarith

/-- The up valence density of `gottfriedModel a` is `2` on the unit interval. -/
lemma gottfriedModel_quark_u_sub_antiquark_u_eqOn (a Q2 : ℝ) :
    Set.EqOn (fun x => gottfriedModel a (.quark u) x Q2 - gottfriedModel a (.antiquark u) x Q2)
      (fun _ => 2) (Set.uIcc 0 1) := fun x hx => by
  rw [Set.uIcc_of_le zero_le_one] at hx
  simp only [gottfriedModel, Set.indicator_of_mem hx]
  ring

/-- The down valence density of `gottfriedModel a` is `1` on the unit interval. -/
lemma gottfriedModel_quark_d_sub_antiquark_d_eqOn (a Q2 : ℝ) :
    Set.EqOn (fun x => gottfriedModel a (.quark d) x Q2 - gottfriedModel a (.antiquark d) x Q2)
      (fun _ => 1) (Set.uIcc 0 1) := fun x hx => by
  rw [Set.uIcc_of_le zero_le_one] at hx
  simp only [gottfriedModel, Set.indicator_of_mem hx]
  ring

/-- The light-sea asymmetry `ubar - dbar` of `gottfriedModel a` is `-a` on the unit interval. -/
lemma gottfriedModel_antiquark_u_sub_antiquark_d_eqOn (a Q2 : ℝ) :
    Set.EqOn (fun x => gottfriedModel a (.antiquark u) x Q2 - gottfriedModel a (.antiquark d) x Q2)
      (fun _ => -a) (Set.uIcc 0 1) := fun x hx => by
  rw [Set.uIcc_of_le zero_le_one] at hx
  simp only [gottfriedModel, Set.indicator_of_mem hx]
  ring

/-- `gottfriedModel a` satisfies the convergence hypotheses of the Gottfried sum rule. -/
theorem gottfriedIntegrable_gottfriedModel (a Q2 : ℝ) :
    GottfriedIntegrable (gottfriedModel a) u d Q2 where
  valenceUp := (intervalIntegrable_congr
    ((gottfriedModel_quark_u_sub_antiquark_u_eqOn a Q2).mono Set.uIoc_subset_uIcc)).2
      intervalIntegrable_const
  valenceDown := (intervalIntegrable_congr
    ((gottfriedModel_quark_d_sub_antiquark_d_eqOn a Q2).mono Set.uIoc_subset_uIcc)).2
      intervalIntegrable_const
  seaAsymmetry := (intervalIntegrable_congr
    ((gottfriedModel_antiquark_u_sub_antiquark_d_eqOn a Q2).mono Set.uIoc_subset_uIcc)).2
      intervalIntegrable_const

/-- The up antiquark density of `gottfriedModel a` is not integrable on the unit interval: it is
`1/x` there. -/
theorem not_intervalIntegrable_gottfriedModel_antiquark_u (a Q2 : ℝ) :
    ¬ IntervalIntegrable (fun x => gottfriedModel a (.antiquark u) x Q2) volume 0 1 := by
  intro h
  have hinv : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 := h.congr fun x hx => by
    rw [Set.uIoc_of_le zero_le_one] at hx
    simp [gottfriedModel, Set.indicator_of_mem (Set.Ioc_subset_Icc_self hx)]
  simp at hinv

/-- `gottfriedModel a` is not a regular density, so the Gottfried sum rule for it does not follow
from `gottfriedSum_lightFlavorCharge_quarkAddAntiquark_of_regularity`. -/
theorem not_regularity_gottfriedModel (a : ℝ) : ¬ Regularity (gottfriedModel a) := fun h =>
  not_intervalIntegrable_gottfriedModel_antiquark_u a 0 (h.intervalIntegrable _ 0 0 1)

/-- **The Gottfried sum of the `1/x`-sea model** is `1/3 - 2a/3`: it differs from `1/3` by `2/3`
times the light-sea asymmetry `∫₀¹ (ubar - dbar) = -a`, although no antiquark density of the model
has a zeroth moment. -/
theorem gottfriedSum_gottfriedModel (a Q2 : ℝ) :
    gottfriedSum charge u d (quarkAddAntiquark (gottfriedModel a)) Q2 = 1 / 3 - 2 / 3 * a := by
  rw [gottfriedSum_lightFlavorCharge_quarkAddAntiquark (gottfriedIntegrable_gottfriedModel a Q2)
    ((intervalIntegral.integral_congr (gottfriedModel_quark_u_sub_antiquark_u_eqOn a Q2)).trans
      (by simp))
    ((intervalIntegral.integral_congr (gottfriedModel_quark_d_sub_antiquark_d_eqOn a Q2)).trans
      (by simp)),
    intervalIntegral.integral_congr (gottfriedModel_antiquark_u_sub_antiquark_d_eqOn a Q2)]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul]
  ring

end LightFlavor

end Inclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
