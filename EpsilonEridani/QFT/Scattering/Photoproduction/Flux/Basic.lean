/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.BesselK.Basic
public import EpsilonEridani.QFT.Scattering.Photoproduction.Kinematics.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The integrated equivalent-photon flux of a point source

A relativistic point charge `Z` with Lorentz factor `γ`, viewed at transverse separations beyond a
minimum impact parameter `b_min`, carries an equivalent-photon spectrum whose number of photons per
unit photon energy `k` is

  `n(k) = (2 Z² α / π) (1/k) [ ξ K₀(ξ) K₁(ξ) − (ξ²/2) (K₁(ξ)² − K₀(ξ)²) ]`,  `ξ = k b_min / γ`,

with `K₀` and `K₁` the modified Bessel functions of the second kind of `EpsilonEridani.besselK`.
This module defines the dimensionless bracket as `photonFluxProfile` and the spectrum itself as
`ChargedSource.integratedPhotonFlux`, and proves the positivity, the large-argument suppression
and the small-argument logarithm of both.

The organising identity is `photonFluxProfile_eq_integral`:

  `photonFluxProfile ξ = ∫_ξ^∞ t K₁(t)² dt`,

a consequence of `hasDerivAt_photonFluxProfile`, which says that the derivative of the bracket is
`-ξ K₁(ξ)²`. Everything else follows: the profile is positive
(`photonFluxProfile_pos`) and strictly decreasing (`strictAntiOn_photonFluxProfile`); it is
suppressed like `exp (-2ξ)` at large `ξ` (`abs_photonFluxProfile_le`), which is the coherence
cutoff appearing as a decay rate rather than as a sharp edge; and it grows like `-log ξ` at small
`ξ` (`isEquivalent_photonFluxProfile_neg_log`), so the spectrum behaves as the inverse photon
energy times the logarithm of the ratio of the maximal photon energy `γ / b_min` to the actual one
(`ChargedSource.isEquivalent_integratedPhotonFlux_neg_log`). The integrand `t K₁(t)²` of the
organising identity is, up to normalisation, the impact-parameter differential flux, so that
identity is also what fixes the relative normalisation of the two forms of the spectrum.

The charge radius carried by `ChargedSource` plays no role here: this is the point-source
spectrum, and `b_min` is an external cutoff on the impact parameter rather than a property of the
source.

## References

* C. F. von Weizsäcker, *Ausstrahlung bei Stößen sehr schneller Elektronen*, Z. Phys. **88**
  (1934) 612; E. J. Williams, *Nature of the high energy particles of penetrating radiation*,
  Phys. Rev. **45** (1934) 729.
* J. D. Jackson, *Classical Electrodynamics*, 3rd edition, Wiley (1999), chapter 15.
* C. A. Bertulani and G. Baur, *Electromagnetic processes in relativistic heavy ion collisions*,
  Phys. Rep. **163** (1988) 299, where the bracket appears in this form.
* A. J. Baltz et al., *The physics of ultraperipheral collisions at the LHC*, Phys. Rep. **458**
  (2008) 1, section 2.
-/

public section

noncomputable section

open Asymptotics Real MeasureTheory Set Filter Topology

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace Photoproduction

/-! ### The dimensionless profile -/

/-- The dimensionless profile `ξ K₀(ξ) K₁(ξ) − (ξ²/2) (K₁(ξ)² − K₀(ξ)²)` of the integrated
equivalent-photon flux, as a function of the scaling variable `ξ = k b_min / γ` built from the
photon energy, the minimum impact parameter and the Lorentz factor of the source. By
`photonFluxProfile_eq_integral` it is `∫_ξ^∞ t K₁(t)² dt`. -/
def photonFluxProfile (ξ : ℝ) : ℝ :=
  ξ * besselK 0 ξ * besselK 1 ξ - ξ ^ 2 / 2 * (besselK 1 ξ ^ 2 - besselK 0 ξ ^ 2)

/-- Defining expression for `photonFluxProfile`. -/
theorem photonFluxProfile_def (ξ : ℝ) : photonFluxProfile ξ =
    ξ * besselK 0 ξ * besselK 1 ξ - ξ ^ 2 / 2 * (besselK 1 ξ ^ 2 - besselK 0 ξ ^ 2) := (rfl)

/-- The derivative of the profile is the single term `-ξ K₁(ξ)²`. -/
theorem hasDerivAt_photonFluxProfile {ξ : ℝ} (hξ : 0 < ξ) :
    HasDerivAt photonFluxProfile (-(ξ * besselK 1 ξ ^ 2)) ξ := by
  -- The two Bessel derivative relations cancel every contribution but one.
  have hprofile : photonFluxProfile = fun y : ℝ ↦
      y * besselK 0 y * besselK 1 y - y ^ 2 / 2 * (besselK 1 y ^ 2 - besselK 0 y ^ 2) :=
    funext photonFluxProfile_def
  have hξne : ξ ≠ 0 := hξ.ne'
  have h₀ := hasDerivAt_besselK_zero hξ
  have h₁ := hasDerivAt_besselK_one hξ
  have e₁ := ((hasDerivAt_id' (x := ξ)).fun_mul h₀).fun_mul h₁
  have e₂ := ((hasDerivAt_pow 2 ξ).div_const 2).fun_mul ((h₁.fun_pow 2).fun_sub (h₀.fun_pow 2))
  rw [hprofile]
  exact (e₁.fun_sub e₂).congr_deriv (by field_simp; ring)

/-- The profile is suppressed like `exp (-2ξ)` at large argument, at the rate set by the decay of
the two Bessel functions. This is the coherence cutoff of the point-source spectrum in its exact
form: a decay rate, not a sharp edge. -/
theorem abs_photonFluxProfile_le {ξ : ℝ} (hξ : 0 < ξ) :
    |photonFluxProfile ξ| ≤ (1 + ξ) ^ 3 / ξ * exp (-(2 * ξ)) := by
  have hξne : ξ ≠ 0 := hξ.ne'
  have hK₀ := besselK_pos 0 hξ
  have hK₁ := besselK_pos 1 hξ
  have hle : besselK 0 ξ ≤ besselK 1 ξ := besselK_le_besselK (by norm_num) ξ
  have hsq : besselK 0 ξ ^ 2 ≤ besselK 1 ξ ^ 2 := by nlinarith
  have hbound : |photonFluxProfile ξ| ≤ (ξ + ξ ^ 2) * besselK 1 ξ ^ 2 := by
    rw [photonFluxProfile_def, abs_le]
    refine ⟨?_, ?_⟩
    · nlinarith [mul_nonneg (mul_nonneg hξ.le hK₀.le) hK₁.le,
        mul_nonneg (sq_nonneg ξ) (sq_nonneg (besselK 0 ξ)),
        mul_nonneg hξ.le (sq_nonneg (besselK 1 ξ)),
        mul_nonneg (sq_nonneg ξ) (sq_nonneg (besselK 1 ξ))]
    · nlinarith [mul_nonneg (mul_nonneg hξ.le hK₁.le) (sub_nonneg.2 hle),
        mul_nonneg (sq_nonneg ξ) (sub_nonneg.2 hsq),
        mul_nonneg (sq_nonneg ξ) (sq_nonneg (besselK 1 ξ))]
  have hexp : besselK 1 ξ ^ 2 ≤ (exp (-ξ) * (1 + 1 / ξ)) ^ 2 := by
    nlinarith [besselK_one_le_exp_neg_mul hξ, besselK_nonneg 1 ξ]
  calc |photonFluxProfile ξ| ≤ (ξ + ξ ^ 2) * besselK 1 ξ ^ 2 := hbound
    _ ≤ (ξ + ξ ^ 2) * (exp (-ξ) * (1 + 1 / ξ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = (1 + ξ) ^ 3 / ξ * exp (-(2 * ξ)) := by
        rw [show exp (-(2 * ξ)) = exp (-ξ) * exp (-ξ) by rw [← exp_add]; congr 1; ring]
        field_simp
        ring

/-- The profile vanishes at large argument. -/
theorem tendsto_photonFluxProfile_atTop : Tendsto photonFluxProfile atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun ξ : ℝ ↦ 8 * (ξ ^ 2 * exp (-ξ))) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ξ hξ
    have hξ0 : 0 < ξ := lt_of_lt_of_le one_pos hξ
    refine (abs_photonFluxProfile_le hξ0).trans ?_
    have h₁ : (1 + ξ) ^ 3 / ξ ≤ 8 * ξ ^ 2 := by
      rw [div_le_iff₀ hξ0]
      nlinarith [sq_nonneg (ξ - 1), sq_nonneg ξ]
    have h₂ : exp (-(2 * ξ)) ≤ exp (-ξ) := exp_le_exp.2 (by linarith)
    calc (1 + ξ) ^ 3 / ξ * exp (-(2 * ξ)) ≤ 8 * ξ ^ 2 * exp (-ξ) := by gcongr
      _ = 8 * (ξ ^ 2 * exp (-ξ)) := by ring
  · simpa using (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul 8

/-- **The profile is the tail integral of `t K₁(t)²`.** The integrand is, up to normalisation, the
impact-parameter differential flux of the same point source, so this identity is what relates the
integrated spectrum to its impact-parameter form. -/
theorem photonFluxProfile_eq_integral {ξ : ℝ} (hξ : 0 < ξ) :
    photonFluxProfile ξ = ∫ t in Ioi ξ, t * besselK 1 t ^ 2 := by
  have hcont : ContinuousWithinAt (fun t ↦ -photonFluxProfile t) (Ici ξ) ξ :=
    ((hasDerivAt_photonFluxProfile hξ).continuousAt.fun_neg).continuousWithinAt
  have hderiv : ∀ t ∈ Ioi ξ,
      HasDerivAt (fun t ↦ -photonFluxProfile t) (t * besselK 1 t ^ 2) t := fun t ht ↦ by
    simpa using (hasDerivAt_photonFluxProfile (hξ.trans ht)).fun_neg
  have hnonneg : ∀ t ∈ Ioi ξ, 0 ≤ t * besselK 1 t ^ 2 := fun t ht ↦
    mul_nonneg (hξ.trans ht).le (sq_nonneg _)
  have hlim : Tendsto (fun t ↦ -photonFluxProfile t) atTop (𝓝 0) := by
    simpa using tendsto_photonFluxProfile_atTop.neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg hlim]
  ring

/-- The profile is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_photonFluxProfile : StrictAntiOn photonFluxProfile (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0)
    (fun ξ hξ ↦ (hasDerivAt_photonFluxProfile hξ).continuousAt.continuousWithinAt) fun ξ hξ ↦ ?_
  rw [interior_Ioi] at hξ
  have hξ' : 0 < ξ := hξ
  have hK₁ := besselK_pos 1 hξ'
  rw [(hasDerivAt_photonFluxProfile hξ').deriv]
  have : 0 < ξ * besselK 1 ξ ^ 2 := by positivity
  linarith

/-- The profile is positive on `(0, ∞)`. -/
theorem photonFluxProfile_pos {ξ : ℝ} (hξ : 0 < ξ) : 0 < photonFluxProfile ξ := by
  -- The profile is nonnegative, being a tail integral of a nonnegative function, and strictly
  -- decreasing, so it is strictly above its value one unit to the right.
  have hnonneg : ∀ {y : ℝ}, 0 < y → 0 ≤ photonFluxProfile y := fun {y} hy ↦ by
    rw [photonFluxProfile_eq_integral hy]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht ↦
      mul_nonneg (hy.trans ht).le (sq_nonneg _)
  exact (hnonneg (show (0 : ℝ) < ξ + 1 by linarith)).trans_lt
    (strictAntiOn_photonFluxProfile hξ (show (0 : ℝ) < ξ + 1 by linarith) (by linarith))

/-- **The profile is logarithmic at the origin:** `photonFluxProfile ξ ~ -log ξ` as `ξ → 0⁺`. -/
theorem isEquivalent_photonFluxProfile_neg_log :
    photonFluxProfile ~[𝓝[>] (0 : ℝ)] fun ξ ↦ -log ξ := by
  -- The leading behaviour comes from `ξ K₀(ξ) K₁(ξ)`, in which `ξ K₁(ξ) → 1` and
  -- `K₀(ξ) ~ -log ξ`; the two squared terms stay bounded and divide away.
  have hlog : Tendsto (fun ξ : ℝ ↦ -log ξ) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have hpos : ∀ᶠ ξ in 𝓝[>] (0 : ℝ), 0 < -log ξ := hlog.eventually_gt_atTop 0
  rw [isEquivalent_iff_tendsto_one (hpos.mono fun ξ h ↦ ne_of_gt h)]
  -- the leading term, and the bounded term that divides away
  have hlead : Tendsto (fun ξ : ℝ ↦ besselK 0 ξ / (-log ξ) * (ξ * besselK 1 ξ))
      (𝓝[>] 0) (𝓝 1) := by
    have h := (isEquivalent_iff_tendsto_one (hpos.mono fun ξ h ↦ ne_of_gt h)).1
      isEquivalent_besselK_zero_neg_log
    simpa using h.mul tendsto_mul_besselK_one_nhdsGT_zero
  have hsmall : Tendsto (fun ξ : ℝ ↦ (ξ * besselK 1 ξ) ^ 2 / (2 * -log ξ)) (𝓝[>] 0) (𝓝 0) := by
    refine Tendsto.div_atTop (a := 1) ?_ (hlog.const_mul_atTop two_pos)
    simpa using tendsto_mul_besselK_one_nhdsGT_zero.pow 2
  have hdiff : Tendsto (fun ξ : ℝ ↦ besselK 0 ξ / (-log ξ) * (ξ * besselK 1 ξ)
      - (ξ * besselK 1 ξ) ^ 2 / (2 * -log ξ)) (𝓝[>] 0) (𝓝 1) := by
    have h := hlead.sub hsmall
    rwa [sub_zero] at h
  -- Both bounds are the same computation: the quotient is `hlead - hsmall + C` with
  -- `0 ≤ C ≤ hsmall`, so it lies between `hlead - hsmall` and `hlead`.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hdiff hlead ?_ ?_
  all_goals
    filter_upwards [self_mem_nhdsWithin, hpos] with ξ (hξ : 0 < ξ) hM
    have hK₀ := besselK_pos 0 hξ
    have hK₁ := besselK_pos 1 hξ
    have hle : besselK 0 ξ ≤ besselK 1 ξ := besselK_le_besselK (by norm_num) ξ
    have hlne : log ξ ≠ 0 := neg_ne_zero.mp (ne_of_gt hM)
    have hkey : photonFluxProfile ξ / (-log ξ)
        = besselK 0 ξ / (-log ξ) * (ξ * besselK 1 ξ) - (ξ * besselK 1 ξ) ^ 2 / (2 * -log ξ)
          + (ξ * besselK 0 ξ) ^ 2 / (2 * -log ξ) := by
      rw [photonFluxProfile_def]
      field_simp
      ring
    have hd : (0 : ℝ) < (2 * -log ξ)⁻¹ := inv_pos.2 (by linarith)
    have hCnonneg : 0 ≤ (ξ * besselK 0 ξ) ^ 2 / (2 * -log ξ) :=
      div_nonneg (sq_nonneg _) (by linarith)
    have hCle : (ξ * besselK 0 ξ) ^ 2 / (2 * -log ξ) ≤ (ξ * besselK 1 ξ) ^ 2 / (2 * -log ξ) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ hd.le
      nlinarith [mul_pos hξ hK₀, mul_le_mul_of_nonneg_left hle hξ.le]
    rw [Pi.div_apply, hkey]
    linarith

/-! ### The spectrum of a charged source -/

namespace Kinematics.ChargedSource

/-- The integrated equivalent-photon flux `n(k)` of a point source `s` of charge `Z = s.charge`
and Lorentz factor `γ = s.gamma`, at fine-structure constant `α`, photon energy `k` and minimum
impact parameter `b_min`:

  `n(k) = (2 Z² α / π) (1/k) photonFluxProfile (k b_min / γ)`.

It counts photons per unit photon energy. -/
def integratedPhotonFlux (s : ChargedSource) (α bMin k : ℝ) : ℝ :=
  2 * s.charge ^ 2 * α / π / k * photonFluxProfile (k * bMin / s.gamma)

/-- Defining expression for `ChargedSource.integratedPhotonFlux`. -/
theorem integratedPhotonFlux_def (s : ChargedSource) (α bMin k : ℝ) :
    s.integratedPhotonFlux α bMin k =
      2 * s.charge ^ 2 * α / π / k * photonFluxProfile (k * bMin / s.gamma) := (rfl)

variable {s : ChargedSource} {α bMin k : ℝ}

/-- The flux of a charged source is positive throughout the physical range of its arguments. -/
theorem integratedPhotonFlux_pos (hZ : s.charge ≠ 0) (hγ : 0 < s.gamma) (hα : 0 < α)
    (hb : 0 < bMin) (hk : 0 < k) : 0 < s.integratedPhotonFlux α bMin k := by
  have hξ : 0 < k * bMin / s.gamma := by positivity
  have hZ' : 0 < s.charge ^ 2 := by positivity
  have hnum : 0 < 2 * s.charge ^ 2 * α / π / k :=
    div_pos (div_pos (mul_pos (mul_pos two_pos hZ') hα) pi_pos) hk
  rw [integratedPhotonFlux_def]
  exact mul_pos hnum (photonFluxProfile_pos hξ)

/-- **The flux is proportional to the squared charge.** Two point sources at the same Lorentz
factor, seen at the same minimum impact parameter and photon energy, have fluxes in the ratio of
their squared charges; stated in cross-multiplied form, so that it needs no non-vanishing
hypothesis. -/
theorem charge_sq_mul_integratedPhotonFlux_eq_charge_sq_mul (s t : ChargedSource)
    (h : s.gamma = t.gamma) (α bMin k : ℝ) :
    t.charge ^ 2 * s.integratedPhotonFlux α bMin k
      = s.charge ^ 2 * t.integratedPhotonFlux α bMin k := by
  rw [integratedPhotonFlux_def, integratedPhotonFlux_def, h]
  ring

/-- **At small photon energy the flux is the inverse energy times a logarithm.** For a point
source the maximal coherent photon energy is `γ / b_min`, and the spectrum behaves as
`(2 Z² α / π) (1/k) log (γ / (k b_min))`, the logarithm of the ratio of that maximum to the actual
photon energy. -/
theorem isEquivalent_integratedPhotonFlux_neg_log (s : ChargedSource) (hγ : 0 < s.gamma)
    (hb : 0 < bMin) (α : ℝ) :
    (fun k ↦ s.integratedPhotonFlux α bMin k) ~[𝓝[>] (0 : ℝ)]
      fun k ↦ 2 * s.charge ^ 2 * α / π / k * log (s.gamma / (k * bMin)) := by
  have hscale : Tendsto (fun k : ℝ ↦ k * bMin / s.gamma) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hc : Continuous fun k : ℝ ↦ k * bMin / s.gamma := by fun_prop
      exact (hc.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with k (hk : 0 < k)
      exact (show (0 : ℝ) < k * bMin / s.gamma by positivity)
  have hprofile := isEquivalent_photonFluxProfile_neg_log.comp_tendsto hscale
  refine ((IsEquivalent.refl (u := fun k : ℝ ↦ 2 * s.charge ^ 2 * α / π / k)).mul
    hprofile).congr_left (Eventually.of_forall fun k ↦ ?_) |>.congr_right
      (Eventually.of_forall fun k ↦ ?_)
  · exact (integratedPhotonFlux_def s α bMin k).symm
  · simp only [Pi.mul_apply, Function.comp_apply]
    rw [← log_inv, inv_div]

end Kinematics.ChargedSource

end Photoproduction
end Scattering
end QFT
end EpsilonEridani
