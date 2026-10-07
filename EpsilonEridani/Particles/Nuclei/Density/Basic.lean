/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Nuclei.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Physlib.SpaceAndTime.Space.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Coordinate-space nuclear density profiles

A nuclear density profile is the nucleon number density `ρ_A : ℝ³ → ℝ` of a nucleus: a
non-negative function on physical space whose integral is the mass number,
`∫ ρ_A d³r = A`. It is normalised to `A` rather than to one, because the geometric
quantities built from it (the thickness function, multiple-scattering corrections) count
nucleons, and a probability-normalised profile would shift their mass-number dependence by one
power of `A`.

Physical space is Physlib's `Space`. This file constructs the three spherically symmetric
profiles of nuclear geometry, written as functions `ℝ → ℝ` of the radius and evaluated at the
distance `‖x‖` from the origin of `Space`, and proves each normalisable:

* the hard sphere `3A / (4π R³) · 1_{r ≤ R}`;
* the Gaussian `A (π R²)^{-3/2} exp(-r²/R²)`;
* the two-parameter Fermi, or Woods–Saxon, profile `ρ₀ / (1 + exp((r - R)/a))`, with
  half-density radius `R` and surface thickness `a`, whose central density `ρ₀` is fixed by the
  normalisation. The relevant integral has no elementary closed form, so `ρ₀` is defined as `A`
  divided by the integral of the profile with `ρ₀ = 1`, and shown to be the unique normalising
  value and positive.

## Main definitions

* `EpsilonEridani.Nucleus.DensityProfile nuc`: a non-negative function on `Space` with integral
  the mass number of `nuc`.
* `EpsilonEridani.hardSphereDensity`, `gaussianDensity`, `woodsSaxonDensity`: the three
  radial profiles.
* `EpsilonEridani.woodsSaxonCentralDensity m R a`: the central density normalising the
  Woods–Saxon profile to `m`.
* `EpsilonEridani.Nucleus.DensityProfile.hardSphere`, `gaussian`, `woodsSaxon`: the bundled
  profiles of a nucleus.

## Main statements

* `EpsilonEridani.integral_hardSphereDensity` and
  `EpsilonEridani.integral_gaussianDensity`: the two closed-form profiles integrate to
  their normalisation parameter.
* `EpsilonEridani.integrable_woodsSaxonDensity`: the Woods–Saxon profile is integrable
  over `ℝ³` for every positive surface thickness.
* `EpsilonEridani.existsUnique_integral_woodsSaxonDensity_eq`: for `0 < a`, exactly one
  central density normalises the Woods–Saxon profile to a given value, and
  `EpsilonEridani.woodsSaxonCentralDensity_pos` shows it is positive when the value is.

## References

* EIC Yellow Report, `arXiv:2103.05419`, Vol. II, §7.3.3.
* H. de Vries, C. W. de Jager and C. de Vries, *Nuclear charge-density-distribution parameters
  from elastic electron scattering*, At. Data Nucl. Data Tables 36 (1987) 495.
-/

public section

noncomputable section

namespace EpsilonEridani

open MeasureTheory Real Metric Set

namespace Nucleus

/-- A coordinate-space density profile of the nucleus `nuc`: a non-negative nucleon number density
on physical space whose integral is the mass number. -/
@[ext]
structure DensityProfile (nuc : Nucleus) where
  /-- The nucleon number density at each point of space. -/
  density : Space → ℝ
  /-- The density is non-negative. -/
  density_nonneg : ∀ x, 0 ≤ density x
  /-- The density integrates to the mass number. -/
  integral_density : ∫ x, density x = nuc.massNumber

namespace DensityProfile

variable {nuc : Nucleus} (ρ : DensityProfile nuc)

/-- A density profile is integrable: its integral is the mass number, which is not zero. -/
lemma integrable : Integrable ρ.density := by
  refine Integrable.of_integral_ne_zero ?_
  rw [ρ.integral_density]
  exact_mod_cast nuc.massNumber_pos.ne'

end DensityProfile

end Nucleus

/-! ### The hard sphere -/

/-- The hard-sphere profile of radius `R` normalised to `m`: the constant `3m / (4π R³)` for
`r ≤ R`, and zero beyond. -/
def hardSphereDensity (m R : ℝ) : ℝ → ℝ :=
  (Iic R).indicator fun _ => 3 * m / (4 * π * R ^ 3)

lemma hardSphereDensity_def (m R : ℝ) :
    hardSphereDensity m R = (Iic R).indicator fun _ => 3 * m / (4 * π * R ^ 3) := (rfl)

lemma hardSphereDensity_nonneg {m R : ℝ} (hm : 0 ≤ m) (hR : 0 ≤ R) (r : ℝ) :
    0 ≤ hardSphereDensity m R r := by
  rw [hardSphereDensity_def]
  exact indicator_nonneg (fun _ _ => by positivity) r

/-- The hard-sphere profile of radius `R > 0` integrates to `m` over space. -/
theorem integral_hardSphereDensity (m : ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ x : Space, hardSphereDensity m R ‖x‖ = m := by
  have h : (fun x : Space => hardSphereDensity m R ‖x‖) =
      (closedBall (0 : Space) R).indicator fun _ => 3 * m / (4 * π * R ^ 3) := by
    ext x
    simp [hardSphereDensity_def, indicator]
  have hV : volume.real (closedBall (0 : Space) R) = R ^ 3 * (4 / 3 * π) := by
    simp [measureReal_def, Measure.addHaar_closedBall _ _ hR.le, Space.finrank_eq_dim,
      Space.volume_metricBall_three, ENNReal.toReal_ofReal, pow_nonneg hR.le, pi_pos.le]
  rw [h, integral_indicator_const _ measurableSet_closedBall, hV, smul_eq_mul]
  field_simp

/-! ### The Gaussian profile -/

/-- The Gaussian profile of range `R` normalised to `m`, `m (π R²)^{-3/2} exp(-r²/R²)`. -/
def gaussianDensity (m R r : ℝ) : ℝ :=
  m / (π * R ^ 2) ^ (3 / 2 : ℝ) * exp (-(r / R) ^ 2)

lemma gaussianDensity_def (m R r : ℝ) :
    gaussianDensity m R r = m / (π * R ^ 2) ^ (3 / 2 : ℝ) * exp (-(r / R) ^ 2) := (rfl)

lemma gaussianDensity_nonneg {m : ℝ} (hm : 0 ≤ m) (R r : ℝ) : 0 ≤ gaussianDensity m R r := by
  rw [gaussianDensity_def]
  positivity

/-- The Gaussian profile of range `R ≠ 0` integrates to `m` over space. -/
theorem integral_gaussianDensity (m : ℝ) {R : ℝ} (hR : R ≠ 0) :
    ∫ x : Space, gaussianDensity m R ‖x‖ = m := by
  have hR2 : 0 < (R ^ 2)⁻¹ := by positivity
  have h : (fun x : Space => gaussianDensity m R ‖x‖) =
      fun x => m / (π * R ^ 2) ^ (3 / 2 : ℝ) * exp (-(R ^ 2)⁻¹ * ‖x‖ ^ 2) := by
    ext x
    simp only [gaussianDensity_def, div_pow, neg_mul, inv_mul_eq_div]
  have : 0 < (π * R ^ 2) ^ (3 / 2 : ℝ) := by positivity
  simp only [h, integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm hR2,
    Space.finrank_eq_dim, div_inv_eq_mul]
  norm_num
  field_simp

/-! ### The Woods–Saxon profile -/

/-- The two-parameter Fermi, or Woods–Saxon, profile with central density `ρ₀`, half-density
radius `R` and surface thickness `a`: `ρ₀ / (1 + exp((r - R)/a))`. -/
def woodsSaxonDensity (ρ₀ R a r : ℝ) : ℝ :=
  ρ₀ / (1 + exp ((r - R) / a))

lemma woodsSaxonDensity_def (ρ₀ R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r = ρ₀ / (1 + exp ((r - R) / a)) := (rfl)

lemma woodsSaxonDensity_nonneg {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (R a r : ℝ) :
    0 ≤ woodsSaxonDensity ρ₀ R a r := by
  rw [woodsSaxonDensity_def]
  positivity

lemma woodsSaxonDensity_pos {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (R a r : ℝ) :
    0 < woodsSaxonDensity ρ₀ R a r := by
  rw [woodsSaxonDensity_def]
  positivity

lemma woodsSaxonDensity_eq_mul (ρ₀ R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r = ρ₀ * woodsSaxonDensity 1 R a r := by
  simp [woodsSaxonDensity_def, div_eq_mul_inv]

/-- The Woods–Saxon profile is bounded by the exponential tail `ρ₀ exp(-(r - R)/a)`. -/
lemma woodsSaxonDensity_le {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r ≤ ρ₀ * exp (-((r - R) / a)) := by
  rw [woodsSaxonDensity_def, exp_neg, ← div_eq_mul_inv]
  gcongr
  linarith [exp_pos ((r - R) / a)]

/-- The Woods–Saxon profile is integrable over space whenever the surface thickness is
positive. -/
theorem integrable_woodsSaxonDensity (ρ₀ R : ℝ) {a : ℝ} (ha : 0 < a) :
    Integrable fun x : Space => woodsSaxonDensity ρ₀ R a ‖x‖ := by
  simp_rw [woodsSaxonDensity_eq_mul ρ₀]
  refine Integrable.const_mul ?_ ρ₀
  rw [integrable_fun_norm_addHaar, Space.finrank_eq_dim]
  -- Compare with `exp (R / a) * r² exp(-r / a)`, integrable on `(0, ∞)` as a Gamma integral.
  have hg : IntegrableOn (fun r : ℝ => exp (R / a) * (r ^ 2 * exp (-a⁻¹ * r))) (Ioi 0) := by
    refine Integrable.const_mul ?_ _
    refine (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (by norm_num) one_pos
      (inv_pos.2 ha)).congr_fun (fun r _ => ?_) measurableSet_Ioi
    simp [rpow_ofNat]
  refine hg.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
  · refine (Continuous.aestronglyMeasurable ?_).restrict
    simp_rw [woodsSaxonDensity_def]
    fun_prop (disch := intro r; positivity)
  · have h0 : 0 ≤ woodsSaxonDensity 1 R a r := woodsSaxonDensity_nonneg zero_le_one R a r
    rw [Nat.add_one_sub_one, smul_eq_mul, Real.norm_of_nonneg (by positivity)]
    calc r ^ 2 * woodsSaxonDensity 1 R a r ≤ r ^ 2 * (1 * exp (-((r - R) / a))) := by
          gcongr; exact woodsSaxonDensity_le zero_le_one R a r
      _ = exp (R / a) * (r ^ 2 * exp (-a⁻¹ * r)) := by
          rw [one_mul, mul_left_comm, ← exp_add]
          congr 2
          field_simp
          ring

/-- The integral over space of the Woods–Saxon profile with unit central density. -/
def woodsSaxonIntegral (R a : ℝ) : ℝ :=
  ∫ x : Space, woodsSaxonDensity 1 R a ‖x‖

lemma woodsSaxonIntegral_def (R a : ℝ) :
    woodsSaxonIntegral R a = ∫ x : Space, woodsSaxonDensity 1 R a ‖x‖ := (rfl)

lemma woodsSaxonIntegral_pos (R : ℝ) {a : ℝ} (ha : 0 < a) : 0 < woodsSaxonIntegral R a := by
  rw [woodsSaxonIntegral_def, integral_pos_iff_support_of_nonneg
    (fun x => woodsSaxonDensity_nonneg zero_le_one R a ‖x‖) (integrable_woodsSaxonDensity 1 R ha)]
  have : Function.support (fun x : Space => woodsSaxonDensity 1 R a ‖x‖) = univ :=
    Function.support_eq_univ fun x => (woodsSaxonDensity_pos one_pos R a ‖x‖).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

/-- The integral of the Woods–Saxon profile is linear in its central density. -/
lemma integral_woodsSaxonDensity (ρ₀ R a : ℝ) :
    ∫ x : Space, woodsSaxonDensity ρ₀ R a ‖x‖ = ρ₀ * woodsSaxonIntegral R a := by
  simp_rw [woodsSaxonDensity_eq_mul ρ₀]
  exact integral_const_mul _ _

/-- The central density `ρ₀` that normalises the Woods–Saxon profile with half-density radius `R`
and surface thickness `a` to `m`. -/
def woodsSaxonCentralDensity (m R a : ℝ) : ℝ :=
  m / woodsSaxonIntegral R a

lemma woodsSaxonCentralDensity_def (m R a : ℝ) :
    woodsSaxonCentralDensity m R a = m / woodsSaxonIntegral R a := (rfl)

/-- The Woods–Saxon central density normalising to a positive `m` is positive. -/
lemma woodsSaxonCentralDensity_pos {m : ℝ} (hm : 0 < m) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    0 < woodsSaxonCentralDensity m R a :=
  div_pos hm (woodsSaxonIntegral_pos R ha)

/-- For `0 < a`, the Woods–Saxon profile integrates to `m` exactly when its central density is
`woodsSaxonCentralDensity m R a`. -/
theorem integral_woodsSaxonDensity_eq_iff {ρ₀ m R a : ℝ} (ha : 0 < a) :
    ∫ x : Space, woodsSaxonDensity ρ₀ R a ‖x‖ = m ↔ ρ₀ = woodsSaxonCentralDensity m R a := by
  rw [integral_woodsSaxonDensity, woodsSaxonCentralDensity_def,
    eq_div_iff (woodsSaxonIntegral_pos R ha).ne']

/-- For `0 < a`, exactly one central density normalises the Woods–Saxon profile to `m`. -/
theorem existsUnique_integral_woodsSaxonDensity_eq (m R : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃! ρ₀ : ℝ, ∫ x : Space, woodsSaxonDensity ρ₀ R a ‖x‖ = m :=
  ⟨woodsSaxonCentralDensity m R a, (integral_woodsSaxonDensity_eq_iff ha).2 rfl,
    fun _ h => (integral_woodsSaxonDensity_eq_iff ha).1 h⟩

/-! ### The bundled profiles of a nucleus -/

namespace Nucleus.DensityProfile

variable (nuc : Nucleus)

/-- The hard-sphere density profile of `nuc` with radius `R > 0`. -/
@[expose, simps density]
def hardSphere {R : ℝ} (hR : 0 < R) : DensityProfile nuc where
  density x := hardSphereDensity nuc.massNumber R ‖x‖
  density_nonneg _ := hardSphereDensity_nonneg (Nat.cast_nonneg _) hR.le _
  integral_density := integral_hardSphereDensity _ hR

/-- The Gaussian density profile of `nuc` with range `R ≠ 0`. -/
@[expose, simps density]
def gaussian {R : ℝ} (hR : R ≠ 0) : DensityProfile nuc where
  density x := gaussianDensity nuc.massNumber R ‖x‖
  density_nonneg _ := gaussianDensity_nonneg (Nat.cast_nonneg _) _ _
  integral_density := integral_gaussianDensity _ hR

/-- The Woods–Saxon density profile of `nuc` with half-density radius `R` and surface thickness
`a > 0`, with its central density fixed by the normalisation. -/
@[expose, simps density]
def woodsSaxon (R : ℝ) {a : ℝ} (ha : 0 < a) : DensityProfile nuc where
  density x := woodsSaxonDensity (woodsSaxonCentralDensity nuc.massNumber R a) R a ‖x‖
  density_nonneg x := woodsSaxonDensity_nonneg
    (woodsSaxonCentralDensity_pos (by exact_mod_cast nuc.massNumber_pos) R ha).le _ _ _
  integral_density := (integral_woodsSaxonDensity_eq_iff ha).2 rfl

end Nucleus.DensityProfile

end EpsilonEridani
