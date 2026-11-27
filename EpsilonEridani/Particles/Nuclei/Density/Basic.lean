/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Gaussian
public import EpsilonEridani.Mathematics.SpecialFunctions.SigmoidExtensions
public import EpsilonEridani.Particles.Nuclei.Basic
public import Physlib.SpaceAndTime.Space.Module
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Physlib.SpaceAndTime.Space.Integrals.Basic
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Coordinate-space nuclear density profiles

A nuclear density profile is the nucleon number density `ρ_A : ℝ³ → ℝ` of a nucleus: a
non-negative function on physical space whose integral is the mass number,
`∫ ρ_A d³r = A`. It is normalised to `A` rather than to one, because the geometric
quantities built from it (the thickness function, multiple-scattering corrections) count
nucleons, and a probability-normalised profile would shift their mass-number dependence by one
power of `A`.

Physical space is Physlib's `Space`. This file constructs the three spherically symmetric
profiles of nuclear geometry. The hard-sphere and Woods–Saxon profiles are written as functions
`ℝ → ℝ` of the radius and evaluated at the distance `‖x‖` from the origin of `Space`; the
Gaussian profile is the isotropic Gaussian density `Gaussian.isotropicDensity` on `Space`, whose
normalisation and integrability are proved in `EpsilonEridani.Mathematics.Gaussian`. This file
proves the other two integrable (the Woods–Saxon profile for positive surface diffuseness
`0 < a`) and normalisable under the stated parameter conditions (`0 < R` for the hard sphere,
`0 < a` for the Woods–Saxon profile):

* the hard sphere `3A / (4π R³) · 1_{r ≤ R}`;
* the Gaussian `A (π R²)^{-3/2} exp(-r²/R²)`, normalisable for `R ≠ 0`;
* the two-parameter Fermi, or Woods–Saxon, profile `ρ₀ / (1 + exp((r - R)/a))`, with
  half-density radius `R` (where the profile equals `ρ₀ / 2`) and surface diffuseness `a`. The
  parameter `ρ₀`, conventionally called the central density, is, for `0 < a`, the plateau value
  the profile approaches deep inside the nucleus, `r - R ≪ -a`; it equals the density at the
  origin only in the sharp-surface limit `a / R → 0`. It is fixed by the normalisation. The
  relevant integral has no elementary closed form, so `ρ₀` is defined as `A` divided by the
  integral of the profile with `ρ₀ = 1`, and shown to be the unique normalising value and
  positive.

All declarations live in the namespace `EpsilonEridani.Particles.Nuclei`.

## Main definitions

* `Nucleus.DensityProfile nuc`: a non-negative function on `Space` with integral the mass
  number of `nuc`.
* `hardSphereDensity`, `woodsSaxonDensity`: the hard-sphere and Woods–Saxon radial profiles.
* `woodsSaxonUnitDensityIntegral R a`: the integral over space of the Woods–Saxon profile with
  `ρ₀ = 1`.
* `woodsSaxonCentralDensity m R a`: the parameter `ρ₀` normalising the Woods–Saxon profile
  to `m`.
* `Nucleus.DensityProfile.hardSphere`, `gaussian`, `woodsSaxon`: the bundled profiles of a
  nucleus.

## Main statements

* `integrable_hardSphereDensity_norm` and `integrable_woodsSaxonDensity_norm`: the two radial
  profiles are integrable over `ℝ³` (the latter for every positive surface diffuseness).
* `integral_hardSphereDensity_norm`: the hard-sphere profile of radius `0 < R` integrates to its
  normalisation parameter.
* `integral_woodsSaxonDensity_norm_woodsSaxonCentralDensity`: for `0 < a`, the Woods–Saxon
  profile with `ρ₀ = woodsSaxonCentralDensity m R a` integrates to `m`.
* `existsUnique_integral_woodsSaxonDensity_norm_eq`: for `0 < a`, exactly one value of `ρ₀`
  normalises the Woods–Saxon profile to a given value, and `woodsSaxonCentralDensity_pos` shows
  it is positive when the value is.

## References

* EIC Yellow Report, `arXiv:2103.05419`, Vol. II, §7.3.3.
* H. de Vries, C. W. de Jager and C. de Vries, *Nuclear charge-density-distribution parameters
  from elastic electron scattering*, At. Data Nucl. Data Tables 36 (1987) 495.
* R. D. Woods and D. S. Saxon, *Diffuse surface optical model for nucleon-nuclei scattering*,
  Phys. Rev. **95** (1954) 577.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Nuclei

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

/-- The density of a density profile is integrable over space. -/
@[fun_prop]
lemma integrable : Integrable ρ.density := by
  -- The Bochner integral of a non-integrable function is `0`, so a nonzero integral forces
  -- integrability.
  refine Integrable.of_integral_ne_zero ?_
  rw [ρ.integral_density]
  exact nuc.cast_massNumber_pos.ne'

-- The normalisation law is a simp normal form: `simp` reduces the integral of a profile's
-- density to the mass number.
attribute [simp] integral_density

end DensityProfile

end Nucleus

/-! ### The hard sphere -/

/-- The hard-sphere profile of radius `R`: the constant `3m / (4π R³)` for `r ≤ R`, and zero
beyond. For `0 < R` it is normalised to `m`. -/
def hardSphereDensity (m R : ℝ) : ℝ → ℝ :=
  (Iic R).indicator fun _ => 3 * m / (4 * π * R ^ 3)

lemma hardSphereDensity_def (m R : ℝ) :
    hardSphereDensity m R = (Iic R).indicator fun _ => 3 * m / (4 * π * R ^ 3) := (rfl)

/-- The hard-sphere profile takes its constant interior value `3m / (4π R³)` up to the
radius `R`. -/
@[simp]
lemma hardSphereDensity_of_le {m R r : ℝ} (h : r ≤ R) :
    hardSphereDensity m R r = 3 * m / (4 * π * R ^ 3) := by
  rw [hardSphereDensity_def]
  exact indicator_of_mem (mem_Iic.2 h) _

/-- The hard-sphere profile vanishes beyond the radius `R`. -/
@[simp]
lemma hardSphereDensity_of_gt {m R r : ℝ} (h : R < r) :
    hardSphereDensity m R r = 0 := by
  rw [hardSphereDensity_def]
  exact indicator_of_notMem (fun hr => not_lt.2 (mem_Iic.1 hr) h) _

lemma hardSphereDensity_nonneg {m R : ℝ} (hm : 0 ≤ m) (hR : 0 ≤ R) (r : ℝ) :
    0 ≤ hardSphereDensity m R r := by
  rw [hardSphereDensity_def]
  exact indicator_nonneg (fun _ _ => by positivity) r

/-- The hard-sphere profile is measurable in the radius. -/
@[fun_prop]
lemma measurable_hardSphereDensity (m R : ℝ) : Measurable (hardSphereDensity m R) :=
  measurable_const.indicator measurableSet_Iic

/-- On space, the hard-sphere profile is the constant `3m / (4π R³)` times the indicator of the
closed ball of radius `R`. -/
lemma hardSphereDensity_norm_eq_indicator (m R : ℝ) :
    (fun x : Space => hardSphereDensity m R ‖x‖) =
      (closedBall (0 : Space) R).indicator fun _ => 3 * m / (4 * π * R ^ 3) := by
  ext x
  by_cases hx : ‖x‖ ≤ R
  · simp [hx, hardSphereDensity_of_le]
  · simp [hx, hardSphereDensity_of_gt (not_le.1 hx)]

/-- The hard-sphere profile is integrable over space. -/
@[fun_prop]
theorem integrable_hardSphereDensity_norm (m R : ℝ) :
    Integrable fun x : Space => hardSphereDensity m R ‖x‖ := by
  rw [hardSphereDensity_norm_eq_indicator]
  exact (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator
    measurableSet_closedBall

/-- The hard-sphere profile of radius `R > 0` integrates to `m` over space. -/
@[simp]
theorem integral_hardSphereDensity_norm (m : ℝ) {R : ℝ} (hR : 0 < R) :
    ∫ x : Space, hardSphereDensity m R ‖x‖ = m := by
  have hV : volume.real (closedBall (0 : Space) R) = R ^ 3 * (4 / 3 * π) := by
    simp [Measure.addHaar_real_closedBall _ _ hR.le, Space.finrank_eq_dim]
  rw [hardSphereDensity_norm_eq_indicator, integral_indicator_const _ measurableSet_closedBall, hV,
    smul_eq_mul]
  field_simp

/-! ### The Woods–Saxon profile -/

/-- The two-parameter Fermi, or Woods–Saxon, profile `ρ₀ / (1 + exp((r - R)/a))`, written as
`ρ₀` times the logistic function `Real.sigmoid`. Here `R` is the half-density radius, where the
profile equals `ρ₀ / 2`, and `a` the surface diffuseness (the 90%–10% surface thickness is
`4 a log 3`). The parameter `ρ₀`, conventionally called the central density, is, for `0 < a`, the
plateau value the profile approaches for `r - R ≪ -a`; it equals the density at the origin only
in the sharp-surface limit `a / R → 0`. -/
def woodsSaxonDensity (ρ₀ R a r : ℝ) : ℝ :=
  ρ₀ * Real.sigmoid ((R - r) / a)

lemma woodsSaxonDensity_def (ρ₀ R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r = ρ₀ * Real.sigmoid ((R - r) / a) := (rfl)

/-- The Woods–Saxon profile in its quotient form, `ρ₀ / (1 + exp((r - R)/a))`. -/
lemma woodsSaxonDensity_eq_div (ρ₀ R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r = ρ₀ / (1 + exp ((r - R) / a)) := by
  rw [woodsSaxonDensity_def, Real.sigmoid_def, ← neg_div, neg_sub]
  ring

/-- At the half-density radius `r = R`, the Woods–Saxon profile equals half its parameter `ρ₀`,
`ρ₀ / 2`. -/
@[simp]
lemma woodsSaxonDensity_self (ρ₀ R a : ℝ) :
    woodsSaxonDensity ρ₀ R a R = ρ₀ / 2 := by
  rw [woodsSaxonDensity_def, sub_self, zero_div, Real.sigmoid_zero]
  ring

lemma woodsSaxonDensity_nonneg {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (R a r : ℝ) :
    0 ≤ woodsSaxonDensity ρ₀ R a r := by
  rw [woodsSaxonDensity_def]
  exact mul_nonneg hρ₀ (Real.sigmoid_nonneg _)

/-- The Woods–Saxon profile never exceeds its parameter `ρ₀`, the plateau value it approaches
deep inside the nucleus. -/
lemma woodsSaxonDensity_le_centralDensity {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r ≤ ρ₀ := by
  rw [woodsSaxonDensity_def]
  exact mul_le_of_le_one_right hρ₀ (Real.sigmoid_le_one _)

lemma woodsSaxonDensity_pos {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (R a r : ℝ) :
    0 < woodsSaxonDensity ρ₀ R a r := by
  rw [woodsSaxonDensity_def]
  exact mul_pos hρ₀ (Real.sigmoid_pos _)

/-- The Woods–Saxon profile is continuous in the radius, for every surface diffuseness. -/
@[fun_prop]
lemma continuous_woodsSaxonDensity (ρ₀ R a : ℝ) : Continuous (woodsSaxonDensity ρ₀ R a) := by
  rw [funext (woodsSaxonDensity_def ρ₀ R a)]
  fun_prop

/-- The Woods–Saxon profile is linear in its parameter `ρ₀`. -/
lemma woodsSaxonDensity_eq_mul (ρ₀ R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r = ρ₀ * woodsSaxonDensity 1 R a r := by
  simp [woodsSaxonDensity_def]

/-- The Woods–Saxon profile is bounded by the exponential tail `ρ₀ exp(-(r - R)/a)`. -/
lemma woodsSaxonDensity_le_mul_exp {ρ₀ : ℝ} (hρ₀ : 0 ≤ ρ₀) (R a r : ℝ) :
    woodsSaxonDensity ρ₀ R a r ≤ ρ₀ * exp (-((r - R) / a)) := by
  rw [woodsSaxonDensity_def, ← neg_div, neg_sub]
  gcongr
  exact Real.sigmoid_le_exp _

/-- The Woods–Saxon profile is integrable over space whenever the surface diffuseness is
positive. -/
@[fun_prop]
theorem integrable_woodsSaxonDensity_norm (ρ₀ R : ℝ) {a : ℝ} (ha : 0 < a) :
    Integrable fun x : Space => woodsSaxonDensity ρ₀ R a ‖x‖ := by
  simp_rw [woodsSaxonDensity_eq_mul ρ₀]
  refine Integrable.const_mul ?_ ρ₀
  -- Dominate by `exp (R / a) * exp (-(a⁻¹ * ‖x‖))`, a multiple of the radial exponential.
  have hdom : Integrable fun x : Space => exp (R / a) * exp (-(a⁻¹ * ‖x‖)) :=
    (TauCeti.integrable_exp_neg_mul_norm volume (inv_pos.2 ha)).const_mul _
  refine hdom.mono' (by fun_prop) (.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (woodsSaxonDensity_nonneg zero_le_one R a _)]
  calc woodsSaxonDensity 1 R a ‖x‖ ≤ 1 * exp (-((‖x‖ - R) / a)) :=
        woodsSaxonDensity_le_mul_exp zero_le_one R a ‖x‖
    _ = exp (R / a) * exp (-(a⁻¹ * ‖x‖)) := by
        have hexp : -((‖x‖ - R) / a) = R / a + -(a⁻¹ * ‖x‖) := by
          field_simp
          ring
        rw [one_mul, hexp, exp_add]

/-- The integral over space of the Woods–Saxon profile with `ρ₀ = 1`. -/
def woodsSaxonUnitDensityIntegral (R a : ℝ) : ℝ :=
  ∫ x : Space, woodsSaxonDensity 1 R a ‖x‖

lemma woodsSaxonUnitDensityIntegral_def (R a : ℝ) :
    woodsSaxonUnitDensityIntegral R a = ∫ x : Space, woodsSaxonDensity 1 R a ‖x‖ := (rfl)

/-- For `0 < a`, the Woods–Saxon profile with `ρ₀ = 1` has strictly positive integral over
space, so dividing by it to normalise the profile is legitimate. -/
lemma woodsSaxonUnitDensityIntegral_pos (R : ℝ) {a : ℝ} (ha : 0 < a) :
    0 < woodsSaxonUnitDensityIntegral R a := by
  rw [woodsSaxonUnitDensityIntegral_def, integral_pos_iff_support_of_nonneg
    (fun x => woodsSaxonDensity_nonneg zero_le_one R a ‖x‖)
    (integrable_woodsSaxonDensity_norm 1 R ha)]
  have : Function.support (fun x : Space => woodsSaxonDensity 1 R a ‖x‖) = univ :=
    Function.support_eq_univ fun x => (woodsSaxonDensity_pos one_pos R a ‖x‖).ne'
  rw [this]
  exact Measure.measure_univ_pos.2 (NeZero.ne _)

/-- The integral of the Woods–Saxon profile is linear in its parameter `ρ₀`. -/
lemma integral_woodsSaxonDensity_norm_eq_mul (ρ₀ R a : ℝ) :
    ∫ x : Space, woodsSaxonDensity ρ₀ R a ‖x‖ = ρ₀ * woodsSaxonUnitDensityIntegral R a := by
  simp_rw [woodsSaxonDensity_eq_mul ρ₀]
  exact integral_const_mul _ _

/-- For `0 < a`, the value of the parameter `ρ₀` (the central density) that normalises the
Woods–Saxon profile with half-density radius `R` and surface diffuseness `a` to `m` (see
`integral_woodsSaxonDensity_norm_eq_iff`); the value is junk otherwise. -/
def woodsSaxonCentralDensity (m R a : ℝ) : ℝ :=
  m / woodsSaxonUnitDensityIntegral R a

lemma woodsSaxonCentralDensity_def (m R a : ℝ) :
    woodsSaxonCentralDensity m R a = m / woodsSaxonUnitDensityIntegral R a := (rfl)

/-- The Woods–Saxon central density normalising to a positive `m` is positive. -/
lemma woodsSaxonCentralDensity_pos {m : ℝ} (hm : 0 < m) (R : ℝ) {a : ℝ} (ha : 0 < a) :
    0 < woodsSaxonCentralDensity m R a :=
  div_pos hm (woodsSaxonUnitDensityIntegral_pos R ha)

/-- For `0 < a`, the Woods–Saxon profile integrates to `m` exactly when its parameter `ρ₀` is
`woodsSaxonCentralDensity m R a`. -/
theorem integral_woodsSaxonDensity_norm_eq_iff {ρ₀ m R a : ℝ} (ha : 0 < a) :
    ∫ x : Space, woodsSaxonDensity ρ₀ R a ‖x‖ = m ↔ ρ₀ = woodsSaxonCentralDensity m R a := by
  rw [integral_woodsSaxonDensity_norm_eq_mul, woodsSaxonCentralDensity_def,
    eq_div_iff (woodsSaxonUnitDensityIntegral_pos R ha).ne']

/-- For `0 < a`, the Woods–Saxon profile with `ρ₀ = woodsSaxonCentralDensity m R a` integrates
to `m`: `woodsSaxonCentralDensity` normalises the profile. -/
@[simp]
theorem integral_woodsSaxonDensity_norm_woodsSaxonCentralDensity (m R : ℝ) {a : ℝ} (ha : 0 < a) :
    ∫ x : Space, woodsSaxonDensity (woodsSaxonCentralDensity m R a) R a ‖x‖ = m :=
  (integral_woodsSaxonDensity_norm_eq_iff ha).2 rfl

/-- For `0 < a`, exactly one value of `ρ₀` normalises the Woods–Saxon profile to `m`. -/
theorem existsUnique_integral_woodsSaxonDensity_norm_eq (m R : ℝ) {a : ℝ} (ha : 0 < a) :
    ∃! ρ₀ : ℝ, ∫ x : Space, woodsSaxonDensity ρ₀ R a ‖x‖ = m :=
  ⟨woodsSaxonCentralDensity m R a, integral_woodsSaxonDensity_norm_woodsSaxonCentralDensity m R ha,
    fun _ h => (integral_woodsSaxonDensity_norm_eq_iff ha).1 h⟩

/-! ### The bundled profiles of a nucleus -/

namespace Nucleus.DensityProfile

variable (nuc : Nucleus)

/-- The hard-sphere density profile of `nuc` with radius `R > 0`. -/
def hardSphere (R : ℝ) (hR : 0 < R) : DensityProfile nuc where
  density x := hardSphereDensity nuc.massNumber R ‖x‖
  density_nonneg _ := hardSphereDensity_nonneg (Nat.cast_nonneg _) hR.le _
  integral_density := integral_hardSphereDensity_norm _ hR

/-- The Gaussian density profile of `nuc` with range `R ≠ 0`. -/
def gaussian (R : ℝ) (hR : R ≠ 0) : DensityProfile nuc where
  density := Gaussian.isotropicDensity nuc.massNumber R
  density_nonneg := Gaussian.isotropicDensity_nonneg (Nat.cast_nonneg _) _
  integral_density := Gaussian.integral_isotropicDensity _ hR

/-- The Woods–Saxon density profile of `nuc` with half-density radius `R` and surface diffuseness
`a > 0`, with its parameter `ρ₀` fixed by the normalisation. -/
def woodsSaxon (R a : ℝ) (ha : 0 < a) : DensityProfile nuc where
  density x := woodsSaxonDensity (woodsSaxonCentralDensity nuc.massNumber R a) R a ‖x‖
  density_nonneg _ := woodsSaxonDensity_nonneg
    (woodsSaxonCentralDensity_pos nuc.cast_massNumber_pos R ha).le _ _ _
  integral_density := integral_woodsSaxonDensity_norm_woodsSaxonCentralDensity _ R ha

-- The pointwise projections are deliberately not simp lemmas: as post-order rewrites they
-- would fire under the integral binder before the unconditional normalisation law
-- `integral_density` can match at the root.
lemma hardSphere_density_apply (R : ℝ) (hR : 0 < R) (x : Space) :
    (hardSphere nuc R hR).density x = hardSphereDensity nuc.massNumber R ‖x‖ := (rfl)

lemma gaussian_density_apply (R : ℝ) (hR : R ≠ 0) (x : Space) :
    (gaussian nuc R hR).density x = Gaussian.isotropicDensity nuc.massNumber R x := (rfl)

lemma woodsSaxon_density_apply (R a : ℝ) (ha : 0 < a) (x : Space) :
    (woodsSaxon nuc R a ha).density x =
      woodsSaxonDensity (woodsSaxonCentralDensity nuc.massNumber R a) R a ‖x‖ := (rfl)

end Nucleus.DensityProfile

end Nuclei
end Particles
end EpsilonEridani
