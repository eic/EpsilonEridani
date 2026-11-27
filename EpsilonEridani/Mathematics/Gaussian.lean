/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import TauCeti.Analysis.PDE.HeatKernel.Basic

/-!
# Normalised isotropic Gaussians

The centred isotropic Gaussian density on a finite-dimensional real inner product space `V`,
`gaussianDensity m R x = m (π R²)^{-n/2} exp(-‖x‖²/R²)` with `n = finrank ℝ V`, normalised to
integral `m` against Lebesgue measure when `R ≠ 0` (`integral_gaussianDensity`) and integrable
for every range `R` (`integrable_gaussianDensity`). It is `m` times TauCeti's heat kernel
`TauCeti.heatKernel` at time `R² / 4`, whose normalisation it inherits.

On the Euclidean plane, `gaussianProfile w y = exp (-‖y‖ ^ 2 / (2 * w ^ 2)) / (2 * π * w ^ 2)`
is the unit-mass Gaussian parametrised by its width `w`, normalised to unit integral when
`w ≠ 0` (for `w = 0` the profile is identically zero); it is `gaussianDensity 1 (√2 * w)`
(`gaussianProfile_eq_gaussianDensity`). `integral_exp_neg_mul_sq_norm_plane` computes the
Gaussian integral `∫ exp (-b ‖y‖²) = π / b` on the plane, from which
`integral_gaussianProfile_mul_gaussianProfile` computes the overlap of two profiles.

Gaussians of this shape are the standard model of a smooth localised profile: in parton physics
they model transverse profiles, from the transverse separation of two partons in a hadron to the
transverse-momentum dependence of TMDs, and in nuclear physics the Gaussian nuclear density.
-/

public section

noncomputable section

open MeasureTheory Real

namespace EpsilonEridani
namespace Gaussian

section Density

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The centred isotropic Gaussian of range `R` and mass `m` on `V`,
`m (π R²)^{-n/2} exp(-‖x‖²/R²)` with `n = finrank ℝ V`: `m` times the heat kernel at time
`R² / 4`. For `R ≠ 0` it integrates to `m` (`integral_gaussianDensity`). -/
def gaussianDensity (m R : ℝ) (x : V) : ℝ :=
  m * TauCeti.heatKernel (R ^ 2 / 4) x

theorem gaussianDensity_def (m R : ℝ) (x : V) :
    gaussianDensity m R x = m * TauCeti.heatKernel (R ^ 2 / 4) x :=
  (rfl)

theorem gaussianDensity_nonneg {m : ℝ} (hm : 0 ≤ m) (R : ℝ) (x : V) :
    0 ≤ gaussianDensity m R x := by
  rw [gaussianDensity_def, TauCeti.heatKernel_apply]
  positivity

variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

/-- The Gaussian density of range `R ≠ 0` integrates to its mass `m`. -/
@[simp]
theorem integral_gaussianDensity (m : ℝ) {R : ℝ} (hR : R ≠ 0) :
    ∫ x : V, gaussianDensity m R x = m := by
  simp only [gaussianDensity_def, integral_const_mul,
    TauCeti.integral_heatKernel (by positivity : 0 < R ^ 2 / 4), mul_one]

/-- The Gaussian density is integrable, for every range `R`. -/
theorem integrable_gaussianDensity (m R : ℝ) : Integrable (gaussianDensity (V := V) m R) := by
  rcases eq_or_ne R 0 with rfl | hR
  · rcases eq_or_ne (Module.finrank ℝ V) 0 with hV | hV
    · -- On the zero space every function is integrable: the space is a point of finite volume.
      have : Subsingleton V := Module.finrank_zero_iff.1 hV
      exact Integrable.of_subsingleton
    · -- In positive dimension the heat kernel at time `0` vanishes: `0 ^ (-n / 2) = 0`.
      have hV' : (-(Module.finrank ℝ V : ℝ) / 2) ≠ 0 := by
        simp [hV]
      refine (integrable_zero V ℝ volume).congr (.of_forall fun x => ?_)
      simp [gaussianDensity_def, TauCeti.heatKernel_apply, zero_rpow hV']
  · exact (TauCeti.integrable_heatKernel (by positivity : 0 < R ^ 2 / 4)).const_mul m

end Density

/-- The Gaussian of width `w` on the Euclidean plane,
`G(y) = exp(-‖y‖ ^ 2 / (2 * w ^ 2)) / (2 * π * w ^ 2)`, normalised to unit integral when `w ≠ 0`
(`integral_gaussianProfile_eq_one`). -/
def gaussianProfile (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2))

theorem gaussianProfile_def (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    gaussianProfile w y = (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2)) :=
  (rfl)

/-- The Gaussian profile of width `0` is identically zero, since `(2 * π * 0 ^ 2)⁻¹ = 0`. -/
@[simp]
theorem gaussianProfile_zero : gaussianProfile 0 = 0 := by
  ext y
  simp [gaussianProfile]

theorem gaussianProfile_nonneg (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ gaussianProfile w y := by
  unfold gaussianProfile
  positivity

/-- The Gaussian integral on the plane: `∫ exp (-b ‖y‖²) dy = π / b` for `0 < b`. -/
theorem integral_exp_neg_mul_sq_norm_plane {b : ℝ} (hb : 0 < b) :
    ∫ y : EuclideanSpace ℝ (Fin 2), exp (-b * ‖y‖ ^ 2) = π / b := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
  norm_num [finrank_euclideanSpace_fin]

/-- The Gaussian profile of width `w` is the unit-mass Gaussian density of range `√2 * w`. -/
theorem gaussianProfile_eq_gaussianDensity (w : ℝ) :
    gaussianProfile w = gaussianDensity 1 (√2 * w) := by
  ext y
  rw [gaussianProfile_def, gaussianDensity_def, TauCeti.heatKernel_apply,
    finrank_euclideanSpace_fin, mul_pow, sq_sqrt zero_le_two]
  norm_num [rpow_neg_one]
  ring_nf

/-- The Gaussian profile is normalised. -/
@[simp]
theorem integral_gaussianProfile_eq_one {w : ℝ} (hw : w ≠ 0) :
    ∫ y, gaussianProfile w y = 1 := by
  rw [gaussianProfile_eq_gaussianDensity, integral_gaussianDensity _ (by positivity)]

/-- The Gaussian profile is integrable. -/
theorem integrable_gaussianProfile (w : ℝ) : Integrable (gaussianProfile w) := by
  rw [gaussianProfile_eq_gaussianDensity]
  exact integrable_gaussianDensity _ _

/-- The overlap of two Gaussian profiles of widths `w` and `w'` is the Gaussian density of width
`√(w² + w'²)` at the origin, `∫ G_w G_w' = (2π (w² + w'²))⁻¹`. -/
theorem integral_gaussianProfile_mul_gaussianProfile {w w' : ℝ} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ∫ y, gaussianProfile w y * gaussianProfile w' y = (2 * π * (w ^ 2 + w' ^ 2))⁻¹ := by
  have hb : 0 < (2 * w ^ 2)⁻¹ + (2 * w' ^ 2)⁻¹ := by positivity
  have : (fun y => gaussianProfile w y * gaussianProfile w' y) =
      fun y : EuclideanSpace ℝ (Fin 2) => ((2 * π * w ^ 2)⁻¹ * (2 * π * w' ^ 2)⁻¹) *
        exp (-((2 * w ^ 2)⁻¹ + (2 * w' ^ 2)⁻¹) * ‖y‖ ^ 2) := by
    ext y
    rw [gaussianProfile, gaussianProfile, mul_mul_mul_comm, ← exp_add]
    congr 2
    ring
  rw [this, integral_const_mul, integral_exp_neg_mul_sq_norm_plane hb]
  field_simp
  ring

end Gaussian
end EpsilonEridani
