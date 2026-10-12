/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian profile on the plane

The centred isotropic Gaussian on the Euclidean plane,
`gaussianProfile w y = exp (-‖y‖ ^ 2 / (2 * w ^ 2)) / (2 * π * w ^ 2)`, with the width `w` as its
only parameter, normalised to unit integral against Lebesgue measure when `w ≠ 0` (for `w = 0`
the profile is identically zero). `integral_exp_neg_mul_sq_norm_plane` computes the Gaussian
integral `∫ exp (-b ‖y‖²) = π / b` on the plane; from it `integral_gaussianProfile_eq_one` proves
the normalisation and `integral_gaussianProfile_mul_gaussianProfile` the overlap of two profiles.

Gaussians of this shape are the standard model of a smooth localised profile on the plane; in
parton physics they model transverse profiles, from the transverse separation of two partons in
a hadron to the transverse-momentum dependence of TMDs.
-/

public section

noncomputable section

open MeasureTheory Real

namespace EpsilonEridani
namespace Gaussian

/-- The Gaussian of width `w` on the Euclidean plane,
`G(y) = exp(-‖y‖ ^ 2 / (2 * w ^ 2)) / (2 * π * w ^ 2)`, normalised to unit integral when `w ≠ 0`
(`integral_gaussianProfile_eq_one`). -/
def gaussianProfile (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2))

theorem gaussianProfile_def (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    gaussianProfile w y = (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2)) :=
  (rfl)

theorem gaussianProfile_nonneg (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ gaussianProfile w y := by
  unfold gaussianProfile
  positivity

/-- The Gaussian integral on the plane: `∫ exp (-b ‖y‖²) dy = π / b` for `0 < b`. -/
theorem integral_exp_neg_mul_sq_norm_plane {b : ℝ} (hb : 0 < b) :
    ∫ y : EuclideanSpace ℝ (Fin 2), exp (-b * ‖y‖ ^ 2) = π / b := by
  rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin, Nat.cast_ofNat,
    div_self two_ne_zero, rpow_one]

/-- The Gaussian profile is normalised. -/
@[simp]
theorem integral_gaussianProfile_eq_one {w : ℝ} (hw : w ≠ 0) :
    ∫ y, gaussianProfile w y = 1 := by
  have : (fun y => gaussianProfile w y) = fun y : EuclideanSpace ℝ (Fin 2) =>
      (2 * π * w ^ 2)⁻¹ * exp (-(2 * w ^ 2)⁻¹ * ‖y‖ ^ 2) := by
    ext y
    rw [gaussianProfile]
    congr 2
    ring
  rw [this, integral_const_mul, integral_exp_neg_mul_sq_norm_plane (by positivity)]
  field_simp

/-- A Gaussian profile of nonzero width is integrable. -/
theorem integrable_gaussianProfile {w : ℝ} (hw : w ≠ 0) : Integrable (gaussianProfile w) := by
  refine Integrable.of_integral_ne_zero ?_
  simp [hw]

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
