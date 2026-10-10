/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The Gaussian profile on the plane

The centred isotropic Gaussian on the Euclidean plane, normalised to unit integral against
Lebesgue measure: `gaussianProfile w y = exp (-‖y‖ ^ 2 / (2 * w ^ 2)) / (2 * π * w ^ 2)`, with
the width `w` as its only parameter. `integral_gaussianProfile_eq_one` proves the normalisation.

Gaussians of this shape are the standard model of a smooth localised profile on the plane; in
parton physics they model transverse profiles, from the transverse separation of two partons in
a hadron to the transverse-momentum dependence of TMDs.
-/

public section

noncomputable section

open MeasureTheory Real

namespace EpsilonEridani
namespace Gaussian

/-- The normalised Gaussian of width `w` on the Euclidean plane,
`G(y) = exp(-‖y‖ ^ 2 / (2 * w ^ 2)) / (2 * π * w ^ 2)`. -/
def gaussianProfile (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2))

theorem gaussianProfile_def (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    gaussianProfile w y = (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2)) :=
  (rfl)

theorem gaussianProfile_nonneg (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ gaussianProfile w y := by
  unfold gaussianProfile
  positivity

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
  rw [this, integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    finrank_euclideanSpace_fin]
  norm_num
  field_simp

end Gaussian
end EpsilonEridani
