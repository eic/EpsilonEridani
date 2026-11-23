/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck, Joseph Myers, Heather Macbeth
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

/-!
# The sine of an oriented angle

Mathlib expresses the cosine of the oriented angle between two vectors of an oriented
two-dimensional real inner product space through the inner product
(`Orientation.inner_eq_norm_mul_norm_mul_cos_oangle`,
`Orientation.cos_oangle_eq_inner_div_norm_mul_norm`). This file supplies the companion statements
for the sine, which is governed by the area form: `ω(x, y) = ‖x‖ ‖y‖ sin ∡(x, y)`. Together the two
identify an oriented angle in coordinates, which is how azimuthal angles about a fixed axis are
defined in scattering kinematics.

The proofs are adapted from those of Mathlib's `Orientation.inner_eq_norm_mul_norm_mul_cos_oangle`
and `Orientation.cos_oangle_eq_inner_div_norm_mul_norm` (Joseph Myers, Heather Macbeth), with the
imaginary part of `Orientation.kahler` in place of its real part.

## Main statements

* `Orientation.areaForm_eq_norm_mul_norm_mul_sin_oangle`: `ω(x, y) = ‖x‖ ‖y‖ sin ∡(x, y)`.
* `Orientation.sin_oangle_eq_areaForm_div_norm_mul_norm`:
  `sin ∡(x, y) = ω(x, y) / (‖x‖ ‖y‖)`, both sides being `0` when `x` or `y` is `0`.
-/

public section

namespace Orientation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- The area form of two vectors is the product of their norms and the sine of the oriented angle
between them. -/
theorem areaForm_eq_norm_mul_norm_mul_sin_oangle (x y : V) :
    o.areaForm x y = ‖x‖ * ‖y‖ * Real.Angle.sin (o.oangle x y) := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [oangle, Real.Angle.sin_coe, Complex.sin_arg, o.norm_kahler]
  simp only [kahler_apply_apply, Complex.real_smul, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re]
  field_simp
  ring

/-- The sine of the oriented angle between two vectors is their area form divided by the product
of their norms. Unlike the cosine, this needs no nonvanishing hypotheses: both sides are `0` when
either vector is `0`. -/
theorem sin_oangle_eq_areaForm_div_norm_mul_norm (x y : V) :
    Real.Angle.sin (o.oangle x y) = o.areaForm x y / (‖x‖ * ‖y‖) := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [o.areaForm_eq_norm_mul_norm_mul_sin_oangle]
  field

end Orientation
