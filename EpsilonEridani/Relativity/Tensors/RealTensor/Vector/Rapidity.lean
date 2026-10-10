/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions

/-!
# The rapidity of a four-vector along an axis

The rapidity of a four-vector `v` along a spatial direction `n` is `y = artanh (v_∥ / v⁰)`, where
`v_∥ = ⟪v⃗, n⟫` is the component of the spatial part along `n` (`Lorentz.Vector.rapidity`).
Inside the forward light cone along `n`, that is for `|v_∥| < v⁰`, the rapidity is the logarithm
of the ratio of the two light-cone components along `n`:
`e^{2y} = (v⁰ + v_∥) / (v⁰ - v_∥)` (`Lorentz.Vector.exp_two_mul_rapidity`).

For a four-vector whose spatial part lies along a unit vector `n`, those two light-cone components
multiply to the Minkowski square `W² = ⟪v, v⟫ₘ`
(`Lorentz.Vector.minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul`). Together the two
statements say that such a four-vector is fixed by its invariant mass and its rapidity:
`v⁰ ± v_∥ = W e^{±y}`, equivalently `v⁰ = W cosh y` and `v_∥ = W sinh y`.

These are the variables in which collider kinematics along a beam axis is reported, and the form
in which an invariant mass and a rapidity are traded for energies.
-/

public section

noncomputable section

namespace Lorentz
namespace Vector

open Real
open scoped InnerProductSpace Lorentz.Vector

variable {d : ℕ}

/-- The rapidity `artanh (v_∥ / v⁰)` of the four-vector `v` along the spatial direction `n`, with
`v_∥ = ⟪v⃗, n⟫` the component of the spatial part along `n`. -/
def rapidity (v : Vector d) (n : EuclideanSpace ℝ (Fin d)) : ℝ :=
  artanh (⟪v.spatialPart, n⟫_ℝ / v.timeComponent)

/-- Defining expression for `Lorentz.Vector.rapidity`. -/
theorem rapidity_def (v : Vector d) (n : EuclideanSpace ℝ (Fin d)) :
    v.rapidity n = artanh (⟪v.spatialPart, n⟫_ℝ / v.timeComponent) :=
  (rfl)

/-- Inside the forward light cone along `n`, the ratio `v_∥ / v⁰` lies in `(-1, 1)`. -/
private theorem div_timeComponent_mem_Ioo {v : Vector d} {a : ℝ} (h : |a| < v.timeComponent) :
    a / v.timeComponent ∈ Set.Ioo (-1) 1 := by
  have ht : 0 < v.timeComponent := (abs_nonneg a).trans_lt h
  rw [Set.mem_Ioo, lt_div_iff₀ ht, div_lt_iff₀ ht]
  constructor <;> linarith [neg_abs_le a, le_abs_self a]

/-- **The rapidity is the logarithm of the ratio of the light-cone components.** Inside the
forward light cone along `n`, `e^{2y} = (v⁰ + v_∥) / (v⁰ - v_∥)`. -/
theorem exp_two_mul_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    exp (2 * v.rapidity n) = (v.timeComponent + ⟪v.spatialPart, n⟫_ℝ) /
      (v.timeComponent - ⟪v.spatialPart, n⟫_ℝ) := by
  have ht : 0 < v.timeComponent := (abs_nonneg _).trans_lt h
  have hx := div_timeComponent_mem_Ioo h
  have hpos : 0 ≤ (1 + ⟪v.spatialPart, n⟫_ℝ / v.timeComponent) /
      (1 - ⟪v.spatialPart, n⟫_ℝ / v.timeComponent) :=
    div_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  rw [two_mul, exp_add, rapidity_def, exp_artanh hx, Real.mul_self_sqrt hpos]
  field_simp

/-- The Minkowski square of a four-vector whose spatial part is `a • n`, for a unit vector `n`, is
the product `(v⁰ + a) (v⁰ - a)` of its light-cone components along `n`. -/
theorem minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n) :
    ⟪v, v⟫ₘ = (v.timeComponent + a) * (v.timeComponent - a) := by
  rw [minkowskiProduct_self_eq_sq_sub, hv]
  simp only [norm_smul, hn, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- **A collinear four-vector from its invariant mass and rapidity, forward component.** If the
spatial part of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then
`v⁰ + a = W e^{y}`, with `W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem timeComponent_add_eq_sqrt_mul_exp_rapidity {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n)
    (h : |a| < v.timeComponent) :
    v.timeComponent + a = √⟪v, v⟫ₘ * exp (v.rapidity n) := by
  have hpar : ⟪v.spatialPart, n⟫_ℝ = a := by
    rw [hv, real_inner_smul_left, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  have hA : 0 < v.timeComponent + a := by linarith [neg_abs_le a]
  have hB : 0 < v.timeComponent - a := by linarith [le_abs_self a]
  have hx := div_timeComponent_mem_Ioo h
  have hratio : (1 + a / v.timeComponent) / (1 - a / v.timeComponent) =
      (v.timeComponent + a) / (v.timeComponent - a) := by
    have ht : v.timeComponent ≠ 0 := ((abs_nonneg a).trans_lt h).ne'
    field_simp
  have hW : √⟪v, v⟫ₘ = √(v.timeComponent + a) * √(v.timeComponent - a) := by
    rw [minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul hn hv, Real.sqrt_mul hA.le]
  have hy : exp (v.rapidity n) = √(v.timeComponent + a) / √(v.timeComponent - a) := by
    rw [rapidity_def, hpar, exp_artanh hx, hratio, Real.sqrt_div hA.le]
  have hB' : 0 < √(v.timeComponent - a) := Real.sqrt_pos.2 hB
  rw [hW, hy]
  field_simp
  rw [Real.sq_sqrt hA.le]

/-- **A collinear four-vector from its invariant mass and rapidity, backward component.** If the
spatial part of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then
`v⁰ - a = W e^{-y}`, with `W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem timeComponent_sub_eq_sqrt_mul_exp_neg_rapidity {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n)
    (h : |a| < v.timeComponent) :
    v.timeComponent - a = √⟪v, v⟫ₘ * exp (-v.rapidity n) := by
  have hA : 0 < v.timeComponent + a := by linarith [neg_abs_le a]
  have hB : 0 < v.timeComponent - a := by linarith [le_abs_self a]
  have hW : (√⟪v, v⟫ₘ) ^ 2 = (v.timeComponent + a) * (v.timeComponent - a) := by
    rw [minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul hn hv]
    exact Real.sq_sqrt (mul_pos hA hB).le
  have hplus := timeComponent_add_eq_sqrt_mul_exp_rapidity hn hv h
  have hexp : exp (v.rapidity n) * exp (-v.rapidity n) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  apply mul_left_cancel₀ hA.ne'
  linear_combination -hW - √⟪v, v⟫ₘ * exp (-v.rapidity n) * hplus - (√⟪v, v⟫ₘ) ^ 2 * hexp

/-- The energy of a collinear four-vector is `W cosh y`. -/
theorem timeComponent_eq_sqrt_mul_cosh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    v.timeComponent = √⟪v, v⟫ₘ * cosh (v.rapidity n) := by
  rw [cosh_eq]
  linear_combination (timeComponent_add_eq_sqrt_mul_exp_rapidity hn hv h +
    timeComponent_sub_eq_sqrt_mul_exp_neg_rapidity hn hv h) / 2

/-- The momentum along the axis of a collinear four-vector is `W sinh y`. -/
theorem eq_sqrt_mul_sinh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    a = √⟪v, v⟫ₘ * sinh (v.rapidity n) := by
  rw [sinh_eq]
  linear_combination (timeComponent_add_eq_sqrt_mul_exp_rapidity hn hv h -
    timeComponent_sub_eq_sqrt_mul_exp_neg_rapidity hn hv h) / 2

end Vector
end Lorentz
