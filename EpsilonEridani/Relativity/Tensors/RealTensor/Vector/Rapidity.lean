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
`v_∥ = ⟪v.spatialPart, n⟫` is the component of the spatial part along `n`
(`Lorentz.Vector.rapidity`). This is the physical rapidity along `n` only for a unit vector,
`‖n‖ = 1`: the definition is not invariant under rescaling `n`
(`Lorentz.Vector.rapidity_smul_right_eq_artanh`).
Inside the forward light cone along `n`, that is for `|v_∥| < v⁰`, it recovers the velocity,
`tanh y = v_∥ / v⁰` (`Lorentz.Vector.tanh_rapidity`), and it is half the logarithm of the ratio of
the two light-cone components along `n`: `e^{y} = √(v⁰ + v_∥) / √(v⁰ - v_∥)`
(`Lorentz.Vector.exp_rapidity`), so `e^{2y} = (v⁰ + v_∥) / (v⁰ - v_∥)`
(`Lorentz.Vector.exp_two_mul_rapidity`).

The two light-cone components multiply to the square `m_T² = (v⁰)² - v_∥²` of the transverse mass
along `n`, so inside that cone the energy and the component along `n` of a four-vector are fixed
by its transverse mass and its rapidity: `v⁰ ± v_∥ = m_T e^{±y}`
(`Lorentz.Vector.timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity`,
`Lorentz.Vector.timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity`), equivalently
`v⁰ = m_T cosh y` and `v_∥ = m_T sinh y`.

For a four-vector whose spatial part lies along a unit vector `n`, the transverse mass is the
invariant mass `W = √⟪v, v⟫ₘ`
(`Lorentz.Vector.minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul`, in
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions`), and the same
relations read `v⁰ ± v_∥ = W e^{±y}`, `v⁰ = W cosh y` and `v_∥ = W sinh y`
(the `_of_spatialPart_eq_smul` forms).

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
`v_∥ = ⟪v.spatialPart, n⟫` the component of the spatial part along `n`. It is the rapidity along
`n` only when `‖n‖ = 1`; rescaling `n` rescales `v_∥`
(`Lorentz.Vector.rapidity_smul_right_eq_artanh`). -/
def rapidity (v : Vector d) (n : EuclideanSpace ℝ (Fin d)) : ℝ :=
  artanh (⟪v.spatialPart, n⟫_ℝ / v.timeComponent)

/-- Defining expression for `Lorentz.Vector.rapidity`. -/
theorem rapidity_def (v : Vector d) (n : EuclideanSpace ℝ (Fin d)) :
    v.rapidity n = artanh (⟪v.spatialPart, n⟫_ℝ / v.timeComponent) :=
  (rfl)

/-- Rescaling the direction rescales the component along it: the rapidity along `c • n` is
`artanh (c v_∥ / v⁰)`, so `rapidity` is the rapidity along `n` only for a unit vector `n`. -/
theorem rapidity_smul_right_eq_artanh (v : Vector d) (c : ℝ) (n : EuclideanSpace ℝ (Fin d)) :
    v.rapidity (c • n) = artanh (c * ⟪v.spatialPart, n⟫_ℝ / v.timeComponent) := by
  rw [rapidity_def, real_inner_smul_right]

/-- Inside the forward light cone along `n`, that is for `|v_∥| < v⁰`, the ratio `v_∥ / v⁰` lies
in `(-1, 1)`, where `artanh` inverts `tanh`. -/
theorem inner_spatialPart_div_timeComponent_mem_Ioo {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    ⟪v.spatialPart, n⟫_ℝ / v.timeComponent ∈ Set.Ioo (-1) 1 := by
  have ht : 0 < v.timeComponent := (abs_nonneg _).trans_lt h
  rw [Set.mem_Ioo, lt_div_iff₀ ht, div_lt_iff₀ ht]
  constructor <;> linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ, le_abs_self ⟪v.spatialPart, n⟫_ℝ]

/-- Inside the forward light cone along `n`, the rapidity `y` recovers the velocity along `n`:
`tanh y = v_∥ / v⁰`. -/
theorem tanh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    tanh (v.rapidity n) = ⟪v.spatialPart, n⟫_ℝ / v.timeComponent := by
  rw [rapidity_def]
  exact tanh_artanh (inner_spatialPart_div_timeComponent_mem_Ioo h)

/-- Inside the forward light cone along `n`, `e^{y} = √(v⁰ + v_∥) / √(v⁰ - v_∥)`. -/
theorem exp_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    exp (v.rapidity n) = √(v.timeComponent + ⟪v.spatialPart, n⟫_ℝ) /
      √(v.timeComponent - ⟪v.spatialPart, n⟫_ℝ) := by
  have ht : v.timeComponent ≠ 0 := ((abs_nonneg _).trans_lt h).ne'
  have hA : 0 ≤ v.timeComponent + ⟪v.spatialPart, n⟫_ℝ := by
    linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ]
  rw [rapidity_def, exp_artanh (inner_spatialPart_div_timeComponent_mem_Ioo h),
    ← Real.sqrt_div hA]
  congr 1
  field_simp

/-- **The rapidity is half the logarithm of the ratio of the light-cone components.** Inside
the forward light cone along `n`, `e^{2y} = (v⁰ + v_∥) / (v⁰ - v_∥)`. -/
theorem exp_two_mul_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    exp (2 * v.rapidity n) = (v.timeComponent + ⟪v.spatialPart, n⟫_ℝ) /
      (v.timeComponent - ⟪v.spatialPart, n⟫_ℝ) := by
  rw [two_mul, exp_add, exp_rapidity h, div_mul_div_comm,
    Real.mul_self_sqrt (by linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ]),
    Real.mul_self_sqrt (by linarith [le_abs_self ⟪v.spatialPart, n⟫_ℝ])]

/-- `x = √(x y) (√x / √y)` for `x ≥ 0` and `y > 0`: the algebra shared by the forward and the
backward light-cone component below. -/
private theorem eq_sqrt_mul_mul_sqrt_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    x = √(x * y) * (√x / √y) := by
  rw [Real.sqrt_mul hx, mul_div_left_comm, mul_div_cancel_right₀ _ (Real.sqrt_pos.2 hy).ne',
    Real.mul_self_sqrt hx]

/-- **A four-vector from its transverse mass and rapidity, forward component.** Inside the
forward light cone along `n`, `v⁰ + v_∥ = m_T e^{y}`, with `m_T = √((v⁰)² - v_∥²)` and `y` the
rapidity along `n`. -/
theorem timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    v.timeComponent + ⟪v.spatialPart, n⟫_ℝ =
      √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * exp (v.rapidity n) := by
  rw [exp_rapidity h, sq_sub_sq]
  exact eq_sqrt_mul_mul_sqrt_div (by linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ])
    (by linarith [le_abs_self ⟪v.spatialPart, n⟫_ℝ])

/-- **A four-vector from its transverse mass and rapidity, backward component.** Inside the
forward light cone along `n`, `v⁰ - v_∥ = m_T e^{-y}`, with `m_T = √((v⁰)² - v_∥²)` and `y` the
rapidity along `n`. -/
theorem timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    v.timeComponent - ⟪v.spatialPart, n⟫_ℝ =
      √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * exp (-v.rapidity n) := by
  -- `e^{-y} = √(v⁰ - v_∥) / √(v⁰ + v_∥)`, the forward computation with the two components swapped
  rw [exp_neg, exp_rapidity h, inv_div, sq_sub_sq, mul_comm (v.timeComponent + _)]
  exact eq_sqrt_mul_mul_sqrt_div (by linarith [le_abs_self ⟪v.spatialPart, n⟫_ℝ])
    (by linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ])

/-- Inside the forward light cone along `n`, the energy of a four-vector is `m_T cosh y`, with
`m_T = √((v⁰)² - v_∥²)` its transverse mass and `y` its rapidity along `n`. -/
theorem timeComponent_eq_sqrt_mul_cosh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    v.timeComponent = √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * cosh (v.rapidity n) := by
  rw [cosh_eq]
  linear_combination (timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity h +
    timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity h) / 2

/-- Inside the forward light cone along `n`, the momentum along `n` of a four-vector is
`m_T sinh y`, with `m_T = √((v⁰)² - v_∥²)` its transverse mass and `y` its rapidity along `n`. -/
theorem inner_spatialPart_eq_sqrt_mul_sinh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    ⟪v.spatialPart, n⟫_ℝ =
      √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * sinh (v.rapidity n) := by
  rw [sinh_eq]
  linear_combination (timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity h -
    timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity h) / 2

/-- **A collinear four-vector from its invariant mass and rapidity, forward component.** If the
spatial part of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then
`v⁰ + a = W e^{y}`, with `W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ}
    (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    v.timeComponent + a = √⟪v, v⟫ₘ * exp (v.rapidity n) := by
  have hpar := inner_spatialPart_eq_of_spatialPart_eq_smul hn hv
  have := timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity (hpar ▸ h)
  rwa [← minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul hn hv, hpar] at this

/-- **A collinear four-vector from its invariant mass and rapidity, backward component.** If the
spatial part of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then
`v⁰ - a = W e^{-y}`, with `W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ}
    (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    v.timeComponent - a = √⟪v, v⟫ₘ * exp (-v.rapidity n) := by
  have hpar := inner_spatialPart_eq_of_spatialPart_eq_smul hn hv
  have := timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity (hpar ▸ h)
  rwa [← minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul hn hv, hpar] at this

/-- The energy of a collinear four-vector is `W cosh y`. -/
theorem timeComponent_eq_sqrt_minkowskiProduct_mul_cosh_rapidity_of_spatialPart_eq_smul
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ}
    (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    v.timeComponent = √⟪v, v⟫ₘ * cosh (v.rapidity n) := by
  have hpar := inner_spatialPart_eq_of_spatialPart_eq_smul hn hv
  rw [minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul hn hv]
  exact timeComponent_eq_sqrt_mul_cosh_rapidity (hpar ▸ h)

/-- The momentum `a` along the axis of a collinear four-vector of spatial part `a • n` is
`W sinh y`. -/
theorem eq_sqrt_minkowskiProduct_mul_sinh_rapidity_of_spatialPart_eq_smul {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n)
    (h : |a| < v.timeComponent) :
    a = √⟪v, v⟫ₘ * sinh (v.rapidity n) := by
  have hpar := inner_spatialPart_eq_of_spatialPart_eq_smul hn hv
  have := inner_spatialPart_eq_sqrt_mul_sinh_rapidity (hpar ▸ h)
  rwa [← minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul hn hv, hpar] at this

end Vector
end Lorentz
