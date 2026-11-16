/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Artanh
public import EpsilonEridani.Mathematics.Algebra.Order.Abs
public import EpsilonEridani.Mathematics.Analysis.Real.Sqrt
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions

/-!
# The rapidity of a four-vector along an axis

The rapidity of a four-vector `v` along a spatial direction `n` is
`y = artanh (⟪v.spatialPart, n⟫ / (‖n‖ v⁰))` (`Lorentz.Vector.rapidity`). The direction is
normalised in the definition, so the rapidity along `n` depends only on the direction of `n`
(`Lorentz.Vector.rapidity_smul_right_of_pos`); for a unit vector `n` it is `artanh (v_∥ / v⁰)`,
where `v_∥ = ⟪v.spatialPart, n⟫` is the component of the spatial part along `n`
(`Lorentz.Vector.rapidity_eq_artanh_of_norm_eq_one`). The value is the rapidity only for
`|v_∥| < v⁰`: on and outside that cone (so for a null vector along `n`, whose rapidity is
physically infinite), and for `n = 0`, it is the junk value `0` of Mathlib's `Real.artanh`.

For a unit vector `n` and `|v_∥| < v⁰` (the forward cone of the projection of `v` onto the plane
spanned by the time axis and `n`), the rapidity recovers the velocity, `tanh y = v_∥ / v⁰`
(`Lorentz.Vector.tanh_rapidity`), and it is half the logarithm of the ratio of the two light-cone
components along `n`: `e^{y} = √(v⁰ + v_∥) / √(v⁰ - v_∥)` (`Lorentz.Vector.exp_rapidity`), so
`e^{2y} = (v⁰ + v_∥) / (v⁰ - v_∥)` (`Lorentz.Vector.exp_two_mul_rapidity`) and
`y = ½ log ((v⁰ + v_∥) / (v⁰ - v_∥))` (`Lorentz.Vector.rapidity_eq_half_log`).

The two light-cone components multiply to the square `m_T² = (v⁰)² - v_∥²` of the transverse mass
along `n`, so for `|v_∥| < v⁰` the energy and the component along `n` of a four-vector are fixed
by its transverse mass and its rapidity: `v⁰ ± v_∥ = m_T e^{±y}`
(`Lorentz.Vector.timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity`,
`Lorentz.Vector.timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity`), equivalently
`v⁰ = m_T cosh y` and `v_∥ = m_T sinh y`.

For a four-vector whose spatial part lies along a unit vector `n`, the transverse mass is the
invariant mass `W = √⟪v, v⟫ₘ`
(`Lorentz.Vector.minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul`, in
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions`), and the
light-cone relations read `v⁰ ± a = W e^{±y}` with `e^{2y} = (v⁰ + a) / (v⁰ - a)`, so that
`v⁰ = W cosh y` and `a = W sinh y` (the `_of_spatialPart_eq_smul` forms).

Collinearity is preserved by sums, so the same relations hold for the system `u + v` of two
four-vectors with spatial parts `a • n` and `b • n`: for `|a + b| < u⁰ + v⁰`,
`u⁰ + v⁰ ± (a + b) = W e^{±y}`, `e^{2y} = (u⁰ + v⁰ + (a + b)) / (u⁰ + v⁰ - (a + b))` and
`u⁰ + v⁰ = W cosh y`, with `W` and `y` the invariant mass and the rapidity of `u + v`
(`Lorentz.Vector.exp_two_mul_rapidity_add_of_spatialPart_eq_smul` and its companions). For two
null vectors of positive energy, one along and one against `n`, these reduce to `e^{2y} = u⁰ / v⁰`,
`2 u⁰ = W e^{y}` and `2 v⁰ = W e^{-y}`, with `W² = 4 u⁰ v⁰`
(`Lorentz.Vector.minkowskiProduct_add_self_eq_four_mul_of_spatialPart_eq_smul`).

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

/-- The rapidity `artanh (⟪v.spatialPart, n⟫ / (‖n‖ v⁰))` of the four-vector `v` along the
spatial direction `n`; for a unit vector `n` it is `artanh (v_∥ / v⁰)`, with
`v_∥ = ⟪v.spatialPart, n⟫` the component of the spatial part along `n`. It is the rapidity only
for `|v_∥| < v⁰`; otherwise (on the light cone along `n`, so for a null vector along `n`, whose
rapidity is physically infinite, outside it, at `v⁰ = 0`, and at `n = 0`) it is the junk value `0`
of `Real.artanh`. -/
def rapidity (v : Vector d) (n : EuclideanSpace ℝ (Fin d)) : ℝ :=
  artanh (⟪v.spatialPart, n⟫_ℝ / (‖n‖ * v.timeComponent))

/-- Defining expression for `Lorentz.Vector.rapidity`. -/
theorem rapidity_def (v : Vector d) (n : EuclideanSpace ℝ (Fin d)) :
    v.rapidity n = artanh (⟪v.spatialPart, n⟫_ℝ / (‖n‖ * v.timeComponent)) :=
  (rfl)

/-- Along a unit vector `n`, the rapidity is `artanh (v_∥ / v⁰)`. -/
theorem rapidity_eq_artanh_of_norm_eq_one (v : Vector d) {n : EuclideanSpace ℝ (Fin d)}
    (hn : ‖n‖ = 1) : v.rapidity n = artanh (⟪v.spatialPart, n⟫_ℝ / v.timeComponent) := by
  rw [rapidity_def, hn, one_mul]

/-- The rapidity along `n` depends only on the direction of `n`: rescaling `n` by a positive
factor leaves it unchanged. -/
theorem rapidity_smul_right_of_pos (v : Vector d) {c : ℝ} (hc : 0 < c)
    (n : EuclideanSpace ℝ (Fin d)) : v.rapidity (c • n) = v.rapidity n := by
  rw [rapidity_def, rapidity_def, real_inner_smul_right, norm_smul, Real.norm_of_nonneg hc.le,
    mul_assoc, mul_div_mul_left _ _ hc.ne']

/-- For `|v_∥| < v⁰` the ratio `v_∥ / v⁰` lies in `(-1, 1)`, where `artanh` inverts `tanh`. -/
theorem inner_spatialPart_div_timeComponent_mem_Ioo {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    ⟪v.spatialPart, n⟫_ℝ / v.timeComponent ∈ Set.Ioo (-1) 1 := by
  have ht : 0 < v.timeComponent := (abs_nonneg _).trans_lt h
  rw [Set.mem_Ioo, lt_div_iff₀ ht, div_lt_iff₀ ht]
  constructor <;> linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ, le_abs_self ⟪v.spatialPart, n⟫_ℝ]

/-- For a unit vector `n` and `|v_∥| < v⁰`, the rapidity `y` along `n` recovers the velocity
along `n`, `tanh y = v_∥ / v⁰`. -/
theorem tanh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1)
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    tanh (v.rapidity n) = ⟪v.spatialPart, n⟫_ℝ / v.timeComponent := by
  rw [rapidity_eq_artanh_of_norm_eq_one v hn]
  exact tanh_artanh (inner_spatialPart_div_timeComponent_mem_Ioo h)

/-- For a unit vector `n` and `|v_∥| < v⁰`, `e^{y} = √(v⁰ + v_∥) / √(v⁰ - v_∥)`. -/
theorem exp_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1)
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    exp (v.rapidity n) = √(v.timeComponent + ⟪v.spatialPart, n⟫_ℝ) /
      √(v.timeComponent - ⟪v.spatialPart, n⟫_ℝ) := by
  have ht : v.timeComponent ≠ 0 := ((abs_nonneg _).trans_lt h).ne'
  have hA : 0 ≤ v.timeComponent + ⟪v.spatialPart, n⟫_ℝ := by
    linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ]
  rw [rapidity_eq_artanh_of_norm_eq_one v hn,
    exp_artanh (inner_spatialPart_div_timeComponent_mem_Ioo h), ← Real.sqrt_div hA]
  congr 1
  field_simp

/-- **The rapidity is half the logarithm of the ratio of the light-cone components.** For a unit
vector `n` and `|v_∥| < v⁰`, `e^{2y} = (v⁰ + v_∥) / (v⁰ - v_∥)`. -/
theorem exp_two_mul_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1)
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    exp (2 * v.rapidity n) = (v.timeComponent + ⟪v.spatialPart, n⟫_ℝ) /
      (v.timeComponent - ⟪v.spatialPart, n⟫_ℝ) := by
  rw [two_mul, exp_add, exp_rapidity hn h, div_mul_div_comm,
    Real.mul_self_sqrt (by linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ]),
    Real.mul_self_sqrt (by linarith [le_abs_self ⟪v.spatialPart, n⟫_ℝ])]

/-- **The rapidity as a logarithm.** For a unit vector `n` and `|v_∥| < v⁰`,
`y = ½ log ((v⁰ + v_∥) / (v⁰ - v_∥))`. -/
theorem rapidity_eq_half_log {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1)
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    v.rapidity n = 1 / 2 * log ((v.timeComponent + ⟪v.spatialPart, n⟫_ℝ) /
      (v.timeComponent - ⟪v.spatialPart, n⟫_ℝ)) := by
  rw [← exp_two_mul_rapidity hn h, log_exp]
  ring

/-- **The forward light-cone component from the rapidity.** For a unit vector `n` and
`|v_∥| < v⁰`, `v⁰ + v_∥ = m_T e^{y}`, with `m_T = √((v⁰)² - v_∥²)` the transverse mass and `y`
the rapidity along `n`. -/
theorem timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1)
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    v.timeComponent + ⟪v.spatialPart, n⟫_ℝ =
      √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * exp (v.rapidity n) := by
  rw [exp_rapidity hn h, sq_sub_sq]
  exact (sqrt_mul_mul_sqrt_div_sqrt (by linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ])
    (by linarith [le_abs_self ⟪v.spatialPart, n⟫_ℝ])).symm

/-- **The backward light-cone component from the rapidity.** For a unit vector `n` and
`|v_∥| < v⁰`, `v⁰ - v_∥ = m_T e^{-y}`, with `m_T = √((v⁰)² - v_∥²)` the transverse mass and `y`
the rapidity along `n`. -/
theorem timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1)
    (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    v.timeComponent - ⟪v.spatialPart, n⟫_ℝ =
      √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * exp (-v.rapidity n) := by
  -- `e^{-y} = √(v⁰ - v_∥) / √(v⁰ + v_∥)`, the forward computation with the two components swapped
  rw [exp_neg, exp_rapidity hn h, inv_div, sq_sub_sq, mul_comm (v.timeComponent + _)]
  exact (sqrt_mul_mul_sqrt_div_sqrt (by linarith [le_abs_self ⟪v.spatialPart, n⟫_ℝ])
    (by linarith [neg_abs_le ⟪v.spatialPart, n⟫_ℝ])).symm

/-- For a unit vector `n` and `|v_∥| < v⁰`, the energy of a four-vector is `m_T cosh y`, with
`m_T = √((v⁰)² - v_∥²)` its transverse mass and `y` its rapidity along `n`. -/
theorem timeComponent_eq_sqrt_mul_cosh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (hn : ‖n‖ = 1) (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    v.timeComponent = √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * cosh (v.rapidity n) := by
  rw [cosh_eq]
  linear_combination (timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity hn h +
    timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity hn h) / 2

/-- For a unit vector `n` and `|v_∥| < v⁰`, the momentum `v_∥ = ⟪v.spatialPart, n⟫` of a
four-vector along `n` is `m_T sinh y`, with `m_T = √((v⁰)² - v_∥²)` its transverse mass and `y`
its rapidity along `n`. -/
theorem inner_spatialPart_eq_sqrt_mul_sinh_rapidity {v : Vector d} {n : EuclideanSpace ℝ (Fin d)}
    (hn : ‖n‖ = 1) (h : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent) :
    ⟪v.spatialPart, n⟫_ℝ =
      √(v.timeComponent ^ 2 - ⟪v.spatialPart, n⟫_ℝ ^ 2) * sinh (v.rapidity n) := by
  rw [sinh_eq]
  linear_combination (timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity hn h -
    timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity hn h) / 2

/-! ### A four-vector along an axis -/

/-- A four-vector whose spatial part is `a • n`, for a unit vector `n`, with `|a| < v⁰` has
`|v_∥| < v⁰`, the hypothesis of the general rapidity relations. -/
theorem abs_inner_spatialPart_lt_timeComponent_of_spatialPart_eq_smul {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n)
    (h : |a| < v.timeComponent) : |⟪v.spatialPart, n⟫_ℝ| < v.timeComponent := by
  rwa [inner_spatialPart_eq_of_spatialPart_eq_smul hn hv]

/-- **The exponential of twice the rapidity of a collinear four-vector.** If the spatial part
of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then `e^{2y} = (v⁰ + a) / (v⁰ - a)`, with
`y` the rapidity of `v` along `n`. -/
theorem exp_two_mul_rapidity_of_spatialPart_eq_smul {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n)
    (h : |a| < v.timeComponent) :
    exp (2 * v.rapidity n) = (v.timeComponent + a) / (v.timeComponent - a) := by
  rw [exp_two_mul_rapidity hn
      (abs_inner_spatialPart_lt_timeComponent_of_spatialPart_eq_smul hn hv h),
    inner_spatialPart_eq_of_spatialPart_eq_smul hn hv]

/-- **A collinear four-vector from its invariant mass and rapidity, forward component.** If the
spatial part of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then
`v⁰ + a = W e^{y}`, with `W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ}
    (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    v.timeComponent + a = √⟪v, v⟫ₘ * exp (v.rapidity n) := by
  rw [minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul hn hv,
    ← inner_spatialPart_eq_of_spatialPart_eq_smul hn hv]
  exact timeComponent_add_inner_spatialPart_eq_sqrt_mul_exp_rapidity hn
    (abs_inner_spatialPart_lt_timeComponent_of_spatialPart_eq_smul hn hv h)

/-- **A collinear four-vector from its invariant mass and rapidity, backward component.** If the
spatial part of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then
`v⁰ - a = W e^{-y}`, with `W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ}
    (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    v.timeComponent - a = √⟪v, v⟫ₘ * exp (-v.rapidity n) := by
  rw [minkowskiProduct_self_eq_sq_sub_inner_sq_of_spatialPart_eq_smul hn hv,
    ← inner_spatialPart_eq_of_spatialPart_eq_smul hn hv]
  exact timeComponent_sub_inner_spatialPart_eq_sqrt_mul_exp_neg_rapidity hn
    (abs_inner_spatialPart_lt_timeComponent_of_spatialPart_eq_smul hn hv h)

/-- **A collinear four-vector from its invariant mass and rapidity, energy.** If the spatial part
of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then `v⁰ = W cosh y`, with
`W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem timeComponent_eq_sqrt_minkowskiProduct_mul_cosh_rapidity_of_spatialPart_eq_smul
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ}
    (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    v.timeComponent = √⟪v, v⟫ₘ * cosh (v.rapidity n) := by
  rw [cosh_eq]
  linear_combination
    (timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul hn hv h +
      timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul hn hv
        h) / 2

/-- **A collinear four-vector from its invariant mass and rapidity, momentum.** If the spatial
part of `v` is `a • n` for a unit vector `n` and `|a| < v⁰`, then `a = W sinh y`, with
`W = √⟪v, v⟫ₘ` and `y` the rapidity along `n`. -/
theorem eq_sqrt_minkowskiProduct_mul_sinh_rapidity_of_spatialPart_eq_smul
    {v : Vector d} {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ}
    (hv : v.spatialPart = a • n) (h : |a| < v.timeComponent) :
    a = √⟪v, v⟫ₘ * sinh (v.rapidity n) := by
  rw [sinh_eq]
  linear_combination
    (timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul hn hv h -
      timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul hn hv
        h) / 2

/-! ### The system of two four-vectors along an axis -/

section Add

variable {u v : Vector d} {n : EuclideanSpace ℝ (Fin d)} {a b : ℝ}

/-- **The rapidity of a system of two collinear four-vectors.** If the spatial parts of `u` and
`v` are `a • n` and `b • n` for a unit vector `n` and `|a + b| < u⁰ + v⁰`, the rapidity `y` of
`u + v` along `n` has `e^{2y} = (u⁰ + v⁰ + (a + b)) / (u⁰ + v⁰ - (a + b))`. -/
theorem exp_two_mul_rapidity_add_of_spatialPart_eq_smul (hn : ‖n‖ = 1)
    (hu : u.spatialPart = a • n) (hv : v.spatialPart = b • n)
    (h : |a + b| < u.timeComponent + v.timeComponent) :
    exp (2 * (u + v).rapidity n) = (u.timeComponent + v.timeComponent + (a + b)) /
      (u.timeComponent + v.timeComponent - (a + b)) := by
  rw [← timeComponent_add] at h ⊢
  exact exp_two_mul_rapidity_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_smul_of_spatialPart_eq_smul hu hv) h

/-- **A system of two collinear four-vectors from its invariant mass and rapidity, forward
component.** If the spatial parts of `u` and `v` are `a • n` and `b • n` for a unit vector `n` and
`|a + b| < u⁰ + v⁰`, then `u⁰ + v⁰ + (a + b) = W e^{y}`, with `W` and `y` the invariant mass and
the rapidity of `u + v` along `n`. -/
theorem add_add_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_spatialPart_eq_smul
    (hn : ‖n‖ = 1) (hu : u.spatialPart = a • n) (hv : v.spatialPart = b • n)
    (h : |a + b| < u.timeComponent + v.timeComponent) :
    u.timeComponent + v.timeComponent + (a + b) =
      √⟪u + v, u + v⟫ₘ * exp ((u + v).rapidity n) := by
  rw [← timeComponent_add] at h ⊢
  exact timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_smul_of_spatialPart_eq_smul hu hv) h

/-- **A system of two collinear four-vectors from its invariant mass and rapidity, backward
component.** If the spatial parts of `u` and `v` are `a • n` and `b • n` for a unit vector `n` and
`|a + b| < u⁰ + v⁰`, then `u⁰ + v⁰ - (a + b) = W e^{-y}`, with `W` and `y` the invariant mass and
the rapidity of `u + v` along `n`. -/
theorem add_sub_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    (hn : ‖n‖ = 1) (hu : u.spatialPart = a • n) (hv : v.spatialPart = b • n)
    (h : |a + b| < u.timeComponent + v.timeComponent) :
    u.timeComponent + v.timeComponent - (a + b) =
      √⟪u + v, u + v⟫ₘ * exp (-(u + v).rapidity n) := by
  rw [← timeComponent_add] at h ⊢
  exact timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_smul_of_spatialPart_eq_smul hu hv) h

/-- **The energy of a system of two collinear four-vectors.** If the spatial parts of `u` and `v`
are `a • n` and `b • n` for a unit vector `n` and `|a + b| < u⁰ + v⁰`, then
`u⁰ + v⁰ = W cosh y`, with `W` and `y` the invariant mass and the rapidity of `u + v` along `n`. -/
theorem add_eq_sqrt_minkowskiProduct_add_self_mul_cosh_rapidity_of_spatialPart_eq_smul
    (hn : ‖n‖ = 1) (hu : u.spatialPart = a • n) (hv : v.spatialPart = b • n)
    (h : |a + b| < u.timeComponent + v.timeComponent) :
    u.timeComponent + v.timeComponent = √⟪u + v, u + v⟫ₘ * cosh ((u + v).rapidity n) := by
  rw [cosh_eq]
  linear_combination
    (add_add_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_spatialPart_eq_smul hn hu hv h +
      add_sub_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_spatialPart_eq_smul hn hu
        hv h) / 2

/-- **Two null four-vectors colliding head-on, forward component.** If `u` is null along a unit
vector `n` and `v` null against it, `u.spatialPart = u⁰ • n` and `v.spatialPart = -v⁰ • n`, with
`0 < u⁰` and `0 < v⁰`, then `2 u⁰ = W e^{y}`, with `W` and `y` the invariant mass and the
rapidity of `u + v` along `n`. -/
theorem two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_spatialPart_eq_smul
    (hn : ‖n‖ = 1) (hu : u.spatialPart = u.timeComponent • n)
    (hv : v.spatialPart = -v.timeComponent • n) (hu₀ : 0 < u.timeComponent)
    (hv₀ : 0 < v.timeComponent) :
    2 * u.timeComponent = √⟪u + v, u + v⟫ₘ * exp ((u + v).rapidity n) := by
  have h := add_add_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_spatialPart_eq_smul hn
    hu hv (by rw [← sub_eq_add_neg]
              exact abs_sub_lt_add_of_pos_of_neg_lt_of_le hu₀ (neg_lt_self hv₀) le_rfl)
  linear_combination h

/-- **Two null four-vectors colliding head-on, backward component.** If `u` is null along a unit
vector `n` and `v` null against it, `u.spatialPart = u⁰ • n` and `v.spatialPart = -v⁰ • n`, with
`0 < u⁰` and `0 < v⁰`, then `2 v⁰ = W e^{-y}`, with `W` and `y` the invariant mass and the
rapidity of `u + v` along `n`. -/
theorem two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    (hn : ‖n‖ = 1) (hu : u.spatialPart = u.timeComponent • n)
    (hv : v.spatialPart = -v.timeComponent • n) (hu₀ : 0 < u.timeComponent)
    (hv₀ : 0 < v.timeComponent) :
    2 * v.timeComponent = √⟪u + v, u + v⟫ₘ * exp (-(u + v).rapidity n) := by
  have h := add_sub_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    hn hu hv (by rw [← sub_eq_add_neg]
                 exact abs_sub_lt_add_of_pos_of_neg_lt_of_le hu₀ (neg_lt_self hv₀) le_rfl)
  linear_combination h

/-- **Two null four-vectors colliding head-on, rapidity.** If `u` is null along a unit vector `n`
and `v` null against it, `u.spatialPart = u⁰ • n` and `v.spatialPart = -v⁰ • n`, with `0 < u⁰`
and `0 < v⁰`, the rapidity `y` of `u + v` along `n` has `e^{2y} = u⁰ / v⁰`. -/
theorem exp_two_mul_rapidity_add_eq_div_of_spatialPart_eq_smul (hn : ‖n‖ = 1)
    (hu : u.spatialPart = u.timeComponent • n) (hv : v.spatialPart = -v.timeComponent • n)
    (hu₀ : 0 < u.timeComponent) (hv₀ : 0 < v.timeComponent) :
    exp (2 * (u + v).rapidity n) = u.timeComponent / v.timeComponent := by
  have hF := two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_spatialPart_eq_smul hn
    hu hv hu₀ hv₀
  have hB := two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    hn hu hv hu₀ hv₀
  have he : exp (2 * (u + v).rapidity n) * exp (-(u + v).rapidity n) =
      exp ((u + v).rapidity n) := by
    rw [← exp_add]
    ring_nf
  rw [eq_div_iff hv₀.ne']
  -- `e^{2y} (2 v⁰) = W e^{2y} e^{-y} = W e^{y} = 2 u⁰`
  linear_combination exp (2 * (u + v).rapidity n) / 2 * hB - hF / 2 +
    √⟪u + v, u + v⟫ₘ / 2 * he

end Add

end Vector
end Lorentz
