/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions

/-!
# The virtuality of an emitted particle

A source of mass `m` and energy `E` that emits a particle and leaves with energy `E'` at
scattering angle `θ` hands the emitted particle the four-momentum `q = p - p'`, whose virtuality is

  `Q² = -q² = 2 (E E' - |p| |p'| cos θ - m²)`,  `|p| = √(E² - m²)`,  `|p'| = √(E'² - m²)`,

where `|p|` and `|p'|` are the magnitudes of the spatial parts (the three-momenta) of `p` and `p'`.

This module develops that formula and the range it takes.

* `emissionVirtuality m E E' θ` is the right-hand side above, and
  `neg_minkowskiProduct_sub_self_eq_emissionVirtuality` proves that it *is* `-q²` for any pair of
  on-shell four-momenta of `Physlib`, with `θ` the angle between their spatial parts.
* Its value at `θ = 0` is a lower bound at every angle
  (`emissionVirtuality_zero_le_emissionVirtuality`), and it is monotone in the angle on `[0, π]`, so
  the virtualities reachable at scattering angle at most `θmax` form the interval between its value
  at `θ = 0` and its value at `θmax` (`image_emissionVirtuality_Icc`).
* The value at `θ = 0` is the kinematic minimum. It vanishes for a massless source, and is strictly
  positive as soon as the source is massive and the emitted particle carries energy
  (`emissionVirtuality_zero_pos_iff`). It strictly exceeds the familiar
  `m² (E - E')² / (E E')` (`sq_mul_sub_sq_div_mul_lt_emissionVirtuality_zero`).
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace Kinematics

open Real InnerProductGeometry Set
open scoped InnerProductSpace Lorentz.Vector

/-! ### The emission virtuality as a function of the scattering angle -/

/-- The virtuality `Q² = 2 (E E' - |p| |p'| cos θ - m²)` of the particle emitted when a source of
mass `m` goes from energy `E` to energy `E'` and is scattered by the angle `θ`, with the
magnitudes of the three-momenta `|p| = √(E² - m²)` and `|p'| = √(E'² - m²)` fixed by the mass
shell. -/
def emissionVirtuality (m E E' θ : ℝ) : ℝ :=
  2 * (E * E' - √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) * cos θ - m ^ 2)

/-- Defining expression for `emissionVirtuality`. -/
theorem emissionVirtuality_def (m E E' θ : ℝ) :
    emissionVirtuality m E E' θ =
      2 * (E * E' - √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) * cos θ - m ^ 2) :=
  (rfl)

/-- The emission virtuality is continuous in the scattering angle. -/
theorem continuous_emissionVirtuality (m E E' : ℝ) : Continuous (emissionVirtuality m E E') := by
  unfold emissionVirtuality
  fun_prop

/-- The value of the emission virtuality at zero scattering angle is a lower bound for its value at
every angle. -/
theorem emissionVirtuality_zero_le_emissionVirtuality (m E E' θ : ℝ) :
    emissionVirtuality m E E' 0 ≤ emissionVirtuality m E E' θ := by
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  simp only [emissionVirtuality, cos_zero, mul_one]
  nlinarith [mul_le_mul_of_nonneg_left (cos_le_one θ) hP]

/-- The emission virtuality grows with the scattering angle on `[0, π]`. -/
theorem monotoneOn_emissionVirtuality (m E E' : ℝ) :
    MonotoneOn (emissionVirtuality m E E') (Icc 0 π) := by
  intro θ hθ θ' hθ' hle
  have hcos : cos θ' ≤ cos θ := cos_le_cos_of_nonneg_of_le_pi hθ.1 hθ'.2 hle
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  unfold emissionVirtuality
  nlinarith [mul_le_mul_of_nonneg_left hcos hP]

/-- The virtualities reachable at scattering angles in `[0, θmax]` form the interval between the
kinematic minimum, at `θ = 0`, and the value at `θmax`. -/
theorem image_emissionVirtuality_Icc (m E E' : ℝ) {θmax : ℝ} (h0 : 0 ≤ θmax) (hπ : θmax ≤ π) :
    emissionVirtuality m E E' '' Icc 0 θmax =
      Icc (emissionVirtuality m E E' 0) (emissionVirtuality m E E' θmax) :=
  (continuous_emissionVirtuality m E E').continuousOn.image_Icc_of_monotoneOn h0
    ((monotoneOn_emissionVirtuality m E E').mono (Icc_subset_Icc_right hπ))

/-- A massless source emits at zero minimum virtuality. -/
theorem emissionVirtuality_zero_zero_eq_zero_of_nonneg {E E' : ℝ} (hE : 0 ≤ E) (hE' : 0 ≤ E') :
    emissionVirtuality 0 E E' 0 = 0 := by
  simp [emissionVirtuality, Real.sqrt_sq hE, Real.sqrt_sq hE']

/-- A source that keeps all of its energy emits at zero minimum virtuality. -/
theorem emissionVirtuality_self_zero_eq_zero {m E : ℝ} (hE : |m| ≤ |E|) :
    emissionVirtuality m E E 0 = 0 := by
  simp only [emissionVirtuality, cos_zero, mul_one,
    Real.mul_self_sqrt (sub_nonneg.2 (sq_le_sq.2 hE))]
  ring

/-- The algebraic identity behind the kinematic minimum: with `A = E E' - m²` and the momenta
`P = √(E² - m²)`, `P' = √(E'² - m²)`, one has `A² - (P P')² = m² (E - E')²`. -/
theorem sq_sub_sq_sqrt_mul_sqrt_eq_sq_mul_sub_sq {m E E' : ℝ} (hE : |m| ≤ |E|)
    (hE' : |m| ≤ |E'|) :
    (E * E' - m ^ 2) ^ 2 - (√(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2)) ^ 2 =
      m ^ 2 * (E - E') ^ 2 := by
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.2 (sq_le_sq.2 hE)),
    Real.sq_sqrt (sub_nonneg.2 (sq_le_sq.2 hE'))]
  ring

/-- When both energies lie above the mass, the momentum product
`P P' = √(E² - m²) √(E'² - m²)` is at most `E E' - m²`. -/
theorem sqrt_mul_sqrt_le_mul_sub_sq {m E E' : ℝ} (hE : |m| ≤ E) (hE' : |m| ≤ E') :
    √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) ≤ E * E' - m ^ 2 := by
  have hA : 0 ≤ E * E' - m ^ 2 := by
    nlinarith [sq_abs m, mul_le_mul hE hE' (abs_nonneg m) (le_trans (abs_nonneg m) hE)]
  have hid := sq_sub_sq_sqrt_mul_sqrt_eq_sq_mul_sub_sq (hE.trans (le_abs_self E))
    (hE'.trans (le_abs_self E'))
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  nlinarith [sq_nonneg m, sq_nonneg (E - E')]

/-- For a massive source and an emitted particle carrying energy, the momentum product
`P P' = √(E² - m²) √(E'² - m²)` is strictly below `E E' - m²`. -/
theorem sqrt_mul_sqrt_lt_mul_sub_sq {m E E' : ℝ} (hm : m ≠ 0) (hE : |m| ≤ E) (hE' : |m| ≤ E')
    (hne : E ≠ E') :
    √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) < E * E' - m ^ 2 := by
  have hB : 0 < m ^ 2 * (E - E') ^ 2 := by
    have := sub_ne_zero.2 hne
    positivity
  have hid := sq_sub_sq_sqrt_mul_sqrt_eq_sq_mul_sub_sq (hE.trans (le_abs_self E))
    (hE'.trans (le_abs_self E'))
  refine (sqrt_mul_sqrt_le_mul_sub_sq hE hE').lt_of_ne fun h => ?_
  rw [h, sub_self] at hid
  linarith

/-- The kinematic minimum of the virtuality is non-negative whenever both energies lie above the
mass. -/
theorem emissionVirtuality_zero_nonneg {m E E' : ℝ} (hE : |m| ≤ E) (hE' : |m| ≤ E') :
    0 ≤ emissionVirtuality m E E' 0 := by
  have := sqrt_mul_sqrt_le_mul_sub_sq hE hE'
  simp only [emissionVirtuality, cos_zero, mul_one]
  linarith

/-- **The kinematic minimum is strictly positive exactly for a massive source emitting a particle
of non-zero energy.** -/
theorem emissionVirtuality_zero_pos_iff {m E E' : ℝ} (hE : |m| ≤ E) (hE' : |m| ≤ E') :
    0 < emissionVirtuality m E E' 0 ↔ m ≠ 0 ∧ E ≠ E' := by
  constructor
  · intro h
    refine ⟨fun hm => ?_, fun hEE => ?_⟩
    · subst hm
      rw [emissionVirtuality_zero_zero_eq_zero_of_nonneg (le_trans (abs_nonneg _) hE)
        (le_trans (abs_nonneg _) hE')] at h
      exact lt_irrefl _ h
    · subst hEE
      rw [emissionVirtuality_self_zero_eq_zero (hE.trans (le_abs_self E))] at h
      exact lt_irrefl _ h
  · rintro ⟨hm, hne⟩
    have := sqrt_mul_sqrt_lt_mul_sub_sq hm hE hE' hne
    simp only [emissionVirtuality, cos_zero, mul_one]
    linarith

/-- **The kinematic minimum strictly exceeds `m² (E - E')² / (E E' - m²)`.** For a high-energy
source the bound approaches the minimum, and it is itself above the familiar high-energy form
`m² (E - E')² / (E E')`; see `sq_mul_sub_sq_div_mul_lt_emissionVirtuality_zero`. -/
theorem sq_mul_sub_sq_div_mul_sub_sq_lt_emissionVirtuality_zero {m E E' : ℝ} (hm : m ≠ 0)
    (hE : |m| ≤ E) (hE' : |m| ≤ E') (hne : E ≠ E') :
    m ^ 2 * (E - E') ^ 2 / (E * E' - m ^ 2) < emissionVirtuality m E E' 0 := by
  have hlt := sqrt_mul_sqrt_lt_mul_sub_sq hm hE hE' hne
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  have hA : 0 < E * E' - m ^ 2 := hP.trans_lt hlt
  have hid := sq_sub_sq_sqrt_mul_sqrt_eq_sq_mul_sub_sq (hE.trans (le_abs_self E))
    (hE'.trans (le_abs_self E'))
  rw [div_lt_iff₀ hA]
  simp only [emissionVirtuality, cos_zero, mul_one]
  nlinarith

/-- **The kinematic minimum strictly exceeds its high-energy form `m² (E - E')² / (E E')`.** -/
theorem sq_mul_sub_sq_div_mul_lt_emissionVirtuality_zero {m E E' : ℝ} (hm : m ≠ 0) (hE : |m| ≤ E)
    (hE' : |m| ≤ E') (hne : E ≠ E') :
    m ^ 2 * (E - E') ^ 2 / (E * E') < emissionVirtuality m E E' 0 := by
  have hlt := sqrt_mul_sqrt_lt_mul_sub_sq hm hE hE' hne
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  have hA : 0 < E * E' - m ^ 2 := hP.trans_lt hlt
  have hm2 : 0 < m ^ 2 := by positivity
  have hB : 0 < m ^ 2 * (E - E') ^ 2 := mul_pos hm2 (by
    have := sub_ne_zero.2 hne
    positivity)
  refine lt_of_le_of_lt ?_ (sq_mul_sub_sq_div_mul_sub_sq_lt_emissionVirtuality_zero hm hE hE' hne)
  exact div_le_div_of_nonneg_left hB.le hA (by linarith)

/-! ### The emission virtuality of on-shell four-momenta -/

/-- **The virtuality of the emitted particle.** If a source of mass `m` with four-momentum `p`
emits a particle and leaves with four-momentum `p'` of the same mass, the particle `q = p - p'` has
virtuality `-q² = emissionVirtuality m E E' θ`, with `E`, `E'` the two energies and `θ` the angle
between the spatial momenta. -/
theorem neg_minkowskiProduct_sub_self_eq_emissionVirtuality {d : ℕ} {p p' : Lorentz.Vector d}
    {m : ℝ} (hp : ⟪p, p⟫ₘ = m ^ 2) (hp' : ⟪p', p'⟫ₘ = m ^ 2) :
    -⟪p - p', p - p'⟫ₘ = emissionVirtuality m p.timeComponent p'.timeComponent
      (angle p.spatialPart p'.spatialPart) := by
  rw [Lorentz.Vector.minkowskiProduct_sub_self, hp, hp',
    Lorentz.Vector.minkowskiProduct_eq_timeComponent_spatialPart, ← cos_angle_mul_norm_mul_norm,
    p.norm_spatialPart_eq_sqrt_sq_sub_minkowskiProduct_self,
    p'.norm_spatialPart_eq_sqrt_sq_sub_minkowskiProduct_self, hp, hp', emissionVirtuality]
  ring

end Kinematics
end Scattering
end QFT
end EpsilonEridani
