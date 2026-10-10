/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.Photoproduction.Kinematics.Basic
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.Rapidity

/-!
# The photon–target system: energy fraction, rapidity and invariant mass

A photon emitted by a charged source meets a target of mass `M` and energy `E` that travels
against it along the beam axis `n`. Three variables are used to label the photon:
* its energy fraction `x = k / E_s` relative to the source (`PhotonKinematics.energyFraction`);
* the invariant mass `W` of the photon–target system, `W² = (q + P)²`, which is the energy at
  which the photon–target cross section is evaluated;
* the rapidity `y` of the photon–target system along the beam axis, which is the rapidity of
  whatever the photon and the target produce, and the rapidity the literature attaches to the
  photon when it writes `k = (W / 2) e^{y}`.

This module proves that the three are interchangeable, by equalities between the four-vector
quantities rather than by convention. Write `p = √(E² - M²)` for the target momentum.
* For any photon four-momentum `q`, of any virtuality and direction,
  `W² = M² + q² + 2 (q⁰ E + p q_∥)` (`minkowskiProduct_add_self_of_target`), so the virtuality
  `Q² = -q²` enters `W²` explicitly.
* For a real photon of energy `k` along the beam axis, `W² = M² + 2 k (E + p)`
  (`minkowskiProduct_add_self_of_realPhoton`), so `W² = M² + 2 x E_s (E + p)` in terms of the
  energy fraction (`minkowskiProduct_add_self_eq_energyFraction`).
* Its rapidity obeys `e^{2y} = (2 k + E - p) / (E + p)`
  (`exp_two_mul_rapidity_add_of_realPhoton`) and `E + p = W e^{-y}`
  (`add_sqrt_eq_sqrt_mul_exp_neg_rapidity`), so that `W` and `y` determine each other at fixed
  target.
* Conversely `2 k = e^{y} (W² - M²) / W` (`two_mul_energy_eq_exp_rapidity_mul`), that is
  `x = e^{y} (W² - M²) / (2 W E_s)` (`energyFraction_eq_exp_rapidity_mul`).

For a massless target these reduce to the familiar `W² = 4 k E`, `k = (W / 2) e^{y}` and
`E = (W / 2) e^{-y}` (`minkowskiProduct_add_self_of_masslessTarget`,
`two_mul_energy_eq_sqrt_mul_exp_rapidity_of_masslessTarget`,
`two_mul_eq_sqrt_mul_exp_neg_rapidity_of_masslessTarget`).
With a massive target the relations stay exact; only their form changes.

## References

* G. Baur, K. Hencken, D. Trautmann, S. Sadovsky and Y. Kharlov, *Coherent γγ and γA interactions
  in very peripheral collisions at relativistic ion colliders*, Phys. Rep. **364** (2002) 359,
  section 2.
* A. J. Baltz et al., *The physics of ultraperipheral collisions at the LHC*, Phys. Rep. **458**
  (2008) 1, section 2, where `W² = 4 k E` and `k = (M / 2) e^{y}` are used.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace Photoproduction
namespace Kinematics

open Real Lorentz.Vector
open scoped InnerProductSpace Lorentz.Vector

variable {d : ℕ} {q P : Lorentz.Vector d} {n : EuclideanSpace ℝ (Fin d)} {M E k : ℝ}

/-! ### The invariant mass of a photon and a target -/

/-- **The invariant mass of a photon and a target.** For a target of mass `M` and energy `E`
travelling against the unit beam axis `n` and any photon four-momentum `q`, the photon–target
system has `W² = M² + q² + 2 (q⁰ E + p q_∥)`, with `p = √(E² - M²)` and
`q_∥ = ⟪q.spatialPart, n⟫`; the virtuality `Q² = -q²` of the photon lowers `W²`. -/
theorem minkowskiProduct_add_self_of_target (hn : ‖n‖ = 1) (hE : |M| ≤ E)
    (hP : P.timeComponent = E) (hP' : P.spatialPart = -√(E ^ 2 - M ^ 2) • n) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 + ⟪q, q⟫ₘ +
      2 * (q.timeComponent * E + √(E ^ 2 - M ^ 2) * ⟪q.spatialPart, n⟫_ℝ) := by
  have hp : √(E ^ 2 - M ^ 2) ^ 2 = E ^ 2 - M ^ 2 :=
    Real.sq_sqrt (sub_nonneg.2 (sq_le_sq' (by linarith [neg_abs_le M]) (by
      linarith [le_abs_self M])))
  have hPP : ⟪P, P⟫ₘ = M ^ 2 := by
    rw [minkowskiProduct_self_eq_sq_sub, hP, hP']
    simp only [norm_smul, hn, mul_one, Real.norm_eq_abs, sq_abs, neg_sq, hp]
    ring
  have hqP : ⟪q, P⟫ₘ = q.timeComponent * E + √(E ^ 2 - M ^ 2) * ⟪q.spatialPart, n⟫_ℝ := by
    rw [minkowskiProduct_eq_timeComponent_spatialPart, hP, hP', real_inner_smul_right]
    ring
  rw [minkowskiProduct_add_self, hPP, hqP]
  ring

/-- The photon–target system of a photon of energy `k` along the beam axis and a target of energy
`E` and momentum `p` against it has energy `k + E` and spatial part `(k - p) • n`. -/
private theorem components_add_target (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
    (hP : P.timeComponent = E) (hP' : P.spatialPart = -√(E ^ 2 - M ^ 2) • n) :
    (q + P).timeComponent = k + E ∧ (q + P).spatialPart = (k - √(E ^ 2 - M ^ 2)) • n := by
  refine ⟨by simp [hq, hP], ?_⟩
  have hsum : (q + P).spatialPart = q.spatialPart + P.spatialPart := by ext i; simp
  rw [hsum, hq', hP', sub_smul, _root_.neg_smul, ← sub_eq_add_neg]

/-- The system of a photon of energy `k > 0` along the beam axis and a target of energy `E > 0`
against it lies inside the forward light cone along the beam axis: `|k - p| < k + E`. -/
private theorem abs_sub_sqrt_lt_timeComponent_add (hq : q.timeComponent = k)
    (hP : P.timeComponent = E) (hk : 0 < k) (hE0 : 0 < E) :
    |k - √(E ^ 2 - M ^ 2)| < (q + P).timeComponent := by
  have hp : √(E ^ 2 - M ^ 2) ≤ E := by
    rw [Real.sqrt_le_left hE0.le]
    nlinarith [sq_nonneg M]
  have h0 : (q + P).timeComponent = k + E := by simp [hq, hP]
  rw [h0, abs_lt]
  constructor <;> linarith [Real.sqrt_nonneg (E ^ 2 - M ^ 2)]

section RealPhoton

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -√(E ^ 2 - M ^ 2) • n)
include hn hq hq' hP hP'

/-- **The invariant mass of a real photon and a target.** A real photon of energy `k` along the
unit beam axis and a target of mass `M` and energy `E` against it form a system of invariant mass
`W² = M² + 2 k (E + p)`, with `p = √(E² - M²)`. -/
theorem minkowskiProduct_add_self_of_realPhoton (hE : |M| ≤ E) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 + 2 * k * (E + √(E ^ 2 - M ^ 2)) := by
  have hqq : ⟪q, q⟫ₘ = 0 := by
    rw [minkowskiProduct_self_eq_sq_sub, hq, hq']
    simp only [norm_smul, hn, mul_one, Real.norm_eq_abs, sq_abs, sub_self]
  rw [minkowskiProduct_add_self_of_target hn hE hP hP', hqq, hq, hq']
  simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, hn]
  ring

/-- **The rapidity of a real photon and a target.** The photon–target system of a real photon of
energy `k` and a target of mass `M` and energy `E` has rapidity `y` along the photon direction with
`e^{2y} = (2 k + E - p) / (E + p)`, where `p = √(E² - M²)`. -/
theorem exp_two_mul_rapidity_add_of_realPhoton (hk : 0 < k) (hE0 : 0 < E) :
    exp (2 * (q + P).rapidity n) =
      (2 * k + E - √(E ^ 2 - M ^ 2)) / (E + √(E ^ 2 - M ^ 2)) := by
  obtain ⟨h0, hs⟩ := components_add_target hq hq' hP hP'
  have hpar : ⟪(q + P).spatialPart, n⟫_ℝ = k - √(E ^ 2 - M ^ 2) := by
    rw [hs, real_inner_smul_left, real_inner_self_eq_norm_sq, hn, one_pow, mul_one]
  rw [exp_two_mul_rapidity (by rw [hpar]; exact abs_sub_sqrt_lt_timeComponent_add hq hP hk hE0),
    hpar, h0]
  ring_nf

/-- **The rapidity is fixed by the invariant mass.** At fixed target, the light-cone component
`E + p` of the target is `W e^{-y}`, where `W` and `y` are the invariant mass and the rapidity of
the photon–target system; so `W` and `y` determine each other. -/
theorem add_sqrt_eq_sqrt_mul_exp_neg_rapidity (hk : 0 < k) (hE0 : 0 < E) :
    E + √(E ^ 2 - M ^ 2) = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  obtain ⟨h0, hs⟩ := components_add_target hq hq' hP hP'
  have := timeComponent_sub_eq_sqrt_mul_exp_neg_rapidity hn hs
    (abs_sub_sqrt_lt_timeComponent_add hq hP hk hE0)
  rw [h0] at this
  linear_combination this

/-- **The photon energy from the invariant mass and the rapidity.** A real photon of energy `k`
and a target of mass `M` form a system of invariant mass `W` and rapidity `y` with
`2 k = e^{y} (W² - M²) / W`. -/
theorem two_mul_energy_eq_exp_rapidity_mul (hE : |M| ≤ E) (hk : 0 < k) (hE0 : 0 < E) :
    2 * k = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - M ^ 2) / √⟪q + P, q + P⟫ₘ := by
  have hB := add_sqrt_eq_sqrt_mul_exp_neg_rapidity hn hq hq' hP hP' hk hE0
  have hW := minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP' hE
  have hBpos : 0 < E + √(E ^ 2 - M ^ 2) := by positivity
  have hWpos : 0 < √⟪q + P, q + P⟫ₘ :=
    Real.sqrt_pos.2 (by rw [hW]; positivity)
  have hexp : exp ((q + P).rapidity n) * exp (-(q + P).rapidity n) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  rw [eq_div_iff hWpos.ne']
  linear_combination (-exp ((q + P).rapidity n)) * hW - 2 * k * exp ((q + P).rapidity n) * hB -
    2 * k * √⟪q + P, q + P⟫ₘ * hexp

end RealPhoton

/-! ### The energy fraction -/

section EnergyFraction

variable {s : ChargedSource} {γ : PhotonKinematics} (hn : ‖n‖ = 1) (hE : |M| ≤ E)
  (hq : q.timeComponent = γ.energy) (hq' : q.spatialPart = γ.energy • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -√(E ^ 2 - M ^ 2) • n)
include hn hE hq hq' hP hP'

/-- **The invariant mass from the energy fraction.** A real photon carrying the fraction `x` of
the energy `E_s ≠ 0` of its source forms with the target a system of invariant mass
`W² = M² + 2 x E_s (E + p)`. -/
theorem minkowskiProduct_add_self_eq_energyFraction (hs : s.energy ≠ 0) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 + 2 * γ.energyFraction s * s.energy * (E + √(E ^ 2 - M ^ 2)) := by
  rw [minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP' hE,
    PhotonKinematics.energyFraction_def]
  field_simp

/-- **The energy fraction from the invariant mass and the rapidity.** A real photon carrying the
fraction `x` of the energy `E_s` of its source forms with the target a system of invariant mass
`W` and rapidity `y` with `x = e^{y} (W² - M²) / (2 W E_s)`. -/
theorem energyFraction_eq_exp_rapidity_mul (hk : 0 < γ.energy) (hE0 : 0 < E) :
    γ.energyFraction s = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - M ^ 2) /
      (2 * √⟪q + P, q + P⟫ₘ * s.energy) := by
  rw [PhotonKinematics.energyFraction_def, mul_comm 2, mul_assoc, ← div_div,
    ← two_mul_energy_eq_exp_rapidity_mul hn hq hq' hP hP' hE hk hE0]
  ring

end EnergyFraction

/-! ### A massless target -/

/-- A massless target of energy `E ≥ 0` has momentum `E`. -/
private theorem spatialPart_eq_of_massless (hP' : P.spatialPart = -E • n) (hE0 : 0 ≤ E) :
    P.spatialPart = -√(E ^ 2 - 0 ^ 2) • n := by
  rw [hP', zero_pow two_ne_zero, sub_zero, Real.sqrt_sq hE0]

section Massless

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -E • n)
include hn hq hq' hP hP'

/-- **A real photon and a massless target, invariant mass.** `W² = 4 k E`. -/
theorem minkowskiProduct_add_self_of_masslessTarget (hE0 : 0 ≤ E) :
    ⟪q + P, q + P⟫ₘ = 4 * k * E := by
  rw [minkowskiProduct_add_self_of_realPhoton (M := 0) hn hq hq' hP
    (spatialPart_eq_of_massless hP' hE0) (by rwa [abs_zero]), zero_pow two_ne_zero, sub_zero,
    Real.sqrt_sq hE0]
  ring

/-- **A real photon and a massless target, photon energy.** `k = (W / 2) e^{y}`. -/
theorem two_mul_energy_eq_sqrt_mul_exp_rapidity_of_masslessTarget (hk : 0 < k) (hE0 : 0 < E) :
    2 * k = √⟪q + P, q + P⟫ₘ * exp ((q + P).rapidity n) := by
  have h := two_mul_energy_eq_exp_rapidity_mul hn hq hq' hP (spatialPart_eq_of_massless hP' hE0.le)
    (by rw [abs_zero]; exact hE0.le) hk hE0
  have hW := minkowskiProduct_add_self_of_masslessTarget hn hq hq' hP hP' hE0.le
  have hWpos : 0 < √⟪q + P, q + P⟫ₘ := Real.sqrt_pos.2 (by rw [hW]; positivity)
  have hsq : ⟪q + P, q + P⟫ₘ = √⟪q + P, q + P⟫ₘ ^ 2 :=
    (Real.sq_sqrt (by rw [hW]; positivity)).symm
  set w := √⟪q + P, q + P⟫ₘ
  rw [h, zero_pow two_ne_zero, sub_zero, hsq]
  field_simp

/-- **A real photon and a massless target, target energy.** `E = (W / 2) e^{-y}`. -/
theorem two_mul_eq_sqrt_mul_exp_neg_rapidity_of_masslessTarget (hk : 0 < k) (hE0 : 0 < E) :
    2 * E = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  have h := add_sqrt_eq_sqrt_mul_exp_neg_rapidity hn hq hq' hP
    (spatialPart_eq_of_massless hP' hE0.le) hk hE0
  rwa [zero_pow two_ne_zero, sub_zero, Real.sqrt_sq hE0.le, ← two_mul] at h

end Massless

end Kinematics
end Photoproduction
end Scattering
end QFT
end EpsilonEridani
