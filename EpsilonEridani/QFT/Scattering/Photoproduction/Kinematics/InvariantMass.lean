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
quantities rather than by convention. The target has momentum `p` against the beam axis, so that
`M² = E² - p²`.
* For any photon four-momentum `q`, of any virtuality and direction,
  `W² = M² + q² + 2 (q⁰ E + p q_∥)` (`minkowskiProduct_add_self_of_target`), so the virtuality
  `Q² = -q²` enters `W²` explicitly.
* For a real photon of energy `k` along the beam axis, `W² = M² + 2 k (E + p)`
  (`minkowskiProduct_add_self_of_realPhoton`).
* The system's rapidity obeys `e^{2y} = (2 k + E - p) / (E + p)`
  (`exp_two_mul_rapidity_of_realPhoton`), `2 k + E - p = W e^{y}`
  (`two_mul_photonEnergy_add_targetEnergy_sub_momentum_eq_sqrt_mul_exp_rapidity`) and
  `E + p = W e^{-y}` (`targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity`), so that `W` and
  `y` determine each other at fixed target.
* Conversely `2 k = e^{y} (W² - M²) / W` (`two_mul_photonEnergy_eq_exp_rapidity_mul_sub_div_sqrt`),
  where `W > 0` (`sqrt_minkowskiProduct_add_self_pos`).
* For a photon `γ : PhotonKinematics` of four-momentum `q` with `q⁰ = γ.energy` and virtuality
  `-q²`, in terms of its energy fraction, `W² = M² - Q² + 2 (x E_s E + p q_∥)`
  (`minkowskiProduct_add_self_of_target_energyFraction`). Along the beam axis `q` is null
  (`Lorentz.Vector.minkowskiProduct_self_eq_zero_of_timeComponent_eq_of_spatialPart_eq_smul`), and
  `W² = M² + 2 x E_s (E + p)` (`minkowskiProduct_add_self_of_realPhoton_energyFraction`),
  `e^{2y} = (2 x E_s + E - p) / (E + p)` (`exp_two_mul_rapidity_of_realPhoton_energyFraction`)
  and `x = e^{y} (W² - M²) / (2 W E_s)` (`energyFraction_eq_exp_rapidity_mul_sub_div_sqrt`).

For a massless target these reduce to the familiar `W² = 4 k E`, `e^{2y} = k / E`,
`k = (W / 2) e^{y}` and `E = (W / 2) e^{-y}` (`minkowskiProduct_add_self_of_masslessTarget`,
`exp_two_mul_rapidity_of_masslessTarget`,
`two_mul_photonEnergy_eq_sqrt_mul_exp_rapidity_of_masslessTarget`,
`two_mul_targetEnergy_eq_sqrt_mul_exp_neg_rapidity_of_masslessTarget`).
With a massive target the relations stay exact; only their form changes.

## References

* G. Baur, K. Hencken, D. Trautmann, S. Sadovsky and Y. Kharlov, *Coherent γγ and γA interactions
  in very peripheral collisions at relativistic ion colliders*, Phys. Rep. **364** (2002) 359,
  section 2.
* A. J. Baltz et al., *The physics of ultraperipheral collisions at the LHC*, Phys. Rep. **458**
  (2008) 1, section 2, where `W² = 4 k E` and `k = (W / 2) e^{y}` are used (the reference writes
  the invariant mass of the produced system, here `W`, as `M`).
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

variable {d : ℕ} {q P : Lorentz.Vector d} {n : EuclideanSpace ℝ (Fin d)} {M E p k : ℝ}

/-! ### The invariant mass of a photon and a target -/

/-- **The invariant mass of a photon and a target.** For a target of mass `M`, energy `E` and
momentum `p` against the beam axis `n` and any photon four-momentum `q`, the photon–target
system has `W² = M² + q² + 2 (q⁰ E + p q_∥)`, with `q_∥ = ⟪q.spatialPart, n⟫`; the virtuality
`Q² = -q²` of the photon lowers `W²`. -/
theorem minkowskiProduct_add_self_of_target (hP : P.timeComponent = E)
    (hP' : P.spatialPart = -p • n) (hM : ⟪P, P⟫ₘ = M ^ 2) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 + ⟪q, q⟫ₘ + 2 * (q.timeComponent * E + p * ⟪q.spatialPart, n⟫_ℝ) := by
  have hqP : ⟪q, P⟫ₘ = q.timeComponent * E + p * ⟪q.spatialPart, n⟫_ℝ := by
    rw [minkowskiProduct_eq_timeComponent_spatialPart, hP, hP', real_inner_smul_right]
    ring
  rw [minkowskiProduct_add_self, hM, hqP]
  ring

/-- The photon–target system of a photon of energy `k` along the beam axis and a target of energy
`E` and momentum `p` against it has energy `k + E` and spatial part `(k - p) • n`. -/
private theorem components_add_target (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
    (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n) :
    (q + P).timeComponent = k + E ∧ (q + P).spatialPart = (k - p) • n := by
  refine ⟨by simp [hq, hP], ?_⟩
  rw [spatialPart_add, hq', hP', sub_smul, _root_.neg_smul, ← sub_eq_add_neg]

/-- The system of a photon of energy `k > 0` along the beam axis and a target of energy `E` and
momentum `-E < p ≤ E` against it lies inside the forward light cone along the beam axis:
`|k - p| < k + E`. -/
private theorem abs_sub_lt_add (hk : 0 < k) (hp : -E < p) (hpE : p ≤ E) : |k - p| < k + E := by
  rw [abs_lt]
  constructor <;> linarith

section RealPhoton

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n)
include hn hq hq' hP hP'

/-- **The invariant mass of a real photon and a target.** A real photon of energy `k` along the
unit beam axis and a target of mass `M`, energy `E` and momentum `p` against it form a system of
invariant mass `W² = M² + 2 k (E + p)`. -/
theorem minkowskiProduct_add_self_of_realPhoton (hM : ⟪P, P⟫ₘ = M ^ 2) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 + 2 * k * (E + p) := by
  rw [minkowskiProduct_add_self_of_target hP hP' hM,
    minkowskiProduct_self_eq_zero_of_timeComponent_eq_of_spatialPart_eq_smul hn hq hq', hq,
    inner_spatialPart_eq_of_spatialPart_eq_smul hn hq']
  ring

/-- **The rapidity of a real photon and a target.** The photon–target system of a real photon of
energy `k` and a target of energy `E` and momentum `p` has rapidity `y` along the photon direction
with `e^{2y} = (2 k + E - p) / (E + p)`. -/
theorem exp_two_mul_rapidity_of_realPhoton (hk : 0 < k) (hp : -E < p) (hpE : p ≤ E) :
    exp (2 * (q + P).rapidity n) = (2 * k + E - p) / (E + p) := by
  obtain ⟨h0, hs⟩ := components_add_target hq hq' hP hP'
  have hpar := inner_spatialPart_eq_of_spatialPart_eq_smul hn hs
  rw [exp_two_mul_rapidity (by rw [hpar, h0]; exact abs_sub_lt_add hk hp hpE), hpar, h0]
  ring_nf

/-- **The forward light-cone component from the invariant mass and the rapidity.** The light-cone
component `2 k + E - p` of the photon–target system along the photon direction is `W e^{y}`, where
`W` and `y` are the invariant mass and the rapidity of the system. -/
theorem two_mul_photonEnergy_add_targetEnergy_sub_momentum_eq_sqrt_mul_exp_rapidity (hk : 0 < k)
    (hp : -E < p) (hpE : p ≤ E) :
    2 * k + E - p = √⟪q + P, q + P⟫ₘ * exp ((q + P).rapidity n) := by
  obtain ⟨h0, hs⟩ := components_add_target hq hq' hP hP'
  have :=
    timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul hn hs
      (by rw [h0]; exact abs_sub_lt_add hk hp hpE)
  rw [h0] at this
  linear_combination this

/-- **The rapidity is fixed by the invariant mass.** At fixed target, the light-cone component
`E + p` of the target is `W e^{-y}`, where `W` and `y` are the invariant mass and the rapidity of
the photon–target system; so `W` and `y` determine each other. -/
theorem targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity (hk : 0 < k) (hp : -E < p)
    (hpE : p ≤ E) :
    E + p = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  obtain ⟨h0, hs⟩ := components_add_target hq hq' hP hP'
  have :=
    timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul hn hs
      (by rw [h0]; exact abs_sub_lt_add hk hp hpE)
  rw [h0] at this
  linear_combination this

/-- The target light-cone component `E + p = W e^{-y}`, rescaled by `e^{y}`, is the invariant
mass `W`. -/
private theorem exp_rapidity_mul_targetEnergy_add_momentum (hk : 0 < k) (hp : -E < p)
    (hpE : p ≤ E) :
    exp ((q + P).rapidity n) * (E + p) = √⟪q + P, q + P⟫ₘ := by
  rw [targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity hn hq hq' hP hP' hk hp hpE, exp_neg,
    mul_left_comm, mul_inv_cancel₀ (exp_pos _).ne', mul_one]

/-- **The invariant mass is positive.** A real photon of energy `k > 0` and a target of energy `E`
and momentum `-E < p ≤ E` form a system of invariant mass `W > 0`. -/
theorem sqrt_minkowskiProduct_add_self_pos (hk : 0 < k) (hp : -E < p) (hpE : p ≤ E) :
    0 < √⟪q + P, q + P⟫ₘ :=
  exp_rapidity_mul_targetEnergy_add_momentum hn hq hq' hP hP' hk hp hpE ▸
    mul_pos (exp_pos _) (by linarith)

/-- **The photon energy from the invariant mass and the rapidity.** A real photon of energy `k`
and a target of mass `M` form a system of invariant mass `W` and rapidity `y` with
`2 k = e^{y} (W² - M²) / W`. -/
theorem two_mul_photonEnergy_eq_exp_rapidity_mul_sub_div_sqrt (hM : ⟪P, P⟫ₘ = M ^ 2) (hk : 0 < k)
    (hp : -E < p) (hpE : p ≤ E) :
    2 * k = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - M ^ 2) / √⟪q + P, q + P⟫ₘ := by
  have hW := minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP' hM
  have hB := exp_rapidity_mul_targetEnergy_add_momentum hn hq hq' hP hP' hk hp hpE
  rw [eq_div_iff (sqrt_minkowskiProduct_add_self_pos hn hq hq' hP hP' hk hp hpE).ne']
  -- `e^{y} (W² - M²) = 2 k e^{y} (E + p) = 2 k W`
  linear_combination (-exp ((q + P).rapidity n)) * hW - 2 * k * hB

end RealPhoton

/-! ### The energy fraction -/

section EnergyFraction

/-! In this section the photon `γ` has four-momentum `q`, with `q⁰ = γ.energy`. -/

variable {s : ChargedSource} {γ : PhotonKinematics} (hn : ‖n‖ = 1)
  (hq : q.timeComponent = γ.energy)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n) (hM : ⟪P, P⟫ₘ = M ^ 2)
include hq hP hP' hM

/-- **The invariant mass from the energy fraction and the virtuality.** A photon `γ` of
four-momentum `q` and virtuality `Q² = -q²` carrying the fraction `x` of the energy `E_s ≠ 0` of
the source `s` forms with the target a system of invariant mass
`W² = M² - Q² + 2 (x E_s E + p q_∥)`. -/
theorem minkowskiProduct_add_self_of_target_energyFraction (hγ : γ.virtuality = -⟪q, q⟫ₘ)
    (hs : s.energy ≠ 0) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 - γ.virtuality +
      2 * (γ.energyFraction s * s.energy * E + p * ⟪q.spatialPart, n⟫_ℝ) := by
  rw [minkowskiProduct_add_self_of_target hP hP' hM, hγ, hq,
    PhotonKinematics.energyFraction_def, div_mul_cancel₀ _ hs]
  ring

include hn in
/-- **The invariant mass from the energy fraction, along the beam axis.** A photon `γ` of
four-momentum `q` along the beam axis carrying the fraction `x` of the energy `E_s ≠ 0` of the
source `s` forms with the target a system of invariant mass `W² = M² + 2 x E_s (E + p)`. -/
theorem minkowskiProduct_add_self_of_realPhoton_energyFraction
    (hq' : q.spatialPart = γ.energy • n) (hs : s.energy ≠ 0) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 + 2 * γ.energyFraction s * s.energy * (E + p) := by
  rw [mul_assoc 2, PhotonKinematics.energyFraction_def, div_mul_cancel₀ _ hs]
  exact minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP' hM

include hn in
omit hM in
/-- **The rapidity from the energy fraction.** A photon `γ` of four-momentum `q` along the beam
axis carrying the fraction `x` of the energy `E_s ≠ 0` of the source `s` forms with the target a
system of rapidity `y` along the beam axis with `e^{2y} = (2 x E_s + E - p) / (E + p)`. -/
theorem exp_two_mul_rapidity_of_realPhoton_energyFraction (hq' : q.spatialPart = γ.energy • n)
    (hs : s.energy ≠ 0) (hk : 0 < γ.energy) (hp : -E < p) (hpE : p ≤ E) :
    exp (2 * (q + P).rapidity n) = (2 * γ.energyFraction s * s.energy + E - p) / (E + p) := by
  rw [mul_assoc 2, PhotonKinematics.energyFraction_def, div_mul_cancel₀ _ hs]
  exact exp_two_mul_rapidity_of_realPhoton hn hq hq' hP hP' hk hp hpE

include hn in
/-- **The energy fraction from the invariant mass and the rapidity.** A photon `γ` of
four-momentum `q` along the beam axis carrying the fraction `x` of the energy `E_s` of the source
`s` forms with the target a system of invariant mass `W` and rapidity `y` with
`x = e^{y} (W² - M²) / (2 W E_s)`. -/
theorem energyFraction_eq_exp_rapidity_mul_sub_div_sqrt (hq' : q.spatialPart = γ.energy • n)
    (hk : 0 < γ.energy) (hp : -E < p) (hpE : p ≤ E) :
    γ.energyFraction s = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - M ^ 2) /
      (2 * √⟪q + P, q + P⟫ₘ * s.energy) := by
  rw [PhotonKinematics.energyFraction_def, mul_assoc 2, mul_left_comm 2, ← div_div,
    ← two_mul_photonEnergy_eq_exp_rapidity_mul_sub_div_sqrt hn hq hq' hP hP' hM hk hp hpE,
    mul_div_mul_left _ _ two_ne_zero]

end EnergyFraction

/-! ### A massless target -/

section Massless

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -E • n)
include hn hq hq' hP hP'

/-- **A real photon and a massless target, invariant mass.** `W² = 4 k E`. -/
theorem minkowskiProduct_add_self_of_masslessTarget : ⟪q + P, q + P⟫ₘ = 4 * k * E := by
  rw [minkowskiProduct_add_self_of_realPhoton (M := 0) hn hq hq' hP hP' (by
    rw [minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul hn hP', hP]; ring)]
  ring

/-- **A real photon and a massless target, rapidity.** `e^{2y} = k / E`. -/
theorem exp_two_mul_rapidity_of_masslessTarget (hk : 0 < k) (hE0 : 0 < E) :
    exp (2 * (q + P).rapidity n) = k / E := by
  rw [exp_two_mul_rapidity_of_realPhoton hn hq hq' hP hP' hk (by linarith) le_rfl,
    add_sub_cancel_right, ← two_mul, mul_div_mul_left _ _ two_ne_zero]

/-- **A real photon and a massless target, photon energy.** `k = (W / 2) e^{y}`. -/
theorem two_mul_photonEnergy_eq_sqrt_mul_exp_rapidity_of_masslessTarget (hk : 0 < k) (hE0 : 0 < E) :
    2 * k = √⟪q + P, q + P⟫ₘ * exp ((q + P).rapidity n) := by
  have h := two_mul_photonEnergy_add_targetEnergy_sub_momentum_eq_sqrt_mul_exp_rapidity hn hq hq' hP
    hP' hk (by linarith) le_rfl
  rwa [add_sub_cancel_right] at h

/-- **A real photon and a massless target, target energy.** `E = (W / 2) e^{-y}`. -/
theorem two_mul_targetEnergy_eq_sqrt_mul_exp_neg_rapidity_of_masslessTarget (hk : 0 < k)
    (hE0 : 0 < E) :
    2 * E = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  have h := targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity hn hq hq' hP hP' hk
    (by linarith) le_rfl
  rwa [← two_mul] at h

end Massless

end Kinematics
end Photoproduction
end Scattering
end QFT
end EpsilonEridani
