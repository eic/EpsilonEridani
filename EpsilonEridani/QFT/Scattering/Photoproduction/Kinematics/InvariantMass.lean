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
* For a photon of energy `k` and momentum `a` along the beam axis, of any virtuality, the system's
  rapidity obeys `e^{2y} = (k + a + E - p) / (k - a + E + p)`
  (`exp_two_mul_rapidity_of_collinearPhoton`) and its light-cone components along the beam axis
  are `k + a + E - p = W e^{y}` and `k - a + E + p = W e^{-y}`
  (`photonEnergy_add_photonMomentum_add_targetEnergy_sub_momentum_eq_sqrt_mul_exp_rapidity`,
  `photonEnergy_sub_photonMomentum_add_targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity`),
  where `W > 0` (`sqrt_minkowskiProduct_add_self_pos_of_collinearPhoton`).
* For a real photon, `a = k`, `W² = M² + 2 k (E + p)` (`minkowskiProduct_add_self_of_realPhoton`),
  `e^{2y} = (2 k + E - p) / (E + p)` (`exp_two_mul_rapidity_of_realPhoton`) and
  `E + p = W e^{-y}` (`targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity`), so that `W` and
  `y` determine each other at fixed target. Conversely `2 k = e^{y} (W² - M²) / W`
  (`two_mul_photonEnergy_eq_exp_rapidity_mul_sub_div_sqrt`).
* For a photon `γ : PhotonKinematics` of four-momentum `q` with `q⁰ = γ.energy` and virtuality
  `-q²`, in terms of its energy fraction, `W² = M² - Q² + 2 (x E_s E + p q_∥)`
  (`minkowskiProduct_add_self_of_target_energyFraction`). Along the beam axis, with `q_∥ = a`,
  `W² = M² - Q² + 2 (x E_s E + p a)` (`minkowskiProduct_add_self_of_collinearPhoton_energyFraction`)
  and `e^{2y} = (x E_s + a + E - p) / (x E_s - a + E + p)`
  (`exp_two_mul_rapidity_of_collinearPhoton_energyFraction`). For a real photon these read
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

variable {d : ℕ} {q P : Lorentz.Vector d} {n : EuclideanSpace ℝ (Fin d)} {M E p k a : ℝ}

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

/-- The system of a photon of energy `k > 0` along the beam axis and a target of energy `E` and
momentum `-E < p ≤ E` against it lies inside the forward light cone along the beam axis:
`|k - p| < k + E`. -/
private theorem abs_sub_lt_add (hk : 0 < k) (hp : -E < p) (hpE : p ≤ E) : |k - p| < k + E := by
  rw [abs_lt]
  constructor <;> linarith

section CollinearPhoton

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = a • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n)
include hn hq hq' hP hP'

/-- **The rapidity of a photon along the beam axis and a target.** The system of a photon of
energy `k` and momentum `a` along the unit beam axis, of any virtuality, and a target of energy `E`
and momentum `p` against it, inside the forward light cone `|a - p| < k + E`, has rapidity `y`
along the beam axis with `e^{2y} = (k + a + E - p) / (k - a + E + p)`. -/
theorem exp_two_mul_rapidity_of_collinearPhoton (h : |a - p| < k + E) :
    exp (2 * (q + P).rapidity n) = (k + a + E - p) / (k - a + E + p) := by
  have hpar := inner_spatialPart_eq_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_smul_of_spatialPart_eq_smul hq' hP')
  rw [exp_two_mul_rapidity (by rw [hpar, timeComponent_add, hq, hP]; exact h), hpar,
    timeComponent_add, hq, hP]
  congr 1 <;> ring

/-- **The forward light-cone component from the invariant mass and the rapidity.** For a photon
of energy `k` and momentum `a` along the beam axis and a target of energy `E` and momentum `p`
against it, with `|a - p| < k + E`, the light-cone component `k + a + E - p` of the system along
the beam axis is `W e^{y}`, where `W` and `y` are its invariant mass and rapidity. -/
theorem photonEnergy_add_photonMomentum_add_targetEnergy_sub_momentum_eq_sqrt_mul_exp_rapidity
    (h : |a - p| < k + E) : k + a + E - p = √⟪q + P, q + P⟫ₘ * exp ((q + P).rapidity n) := by
  have := timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_smul_of_spatialPart_eq_smul hq' hP')
    (by rw [timeComponent_add, hq, hP]; exact h)
  rw [timeComponent_add, hq, hP] at this
  linear_combination this

/-- **The backward light-cone component from the invariant mass and the rapidity.** For a photon
of energy `k` and momentum `a` along the beam axis and a target of energy `E` and momentum `p`
against it, with `|a - p| < k + E`, the light-cone component `k - a + E + p` of the system along
the beam axis is `W e^{-y}`, where `W` and `y` are its invariant mass and rapidity. -/
theorem photonEnergy_sub_photonMomentum_add_targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity
    (h : |a - p| < k + E) :
    k - a + E + p = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  have := timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    hn (spatialPart_add_eq_smul_of_spatialPart_eq_smul hq' hP')
    (by rw [timeComponent_add, hq, hP]; exact h)
  rw [timeComponent_add, hq, hP] at this
  linear_combination this

/-- **The invariant mass is positive.** A photon of energy `k` and momentum `a` along the beam axis
and a target of energy `E` and momentum `p` against it, with `|a - p| < k + E`, form a system of
invariant mass `W > 0`. -/
theorem sqrt_minkowskiProduct_add_self_pos_of_collinearPhoton (h : |a - p| < k + E) :
    0 < √⟪q + P, q + P⟫ₘ :=
  sqrt_minkowskiProduct_self_pos_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_smul_of_spatialPart_eq_smul hq' hP')
    (by rw [timeComponent_add, hq, hP]; exact h)

end CollinearPhoton

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
  rw [exp_two_mul_rapidity_of_collinearPhoton hn hq hq' hP hP' (abs_sub_lt_add hk hp hpE)]
  congr 1 <;> ring

/-- **The rapidity is fixed by the invariant mass.** At fixed target, the light-cone component
`E + p` of the target is `W e^{-y}`, where `W` and `y` are the invariant mass and the rapidity of
the photon–target system; so `W` and `y` determine each other. -/
theorem targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity (hk : 0 < k) (hp : -E < p)
    (hpE : p ≤ E) :
    E + p = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  have h :=
    photonEnergy_sub_photonMomentum_add_targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity hn
      hq hq' hP hP' (abs_sub_lt_add hk hp hpE)
  linear_combination h

/-- **The photon energy from the invariant mass and the rapidity.** A real photon of energy `k`
and a target of mass `M` form a system of invariant mass `W` and rapidity `y` with
`2 k = e^{y} (W² - M²) / W`. -/
theorem two_mul_photonEnergy_eq_exp_rapidity_mul_sub_div_sqrt (hM : ⟪P, P⟫ₘ = M ^ 2) (hk : 0 < k)
    (hp : -E < p) (hpE : p ≤ E) :
    2 * k = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - M ^ 2) / √⟪q + P, q + P⟫ₘ := by
  have hW := minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP' hM
  have hB := targetEnergy_add_momentum_eq_sqrt_mul_exp_neg_rapidity hn hq hq' hP hP' hk hp hpE
  have he : exp ((q + P).rapidity n) * exp (-(q + P).rapidity n) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  rw [eq_div_iff (sqrt_minkowskiProduct_add_self_pos_of_collinearPhoton hn hq hq' hP hP'
    (abs_sub_lt_add hk hp hpE)).ne']
  -- `e^{y} (W² - M²) = 2 k e^{y} (E + p) = 2 k W e^{y} e^{-y} = 2 k W`
  linear_combination (-exp ((q + P).rapidity n)) * hW - 2 * k * exp ((q + P).rapidity n) * hB -
    2 * k * √⟪q + P, q + P⟫ₘ * he

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
  rw [minkowskiProduct_add_self_of_target hP hP' hM, hγ, hq, γ.energyFraction_mul_energy hs]
  ring

include hn in
/-- **The invariant mass from the energy fraction, along the beam axis.** A photon `γ` of
four-momentum `q` with momentum `a` along the beam axis and virtuality `Q² = -q²`, carrying the
fraction `x` of the energy `E_s ≠ 0` of the source `s`, forms with the target a system of
invariant mass `W² = M² - Q² + 2 (x E_s E + p a)`. -/
theorem minkowskiProduct_add_self_of_collinearPhoton_energyFraction
    (hq' : q.spatialPart = a • n) (hγ : γ.virtuality = -⟪q, q⟫ₘ) (hs : s.energy ≠ 0) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 - γ.virtuality +
      2 * (γ.energyFraction s * s.energy * E + p * a) := by
  rw [minkowskiProduct_add_self_of_target_energyFraction hq hP hP' hM hγ hs,
    inner_spatialPart_eq_of_spatialPart_eq_smul hn hq']

include hn in
/-- **The invariant mass from the energy fraction, real photon.** A real photon `γ` of
four-momentum `q` along the beam axis carrying the fraction `x` of the energy `E_s ≠ 0` of the
source `s` forms with the target a system of invariant mass `W² = M² + 2 x E_s (E + p)`. -/
theorem minkowskiProduct_add_self_of_realPhoton_energyFraction
    (hq' : q.spatialPart = γ.energy • n) (hs : s.energy ≠ 0) :
    ⟪q + P, q + P⟫ₘ = M ^ 2 + 2 * γ.energyFraction s * s.energy * (E + p) := by
  rw [minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP' hM,
    ← γ.energyFraction_mul_energy hs]
  ring

include hn in
omit hM in
/-- **The rapidity from the energy fraction.** A photon `γ` of four-momentum `q` with momentum `a`
along the beam axis, of any virtuality, carrying the fraction `x` of the energy `E_s ≠ 0` of the
source `s`, forms with the target, inside the forward light cone `|a - p| < x E_s + E`, a system of
rapidity `y` along the beam axis with `e^{2y} = (x E_s + a + E - p) / (x E_s - a + E + p)`. -/
theorem exp_two_mul_rapidity_of_collinearPhoton_energyFraction (hq' : q.spatialPart = a • n)
    (hs : s.energy ≠ 0) (h : |a - p| < γ.energyFraction s * s.energy + E) :
    exp (2 * (q + P).rapidity n) = (γ.energyFraction s * s.energy + a + E - p) /
      (γ.energyFraction s * s.energy - a + E + p) := by
  rw [γ.energyFraction_mul_energy hs] at h ⊢
  exact exp_two_mul_rapidity_of_collinearPhoton hn hq hq' hP hP' h

include hn in
omit hM in
/-- **The rapidity from the energy fraction, real photon.** A real photon `γ` of four-momentum `q`
along the beam axis carrying the fraction `x` of the energy `E_s ≠ 0` of the source `s` forms with
the target a system of rapidity `y` along the beam axis with
`e^{2y} = (2 x E_s + E - p) / (E + p)`. -/
theorem exp_two_mul_rapidity_of_realPhoton_energyFraction (hq' : q.spatialPart = γ.energy • n)
    (hs : s.energy ≠ 0) (hk : 0 < γ.energy) (hp : -E < p) (hpE : p ≤ E) :
    exp (2 * (q + P).rapidity n) = (2 * γ.energyFraction s * s.energy + E - p) / (E + p) := by
  rw [exp_two_mul_rapidity_of_realPhoton hn hq hq' hP hP' hk hp hpE,
    ← γ.energyFraction_mul_energy hs]
  ring

include hn in
/-- **The energy fraction from the invariant mass and the rapidity.** A real photon `γ` of
four-momentum `q` along the beam axis carrying the fraction `x` of the energy `E_s` of the source
`s` forms with the target a system of invariant mass `W` and rapidity `y` with
`x = e^{y} (W² - M²) / (2 W E_s)`. -/
theorem energyFraction_eq_exp_rapidity_mul_sub_div_sqrt (hq' : q.spatialPart = γ.energy • n)
    (hk : 0 < γ.energy) (hp : -E < p) (hpE : p ≤ E) :
    γ.energyFraction s = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - M ^ 2) /
      (2 * √⟪q + P, q + P⟫ₘ * s.energy) := by
  have h := two_mul_photonEnergy_eq_exp_rapidity_mul_sub_div_sqrt hn hq hq' hP hP' hM hk hp hpE
  rw [PhotonKinematics.energyFraction_def]
  linear_combination h / (2 * s.energy)

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
  have h := photonEnergy_add_photonMomentum_add_targetEnergy_sub_momentum_eq_sqrt_mul_exp_rapidity
    hn hq hq' hP hP' (abs_sub_lt_add hk (by linarith) le_rfl)
  rwa [add_sub_cancel_right, ← two_mul] at h

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
