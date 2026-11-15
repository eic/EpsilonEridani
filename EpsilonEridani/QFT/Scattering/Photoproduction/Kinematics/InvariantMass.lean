/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.Photoproduction.Kinematics.Basic
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.Rapidity
public import EpsilonEridani.Mathematics.Algebra.Order.Abs

/-!
# The photon–target system: energy fraction, rapidity and invariant mass

A photon emitted by a charged source meets a target of energy `E` that travels against it along a
unit beam axis `n` (`‖n‖ = 1`). Three variables are used to label the photon:
* its energy fraction `x = k / E_s` relative to the source (`PhotonKinematics.energyFraction`);
* the invariant mass `W` of the photon–target system, `W² = (q + P)²`, which is the energy at
  which the photon–target cross section is evaluated;
* the rapidity `y` of the photon–target system along the beam axis, which is the rapidity of
  whatever the photon and the target produce, and the rapidity the literature attaches to the
  photon when it writes `k = (W / 2) e^{y}`.

This module relates the three by equalities between the four-vector quantities rather than by
convention. The target has momentum `p` against the beam axis, so that its mass `M` has
`M² = P² = E² - p²`. The invariant mass and the rapidity are related at any virtuality; the
energy fraction enters through `k = x E_s`, and is isolated in terms of `W` and `y` by
`x = (W cosh y - E) / E_s`, also at any virtuality.
* For any photon four-momentum `q`, of any virtuality and direction,
  `W² = P² + q² + 2 (q⁰ E + p q_∥)` (`minkowskiProduct_add_self_of_target`), so the virtuality
  `Q² = -q²` enters `W²` explicitly.
* For a photon of energy `k` and momentum `a` along the beam axis, of any virtuality,
  `W² = P² + q² + 2 (k E + p a)` (`minkowskiProduct_add_self_of_collinearPhoton`), which for a
  photon `γ : PhotonKinematics` reads `W² = P² - Q² + 2 (k E + p a)`
  (`PhotonKinematics.minkowskiProduct_add_self_eq_sub_virtuality_of_collinearPhoton`). Inside the
  forward light cone `|a - p| < k + E` (for a real photon, `a = k`, this follows from `0 < k` and
  `-E < p ≤ E` by `abs_sub_lt_add_of_pos_of_neg_lt_of_le`), the system's rapidity obeys
  `e^{2y} = (k + a + E - p) / (k - a + E + p)` (`exp_two_mul_rapidity_add_of_collinearPhoton`), its
  light-cone components along the beam axis are `k + a + E - p = W e^{y}` and
  `k - a + E + p = W e^{-y}`
  (`add_add_sub_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_collinearPhoton`,
  `sub_add_add_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_collinearPhoton`),
  where `W > 0` (`sqrt_minkowskiProduct_add_self_pos_of_collinearPhoton`), and the energy fraction
  is `x = (W cosh y - E) / E_s` (in the `PhotonKinematics` namespace,
`energyFraction_eq_sqrt_minkowskiProduct_add_self_mul_cosh_rapidity_sub_div_of_collinearPhoton`).
* For a real photon, `a = k`, `W² = P² + 2 k (E + p)` (`minkowskiProduct_add_self_of_realPhoton`)
  and, inside the forward light cone `|k - p| < k + E`, `e^{2y} = (2 k + E - p) / (E + p)`
  (`exp_two_mul_rapidity_add_of_realPhoton`) and `E + p = W e^{-y}`
  (`add_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_realPhoton`), so that `W` and
  `y` determine each other at fixed target. Conversely `2 k = e^{y} (W² - P²) / W`
  (`two_mul_eq_exp_rapidity_mul_sub_div_sqrt_minkowskiProduct_add_self_of_realPhoton`), that is
  `x = e^{y} (W² - M²) / (2 W E_s)` by `PhotonKinematics.energyFraction_def`.

The real-photon relations are the collinear ones at `a = k`, where `q² = 0`. No photon in the
physical region `ChargedSource.photonRegion` of a massive source is exactly real
(`ChargedSource.not_isReal_of_mem_photonRegion`), so for such a source it is the collinear forms,
valid at any virtuality, that apply exactly.

For a real photon of energy `k > 0` and a massless target of energy `E > 0` these reduce to the
familiar `W² = 4 k E`, `e^{2y} = k / E`, `k = (W / 2) e^{y}` and `E = (W / 2) e^{-y}`
(`minkowskiProduct_add_self_of_realPhoton_of_masslessTarget`,
`exp_two_mul_rapidity_add_of_realPhoton_of_masslessTarget`,
`two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_realPhoton_of_masslessTarget`,
`two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_realPhoton_of_masslessTarget`).
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

variable {d : ℕ} {q P : Lorentz.Vector d} {n : EuclideanSpace ℝ (Fin d)} {E p k a : ℝ}

/-! ### The invariant mass of a photon and a target -/

/-- **The invariant mass of a photon and a target.** For a target of energy `E` and momentum `p`
against the beam axis `n` and any photon four-momentum `q`, the photon–target system has
`W² = P² + q² + 2 (q⁰ E + p q_∥)`, with `q_∥ = ⟪q.spatialPart, n⟫` and `P² = M²` for a target of
mass `M`; the virtuality `Q² = -q²` of the photon lowers `W²`. The identity holds for any `n`, but
`p` is the target momentum and `q_∥` the component of the photon momentum along the axis only
when `‖n‖ = 1`. -/
theorem minkowskiProduct_add_self_of_target (hP : P.timeComponent = E)
    (hP' : P.spatialPart = -p • n) :
    ⟪q + P, q + P⟫ₘ = ⟪P, P⟫ₘ + ⟪q, q⟫ₘ +
      2 * (q.timeComponent * E + p * ⟪q.spatialPart, n⟫_ℝ) := by
  have hqP : ⟪q, P⟫ₘ = q.timeComponent * E + p * ⟪q.spatialPart, n⟫_ℝ := by
    rw [minkowskiProduct_eq_timeComponent_spatialPart, hP, hP', real_inner_smul_right]
    ring
  rw [minkowskiProduct_add_self, hqP]
  ring

section CollinearPhoton

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = a • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n)
include hn hq hq' hP hP'

/-- **The invariant mass of a photon along the beam axis and a target.** A photon of energy `k`
and momentum `a` along the unit beam axis, of any virtuality, and a target of energy `E` and
momentum `p` against it form a system of invariant mass `W² = P² + q² + 2 (k E + p a)`. -/
theorem minkowskiProduct_add_self_of_collinearPhoton :
    ⟪q + P, q + P⟫ₘ = ⟪P, P⟫ₘ + ⟪q, q⟫ₘ + 2 * (k * E + p * a) := by
  rw [minkowskiProduct_add_self_of_target hP hP', hq,
    inner_spatialPart_eq_of_spatialPart_eq_smul hn hq']

/-- **The rapidity of a photon along the beam axis and a target.** The system of a photon of
energy `k` and momentum `a` along the unit beam axis, of any virtuality, and a target of energy `E`
and momentum `p` against it, inside the forward light cone `|a - p| < k + E`, has rapidity `y`
along the beam axis with `e^{2y} = (k + a + E - p) / (k - a + E + p)`. -/
theorem exp_two_mul_rapidity_add_of_collinearPhoton (h : |a - p| < k + E) :
    exp (2 * (q + P).rapidity n) = (k + a + E - p) / (k - a + E + p) := by
  rw [exp_two_mul_rapidity_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_sub_smul_of_spatialPart_eq_smul hq' hP')
    (by rwa [timeComponent_add_eq_add_of_timeComponent_eq hq hP]),
    timeComponent_add_eq_add_of_timeComponent_eq hq hP]
  congr 1 <;> ring

/-- **The forward light-cone component from the invariant mass and the rapidity.** For a photon
of energy `k` and momentum `a` along the unit beam axis and a target of energy `E` and momentum `p`
against it, with `|a - p| < k + E`, the light-cone component `k + a + E - p` of the system along
the beam axis is `W e^{y}`, where `W` and `y` are its invariant mass and rapidity. -/
theorem add_add_sub_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_collinearPhoton
    (h : |a - p| < k + E) : k + a + E - p = √⟪q + P, q + P⟫ₘ * exp ((q + P).rapidity n) := by
  have := timeComponent_add_eq_sqrt_minkowskiProduct_mul_exp_rapidity_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_sub_smul_of_spatialPart_eq_smul hq' hP')
    (by rwa [timeComponent_add_eq_add_of_timeComponent_eq hq hP])
  rw [timeComponent_add_eq_add_of_timeComponent_eq hq hP] at this
  linear_combination this

/-- **The backward light-cone component from the invariant mass and the rapidity.** For a photon
of energy `k` and momentum `a` along the unit beam axis and a target of energy `E` and momentum `p`
against it, with `|a - p| < k + E`, the light-cone component `k - a + E + p` of the system along
the beam axis is `W e^{-y}`, where `W` and `y` are its invariant mass and rapidity. -/
theorem sub_add_add_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_collinearPhoton
    (h : |a - p| < k + E) : k - a + E + p = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  have := timeComponent_sub_eq_sqrt_minkowskiProduct_mul_exp_neg_rapidity_of_spatialPart_eq_smul
    hn (spatialPart_add_eq_sub_smul_of_spatialPart_eq_smul hq' hP')
    (by rwa [timeComponent_add_eq_add_of_timeComponent_eq hq hP])
  rw [timeComponent_add_eq_add_of_timeComponent_eq hq hP] at this
  linear_combination this

/-- **The invariant mass is positive.** A photon of energy `k` and momentum `a` along the unit
beam axis and a target of energy `E` and momentum `p` against it, with `|a - p| < k + E`, form a
system of invariant mass `W > 0`. -/
theorem sqrt_minkowskiProduct_add_self_pos_of_collinearPhoton (h : |a - p| < k + E) :
    0 < √⟪q + P, q + P⟫ₘ :=
  sqrt_minkowskiProduct_self_pos_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_sub_smul_of_spatialPart_eq_smul hq' hP')
    (by rwa [timeComponent_add_eq_add_of_timeComponent_eq hq hP])

end CollinearPhoton

section RealPhoton

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n)
include hn hq hq' hP hP'

/-- **The invariant mass of a real photon and a target.** A real photon of energy `k` along the
unit beam axis and a target of energy `E` and momentum `p` against it form a system of invariant
mass `W² = P² + 2 k (E + p)`, with `P² = M²` for a target of mass `M`. -/
theorem minkowskiProduct_add_self_of_realPhoton :
    ⟪q + P, q + P⟫ₘ = ⟪P, P⟫ₘ + 2 * k * (E + p) := by
  rw [minkowskiProduct_add_self_of_collinearPhoton hn hq hq' hP hP',
    minkowskiProduct_self_eq_zero_of_timeComponent_eq_of_spatialPart_eq_smul hn hq hq']
  ring

/-- **The rapidity of a real photon and a target.** The system of a real photon of energy `k`
along the unit beam axis and a target of energy `E` and momentum `p` against it, inside the
forward light cone `|k - p| < k + E` (for instance when `0 < k` and `-E < p ≤ E`, by
`abs_sub_lt_add_of_pos_of_neg_lt_of_le`), has rapidity `y` along the beam axis with
`e^{2y} = (2 k + E - p) / (E + p)`. -/
theorem exp_two_mul_rapidity_add_of_realPhoton (h : |k - p| < k + E) :
    exp (2 * (q + P).rapidity n) = (2 * k + E - p) / (E + p) := by
  rw [exp_two_mul_rapidity_add_of_collinearPhoton hn hq hq' hP hP' h]
  congr 1 <;> ring

/-- **The rapidity is fixed by the invariant mass.** For a real photon of energy `k` along the unit
beam axis and a target of energy `E` and momentum `p` against it, inside the forward light cone
`|k - p| < k + E`, the light-cone component `E + p` of the target is `W e^{-y}`, where `W` and `y`
are the invariant mass and the rapidity of the photon–target system; so at fixed target `W` and
`y` determine each other. -/
theorem add_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_realPhoton
    (h : |k - p| < k + E) : E + p = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  have h' := sub_add_add_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_collinearPhoton
    hn hq hq' hP hP' h
  linear_combination h'

/-- **The photon energy from the invariant mass and the rapidity.** A real photon of energy `k`
along the unit beam axis and a target of energy `E` and momentum `p` against it, inside the forward
light cone `|k - p| < k + E`, form a system of invariant mass `W` and rapidity `y` with
`2 k = e^{y} (W² - P²) / W`, where `P² = M²` for a target of mass `M`. -/
theorem two_mul_eq_exp_rapidity_mul_sub_div_sqrt_minkowskiProduct_add_self_of_realPhoton
    (h : |k - p| < k + E) :
    2 * k = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - ⟪P, P⟫ₘ) / √⟪q + P, q + P⟫ₘ := by
  have hW := minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP'
  have hB := add_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_realPhoton hn hq hq' hP
    hP' h
  have he : exp ((q + P).rapidity n) * exp (-(q + P).rapidity n) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  rw [eq_div_iff (sqrt_minkowskiProduct_add_self_pos_of_collinearPhoton hn hq hq' hP hP' h).ne']
  -- `e^{y} (W² - P²) = 2 k e^{y} (E + p) = 2 k W e^{y} e^{-y} = 2 k W`
  linear_combination (-exp ((q + P).rapidity n)) * hW - 2 * k * exp ((q + P).rapidity n) * hB -
    2 * k * √⟪q + P, q + P⟫ₘ * he

end RealPhoton

/-! ### The virtuality and the energy fraction -/

namespace PhotonKinematics

variable {γ : PhotonKinematics} (hn : ‖n‖ = 1) (hq : q.timeComponent = γ.energy)
  (hq' : q.spatialPart = a • n) (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n)
include hn hq hq' hP hP'

/-- **The invariant mass and the virtuality.** A photon `γ` of four-momentum `q`, with
`q⁰ = γ.energy`, virtuality `Q² = -q²` and momentum `a` along the unit beam axis, and a target of
energy `E` and momentum `p` against it form a system of invariant mass
`W² = P² - Q² + 2 (γ.energy E + p a)`. -/
theorem minkowskiProduct_add_self_eq_sub_virtuality_of_collinearPhoton
    (hγ : γ.virtuality = -⟪q, q⟫ₘ) :
    ⟪q + P, q + P⟫ₘ = ⟪P, P⟫ₘ - γ.virtuality + 2 * (γ.energy * E + p * a) := by
  rw [minkowskiProduct_add_self_of_collinearPhoton hn hq hq' hP hP', hγ]
  ring

/-- **The energy fraction from the invariant mass and the rapidity.** A photon `γ` of
four-momentum `q`, with `q⁰ = γ.energy` and momentum `a` along the unit beam axis, of any
virtuality, and a target of energy `E` and momentum `p` against it, inside the forward light cone
`|a - p| < γ.energy + E`, form a system of invariant mass `W` and rapidity `y` with
`x = (W cosh y - E) / E_s`, where `x` is the fraction of the energy `E_s` of the source `s`
carried by the photon. -/
theorem
    energyFraction_eq_sqrt_minkowskiProduct_add_self_mul_cosh_rapidity_sub_div_of_collinearPhoton
    {s : ChargedSource} (h : |a - p| < γ.energy + E) :
    γ.energyFraction s = (√⟪q + P, q + P⟫ₘ * cosh ((q + P).rapidity n) - E) / s.energy := by
  -- the energy of the system is `γ.energy + E = W cosh y`
  have hc := timeComponent_eq_sqrt_minkowskiProduct_mul_cosh_rapidity_of_spatialPart_eq_smul hn
    (spatialPart_add_eq_sub_smul_of_spatialPart_eq_smul hq' hP')
    (by rwa [timeComponent_add_eq_add_of_timeComponent_eq hq hP])
  rw [timeComponent_add_eq_add_of_timeComponent_eq hq hP] at hc
  rw [energyFraction_def, ← hc, add_sub_cancel_right]

end PhotonKinematics

/-! ### A real photon and a massless target -/

section Massless

variable (hn : ‖n‖ = 1) (hq : q.timeComponent = k) (hq' : q.spatialPart = k • n)
  (hP : P.timeComponent = E) (hP' : P.spatialPart = -E • n)
include hn hq hq' hP hP'

/-- **A real photon and a massless target, invariant mass.** A real photon of energy `k` along the
unit beam axis and a massless target of energy `E` against it form a system with `W² = 4 k E`. -/
theorem minkowskiProduct_add_self_of_realPhoton_of_masslessTarget :
    ⟪q + P, q + P⟫ₘ = 4 * k * E := by
  rw [minkowskiProduct_add_self_of_realPhoton hn hq hq' hP hP',
    minkowskiProduct_self_eq_mul_of_spatialPart_eq_smul hn hP', hP]
  ring

/-- **A real photon and a massless target, rapidity.** A real photon of energy `k > 0` along the
unit beam axis and a massless target of energy `E > 0` against it form a system of rapidity `y`
with `e^{2y} = k / E`. -/
theorem exp_two_mul_rapidity_add_of_realPhoton_of_masslessTarget (hk : 0 < k) (hE0 : 0 < E) :
    exp (2 * (q + P).rapidity n) = k / E := by
  rw [exp_two_mul_rapidity_add_of_realPhoton hn hq hq' hP hP'
      (abs_sub_lt_add_of_pos_of_neg_lt_of_le hk (by linarith) le_rfl),
    div_eq_div_iff (by linarith) hE0.ne']
  ring

/-- **A real photon and a massless target, photon energy.** A real photon of energy `k > 0` along
the unit beam axis and a massless target of energy `E > 0` against it form a system of invariant
mass `W` and rapidity `y` with `k = (W / 2) e^{y}`. -/
theorem two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_realPhoton_of_masslessTarget
    (hk : 0 < k) (hE0 : 0 < E) : 2 * k = √⟪q + P, q + P⟫ₘ * exp ((q + P).rapidity n) := by
  have h := add_add_sub_eq_sqrt_minkowskiProduct_add_self_mul_exp_rapidity_of_collinearPhoton hn
    hq hq' hP hP' (abs_sub_lt_add_of_pos_of_neg_lt_of_le hk (by linarith) le_rfl)
  linear_combination h

/-- **A real photon and a massless target, target energy.** A real photon of energy `k > 0` along
the unit beam axis and a massless target of energy `E > 0` against it form a system of invariant
mass `W` and rapidity `y` with `E = (W / 2) e^{-y}`. -/
theorem
    two_mul_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_realPhoton_of_masslessTarget
    (hk : 0 < k) (hE0 : 0 < E) : 2 * E = √⟪q + P, q + P⟫ₘ * exp (-(q + P).rapidity n) := by
  have h := add_eq_sqrt_minkowskiProduct_add_self_mul_exp_neg_rapidity_of_realPhoton hn hq hq' hP
    hP' (abs_sub_lt_add_of_pos_of_neg_lt_of_le hk (by linarith) le_rfl)
  linear_combination h

end Massless

end Kinematics
end Photoproduction
end Scattering
end QFT
end EpsilonEridani
