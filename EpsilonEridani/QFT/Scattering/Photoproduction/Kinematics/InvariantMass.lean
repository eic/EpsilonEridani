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

A photon `γ : PhotonKinematics` of four-momentum `q`, emitted by a charged source `s`, meets a
target of four-momentum `P`, energy `E` and momentum `p` against a unit beam axis `n`
(`‖n‖ = 1`), so that its mass `M` has `M² = P² = E² - p²`. Three variables are used to label the
photon:
* its energy fraction `x = k / E_s` relative to the source (`PhotonKinematics.energyFraction`);
* the invariant mass `W` of the photon–target system, `W² = (q + P)²`, which is the energy at
  which the photon–target cross section is evaluated;
* the rapidity `y = (q + P).rapidity n` of the total photon–target four-momentum along the beam
  axis, which is the rapidity of whatever the photon and the target produce. For a real photon and
  a massless target it is the rapidity of the literature's `k = (W / 2) e^{y}`; for a target of
  mass `M` the factor `(W² - M²) / W²` enters, `k = (W / 2) e^{y} (W² - M²) / W²`.

This module relates the three by equalities between four-vector quantities rather than by
convention.
* For a photon of any virtuality `Q² = γ.virtuality = -q²` and direction,
  `W² = M² - Q² + 2 (k E + p q_∥)`, with `q_∥ = ⟪q.spatialPart, n⟫`
  (`PhotonKinematics.minkowskiProduct_add_self_eq_sub_virtuality`), so the virtuality enters `W²`
  explicitly.
* For a photon of momentum `a` along the beam axis, of any virtuality, with `|a - p| < k + E`, the
  energy fraction is `x = (W cosh y - E) / E_s`
  (`PhotonKinematics.energyFraction_eq_sqrt_minkowskiProduct_add_self_mul_cosh_rapidity_sub_div`).
* A photon of energy `k ≥ 0` and momentum `a` along the beam axis is real exactly when `|a| = k`
  (`PhotonKinematics.isReal_iff_abs_eq_energy_of_spatialPart_eq_smul`, in
  `EpsilonEridani.QFT.Scattering.Photoproduction.Kinematics.Basic`). For a photon null along the
  beam axis, `a = k`,
  `W² = M² + 2 k (E + p)`
  (`PhotonKinematics.minkowskiProduct_add_self_eq_add_two_mul_energy_mul_add`) and, with
  `|k - p| < k + E`, the energy fraction is `x = e^{y} (W² - M²) / (2 W E_s)`
  (`PhotonKinematics.energyFraction_eq_exp_rapidity_mul_sub_div_sqrt_minkowskiProduct_add_self`).
  For a massless target, `M = 0`, this is the familiar `x = W e^{y} / (2 E_s)`, that is
  `k = (W / 2) e^{y}`.

The underlying relations for any system of two four-vectors along an axis, `e^{2y}`,
`W e^{±y}` and `W cosh y`, are stated for Lorentz vectors in
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.Rapidity` and
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions`; for a real
photon against a massless target they give the familiar `W² = 4 k E`, `e^{2y} = k / E`,
`k = (W / 2) e^{y}` and `E = (W / 2) e^{-y}`. With a massive target the relations stay exact; only
their form changes.

No photon in the physical region `ChargedSource.photonRegion` of a massive source is exactly real
(`ChargedSource.not_isReal_of_mem_photonRegion`), so for such a source it is the forms valid at
any virtuality that apply exactly.

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

namespace PhotonKinematics

variable {d : ℕ} {q P : Lorentz.Vector d} {n : EuclideanSpace ℝ (Fin d)} {E p a : ℝ}
  {γ : PhotonKinematics} {s : ChargedSource}

/-- **The invariant mass and the virtuality.** A photon `γ` of four-momentum `q`, with
`q⁰ = γ.energy` and virtuality `Q² = -q²`, and a target of energy `E` and momentum `p` against the
direction `n` form a system of invariant mass `W² = P² - Q² + 2 (γ.energy E + p q_∥)`, with
`q_∥ = ⟪q.spatialPart, n⟫` and `P² = M²` for a target of mass `M`. For a unit vector `n`, `p` is
the target momentum and `q_∥` the photon momentum along `n`. -/
theorem minkowskiProduct_add_self_eq_sub_virtuality (hq : q.timeComponent = γ.energy)
    (hγ : γ.virtuality = -⟪q, q⟫ₘ) (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n) :
    ⟪q + P, q + P⟫ₘ =
      ⟪P, P⟫ₘ - γ.virtuality + 2 * (γ.energy * E + p * ⟪q.spatialPart, n⟫_ℝ) := by
  rw [minkowskiProduct_add_self_of_spatialPart_eq_smul hP', hq, hP, hγ]
  ring

/-- **The invariant mass of a photon null along the beam axis and a target.** A photon `γ` whose
four-momentum `q` is null along the unit beam axis `n`, `q⁰ = γ.energy` and
`q.spatialPart = γ.energy • n`, and a target of energy `E` and momentum
`p` against it form a system of invariant mass `W² = P² + 2 γ.energy (E + p)`, with `P² = M²` for a
target of mass `M`. When moreover `γ.virtuality = -⟪q, q⟫ₘ` and `0 ≤ γ.energy`, `γ` is a real
photon (`PhotonKinematics.isReal_iff_abs_eq_energy_of_spatialPart_eq_smul`). -/
theorem minkowskiProduct_add_self_eq_add_two_mul_energy_mul_add (hn : ‖n‖ = 1)
    (hq : q.timeComponent = γ.energy) (hq' : q.spatialPart = γ.energy • n)
    (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n) :
    ⟪q + P, q + P⟫ₘ = ⟪P, P⟫ₘ + 2 * γ.energy * (E + p) := by
  rw [minkowskiProduct_add_self_of_spatialPart_eq_smul hP',
    minkowskiProduct_self_eq_zero_of_timeComponent_eq_of_spatialPart_eq_smul hn hq hq',
    inner_spatialPart_eq_of_spatialPart_eq_smul hn hq', hq, hP]
  ring

/-- **The energy fraction from the invariant mass and the rapidity.** A photon `γ` of
four-momentum `q`, with `q⁰ = γ.energy` and momentum `a` along the unit beam axis `n`, of any
virtuality, and a target of energy `E` and momentum `p` against it, with `|a - p| < γ.energy + E`,
form a system of invariant mass `W` and rapidity `y` along `n` with `x = (W cosh y - E) / E_s`,
where `x` is the fraction of the energy `E_s` of the source `s` carried by the photon. -/
theorem energyFraction_eq_sqrt_minkowskiProduct_add_self_mul_cosh_rapidity_sub_div
    (hn : ‖n‖ = 1) (hq : q.timeComponent = γ.energy) (hq' : q.spatialPart = a • n)
    (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n) (h : |a - p| < γ.energy + E) :
    γ.energyFraction s = (√⟪q + P, q + P⟫ₘ * cosh ((q + P).rapidity n) - E) / s.energy := by
  -- the energy of the system is `γ.energy + E = W cosh y`
  rw [energyFraction_def,
    ← timeComponent_eq_sqrt_minkowskiProduct_self_mul_cosh_rapidity_of_spatialPart_eq_smul hn
      (spatialPart_add_eq_smul_of_spatialPart_eq_smul hq' hP')
      (by rwa [timeComponent_add, hq, hP, ← sub_eq_add_neg]),
    timeComponent_add, hq, hP, add_sub_cancel_right]

/-- **The energy fraction of a photon null along the beam axis from the invariant mass and the
rapidity.** A photon `γ` whose four-momentum `q` is null along the unit beam axis `n`,
`q⁰ = γ.energy` and `q.spatialPart = γ.energy • n`, and a target of energy `E` and momentum `p`
against it, with `|γ.energy - p| < γ.energy + E`, form a system of invariant mass `W` and rapidity
`y` along `n` with `x = e^{y} (W² - P²) / (2 W E_s)`, where `x` is the fraction of the energy
`E_s` of the source `s` carried by the photon and `P² = M²` for a target of mass `M`. When
moreover `γ.virtuality = -⟪q, q⟫ₘ` and `0 ≤ γ.energy`, `γ` is a real photon
(`PhotonKinematics.isReal_iff_abs_eq_energy_of_spatialPart_eq_smul`). -/
theorem energyFraction_eq_exp_rapidity_mul_sub_div_sqrt_minkowskiProduct_add_self
    (hn : ‖n‖ = 1) (hq : q.timeComponent = γ.energy) (hq' : q.spatialPart = γ.energy • n)
    (hP : P.timeComponent = E) (hP' : P.spatialPart = -p • n)
    (h : |γ.energy - p| < γ.energy + E) :
    γ.energyFraction s = exp ((q + P).rapidity n) * (⟪q + P, q + P⟫ₘ - ⟪P, P⟫ₘ) /
      (2 * √⟪q + P, q + P⟫ₘ * s.energy) := by
  have h' : |γ.energy + -p| < q.timeComponent + P.timeComponent := by
    rwa [hq, hP, ← sub_eq_add_neg]
  have hW := minkowskiProduct_add_self_eq_add_two_mul_energy_mul_add hn hq hq' hP hP'
  -- `E + p = W e^{-y}`
  have hB :=
    timeComponent_sub_eq_sqrt_minkowskiProduct_self_mul_exp_neg_rapidity_of_spatialPart_eq_smul hn
      (spatialPart_add_eq_smul_of_spatialPart_eq_smul hq' hP') (by rwa [timeComponent_add])
  rw [timeComponent_add, hq, hP] at hB
  have hpos := sqrt_minkowskiProduct_add_self_pos_of_spatialPart_eq_smul hn hq' hP' h'
  have he : exp ((q + P).rapidity n) * exp (-(q + P).rapidity n) = 1 := by
    rw [← exp_add, add_neg_cancel, exp_zero]
  rw [energyFraction_def, ← div_div]
  congr 1
  rw [eq_div_iff (mul_ne_zero two_ne_zero hpos.ne')]
  -- `e^{y} (W² - P²) = 2 k e^{y} (E + p) = 2 k W e^{y} e^{-y} = 2 k W`
  linear_combination (-exp ((q + P).rapidity n)) * hW -
    2 * γ.energy * exp ((q + P).rapidity n) * hB - 2 * γ.energy * √⟪q + P, q + P⟫ₘ * he

end PhotonKinematics

end Kinematics
end Photoproduction
end Scattering
end QFT
end EpsilonEridani
