/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# DIS Kinematics Access Methods

This module implements reconstruction methods for DIS invariants from experimental measurements.
The electron method reconstructs Q², y and xBj and carries positivity and range lemmas. The Sigma
method reconstructs y, which is `DisKinematics.yInel` under energy-momentum conservation; the
Sigma method needs no Q² of its own, since the lepton momentum transfer gives the canonical
`DisKinematics.Q2` directly.

## Access Methods

- **Electron Method**: Reconstructs invariants from electron scattering
  kinematics (angle, energy loss)
- **Sigma Method**: Reconstructs y from the target momentum `P`, the hadronic final state `p_X`
  and the scattered lepton `k'`, as `y_Σ = P·(p_X - P) / (P·(p_X - P) + P·k')`; this y does not
  involve the incident lepton momentum

## References

- U. Bassler and G. Bernardi, *On the kinematic reconstruction of deep inelastic scattering at
  HERA: the Σ method*, Nucl. Instrum. Meth. A **361** (1995) 197, arXiv:hep-ex/9412004. In the
  HERA frame with a massless target, `ySigma` reduces to their `y_Σ = Σ / (Σ + E'(1 - cos θ))`.

-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]

/-- Electron method: Q² reconstruction from electron scattering angle and energy.
    Q² = 4 * E_e * E_e' * sin²(θ/2), where E_e is initial electron energy,
    E_e' is final electron energy, and θ is the scattering angle. -/
structure ElectronMethodData where
  /-- Initial electron energy. -/
  initialEnergy : ℝ
  /-- Final electron energy after scattering. -/
  finalEnergy : ℝ
  /-- Scattering angle (between incident and scattered electron). -/
  theta : ℝ
  /-- Constraint: final energy is less than initial (energy loss). -/
  energy_loss : 0 < finalEnergy ∧ finalEnergy < initialEnergy
  /-- Constraint: scattering angle in physical range. -/
  theta_bounds : 0 < theta ∧ theta < Real.pi

namespace ElectronMethodData

/-- Electron method Q² reconstruction. -/
def q2Electron (d : ElectronMethodData) : ℝ :=
  4 * d.initialEnergy * d.finalEnergy * (Real.sin (d.theta / 2)) ^ 2

/-- Electron method y reconstruction from energy ratio. -/
def yElectron (d : ElectronMethodData) : ℝ :=
  1 - d.finalEnergy / d.initialEnergy

/-- Electron method xBj reconstruction; `M_p` is the target (proton) mass. -/
def xBjElectron (d : ElectronMethodData) (M_p : ℝ) : ℝ :=
  (q2Electron d) / (2 * M_p * d.initialEnergy * (yElectron d))

/-- Appropriateness theorem: electron method Q² reconstruction is positive. -/
lemma q2Electron_pos (d : ElectronMethodData) : 0 < q2Electron d := by
  unfold q2Electron
  have hEi : 0 < d.initialEnergy := lt_trans d.energy_loss.1 d.energy_loss.2
  have hEf : 0 < d.finalEnergy := d.energy_loss.1
  have hHalfPos : 0 < d.theta / 2 := by linarith [d.theta_bounds.1]
  have hHalfLtPi : d.theta / 2 < Real.pi := by linarith [d.theta_bounds.2, Real.pi_pos]
  have hSinPos : 0 < Real.sin (d.theta / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hHalfPos hHalfLtPi
  have hSinSqPos : 0 < (Real.sin (d.theta / 2)) ^ 2 := sq_pos_of_pos hSinPos
  positivity

/-- Appropriateness theorem: electron method y is in valid range (0, 1). -/
lemma yElectron_bounds (d : ElectronMethodData) : 0 < yElectron d ∧ yElectron d < 1 := by
  unfold yElectron
  have hEi : 0 < d.initialEnergy := lt_trans d.energy_loss.1 d.energy_loss.2
  have hRatioPos : 0 < d.finalEnergy / d.initialEnergy := div_pos d.energy_loss.1 hEi
  have hRatioLtOne : d.finalEnergy / d.initialEnergy < 1 := by
    refine (div_lt_iff₀ hEi).2 ?_
    simpa using d.energy_loss.2
  constructor
  · linarith [hRatioLtOne]
  · linarith [hRatioPos]

end ElectronMethodData

/-- Sigma method input data: the hadronic final state momentum sum, the outgoing lepton momentum,
and the incoming target momentum. -/
structure SigmaMethodData where
  /-- Sum of hadronic final state momenta `p_X`. -/
  hadronicMomentum : V
  /-- Outgoing lepton momentum. -/
  kOut : V
  /-- Incoming target hadron momentum. -/
  targetMomentum : V

namespace SigmaMethodData

variable {V}

/-- Sigma method y reconstruction `P·q_h / (P·q_h + P·k')`, built from the target momentum `P`,
the hadronic transfer `q_h = hadronicMomentum - P` and the outgoing lepton momentum `k'`. The
incoming lepton momentum does not enter. -/
def ySigma (d : SigmaMethodData V) (g_met : Bilin V) : ℝ :=
  g_met d.targetMomentum (d.hadronicMomentum - d.targetMomentum) /
    (g_met d.targetMomentum (d.hadronicMomentum - d.targetMomentum) +
      g_met d.targetMomentum d.kOut)

/-- Under energy-momentum conservation `P + k = p_X + k'`, the Sigma method y is the canonical
`DisKinematics.yInel` of any kinematic record with the same target and outgoing lepton
momenta. -/
lemma ySigma_eq_yInel (d : SigmaMethodData V) (g_met : Bilin V) (K : DisKinematics V)
    (hp : K.p = d.targetMomentum) (hk' : K.kPrime = d.kOut)
    (hCons : d.targetMomentum + K.k = d.hadronicMomentum + d.kOut) :
    d.ySigma g_met = K.yInel g_met := by
  have hq : d.hadronicMomentum - d.targetMomentum = K.q := by
    rw [K.hq, hk', sub_eq_sub_iff_add_eq_add, ← hCons, add_comm]
  rw [ySigma, DisKinematics.yInel, hq, ← map_add, hp, K.hq, hk', sub_add_cancel]

end SigmaMethodData

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
