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
Each method represents a different experimental technique for accessing the standard DIS variables
(xBj, Q2, y). The electron, Sigma and eSigma methods carry appropriateness lemmas (positivity,
range and the eSigma agreement identity).

## Access Methods

- **Electron Method**: Reconstructs invariants from electron scattering
  kinematics (angle, energy loss)
- **Sigma Method**: Reconstructs Q² from the lepton momentum transfer and y from the hadronic
  final state
- **eSigma Method**: Reconstructs invariants from both electron and hadronic final states

-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]
variable (g : Bilin V)

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

/-- Electron method xBj reconstruction (requires hadronic invariant mass input). -/
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

/-- Sigma method data: hadronic final state information. -/
structure SigmaMethodData where
  /-- Sum of hadronic final state momenta (Jacquet-Blondel observable). -/
  hadronicMomentum : V
  /-- Incoming lepton momentum. -/
  kIn : V
  /-- Outgoing lepton momentum (required for energy-momentum conservation). -/
  kOut : V
  /-- Initial state total 4-momentum. -/
  initialMomentum : V

namespace SigmaMethodData

/-- Sigma method Q² reconstruction from the t-channel momentum transfer: minus the Minkowski square
of the lepton momentum transfer `kIn - kOut`. -/
def q2Sigma (d : SigmaMethodData V) (g_met : Bilin V) : ℝ :=
  -g_met (d.kIn - d.kOut) (d.kIn - d.kOut)

/-- Sigma method y reconstruction from hadronic energy fraction. -/
def ySigma (d : SigmaMethodData V) (g_met : Bilin V) : ℝ :=
  (g_met d.initialMomentum d.initialMomentum -
    g_met (d.initialMomentum - d.hadronicMomentum - d.kOut)
      (d.initialMomentum - d.hadronicMomentum - d.kOut)) /
    g_met d.initialMomentum d.initialMomentum

/-- Appropriateness theorem: Sigma method Q² is non-negative. -/
lemma q2Sigma_nonneg (d : SigmaMethodData V) (g_met : Bilin V)
    (hTransfer : g_met (d.kIn - d.kOut) (d.kIn - d.kOut) ≤ 0) :
    0 ≤ SigmaMethodData.q2Sigma (V := V) d g_met := by
  simp only [q2Sigma]
  exact neg_nonneg.mpr hTransfer

end SigmaMethodData

/-- eSigma method: uses both electron and hadronic information. -/
structure ESigmaMethodData where
  /-- Electron method component. -/
  electronData : ElectronMethodData
  /-- Hadronic method component. -/
  sigmaData : SigmaMethodData V

namespace ESigmaMethodData

/-- eSigma method Q² reconstruction: average of electron and Sigma methods. -/
def q2ESigma (d : ESigmaMethodData V) : ℝ :=
  (ElectronMethodData.q2Electron d.electronData +
    SigmaMethodData.q2Sigma (V := V) d.sigmaData g) / 2

/-- eSigma method y reconstruction: average of both methods. -/
def yESigma (d : ESigmaMethodData V) : ℝ :=
  (ElectronMethodData.yElectron d.electronData +
    SigmaMethodData.ySigma (V := V) d.sigmaData g) / 2

/-- Appropriateness theorem: the eSigma Q² lies exactly halfway between the electron and Sigma
reconstructions, so its deviation from the electron Q² is exactly half the electron-Sigma
discrepancy. -/
lemma abs_q2ESigma_sub_q2Electron_eq (d : ESigmaMethodData V) :
    |q2ESigma (V := V) (g := g) d - ElectronMethodData.q2Electron d.electronData| =
      |ElectronMethodData.q2Electron d.electronData -
        SigmaMethodData.q2Sigma (V := V) d.sigmaData g| / 2 := by
  let A : ℝ := ElectronMethodData.q2Electron d.electronData
  let B : ℝ := SigmaMethodData.q2Sigma (V := V) d.sigmaData g
  unfold q2ESigma
  have hcalc : (A + B) / 2 - A = (B - A) / 2 := by ring
  rw [hcalc]
  rw [abs_div, abs_sub_comm]
  simp [A, B]

end ESigmaMethodData

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
