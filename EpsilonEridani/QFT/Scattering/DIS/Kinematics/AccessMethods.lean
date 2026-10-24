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
- **Covariant methods**: `electronMethod`, `hadronicMethod`, `sigmaMethod` and `mixedMethod`
  return the full triple `(x, Q², y)` as a `ReconstructedInvariants`, each as a function of
  exactly the momenta it measures. `ElectronMethodData` is the collider-frame form of
  `electronMethod`; the reduction of one to the other is not yet proved.

## References

- U. Bassler and G. Bernardi, *On the kinematic reconstruction of deep inelastic scattering at
  HERA: the Σ method*, Nucl. Instrum. Meth. A **361** (1995) 197, arXiv:hep-ex/9412004. In the
  HERA frame with a massless target, `ySigma` reduces to their `y_Σ = Σ / (Σ + E'(1 - cos θ))`.
- F. Jacquet and A. Blondel, in *Proceedings of the Study of an ep Facility for Europe*,
  ed. U. Amaldi, DESY 79/48 (1979) 391, for the hadronic method.
- S. Bentvelsen, J. Engelen and P. Kooijman, *Reconstruction of (x, Q²) and extraction of
  structure functions in neutral current scattering at HERA*, Proceedings of the Workshop
  Physics at HERA, vol. 1 (1992) 23, for the mixed method.

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
    E_e' is final electron energy, and θ is the scattering angle. This is the collider-frame
    form of the covariant `electronMethod`; the reduction of one to the other is not yet
    proved. -/
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

/-! ### Covariant reconstruction methods -/

section Covariant

variable {V}

/-- The invariants `x`, `Q²` and `y` computed from a measurement by a reconstruction method. -/
@[ext] structure ReconstructedInvariants where
  /-- The reconstructed Bjorken variable. -/
  x : ℝ
  /-- The reconstructed photon virtuality. -/
  Q2 : ℝ
  /-- The reconstructed inelasticity. -/
  y : ℝ

/-- The electron method, from the incoming lepton `k`, the target `p` and the scattered lepton
`k'`: with `q_e = k - k'`, it returns `Q²_e = -q_e²`, `y_e = (p·q_e) / (p·k)` and
`x_e = Q²_e / (2 p·q_e)`. `ElectronMethodData` is its collider-frame form in terms of the beam
energy, the scattered energy and the scattering angle; the reduction of this definition to that
one is not yet proved. -/
@[simps]
def electronMethod (g : Bilin V) (k p kPrime : V) : ReconstructedInvariants where
  x := -g (k - kPrime) (k - kPrime) / (2 * g p (k - kPrime))
  Q2 := -g (k - kPrime) (k - kPrime)
  y := g p (k - kPrime) / g p k

/-- The hadronic method of Jacquet and Blondel, from the incoming lepton `k`, the target `p` and
the hadronic final state `p_X`: with `q_h = p_X - p`, it returns `Q²_h = -q_h²`,
`y_h = (p·q_h) / (p·k)` and `x_h = Q²_h / (2 p·q_h)`. -/
@[simps]
def hadronicMethod (g : Bilin V) (k p pX : V) : ReconstructedInvariants where
  x := -g (pX - p) (pX - p) / (2 * g p (pX - p))
  Q2 := -g (pX - p) (pX - p)
  y := g p (pX - p) / g p k

/-- The Sigma method, from all four measured momenta: the virtuality `Q²_e` of the electron
method, the inelasticity `y_Σ = (p·q_h) / (p·q_h + p·k')` of Bassler and Bernardi
(`SigmaMethodData.ySigma`), in which the incoming lepton does not appear, and
`x_Σ = Q²_e / (2 (p·k) y_Σ)`. Bassler and Bernardi build their own virtuality from the
transverse momentum of the scattered lepton; it is not used here. -/
@[simps]
def sigmaMethod (g : Bilin V) (k p kPrime pX : V) : ReconstructedInvariants where
  x := (electronMethod g k p kPrime).Q2 / (2 * g p k * SigmaMethodData.ySigma ⟨pX, kPrime, p⟩ g)
  Q2 := (electronMethod g k p kPrime).Q2
  y := SigmaMethodData.ySigma ⟨pX, kPrime, p⟩ g

/-- The mixed method of Bentvelsen, Engelen and Kooijman, from all four measured momenta: the
virtuality `Q²_e` of the electron method, the inelasticity `y_h` of the hadronic method, and
`x = Q²_e / (2 p·q_h)`, which is `Q²_e / (2 (p·k) y_h)` wherever `p·k ≠ 0`
(`mixedMethod_x_eq`). -/
@[simps]
def mixedMethod (g : Bilin V) (k p kPrime pX : V) : ReconstructedInvariants where
  x := (electronMethod g k p kPrime).Q2 / (2 * g p (pX - p))
  Q2 := (electronMethod g k p kPrime).Q2
  y := (hadronicMethod g k p pX).y

/-- The Sigma-method inelasticity in terms of the measured momenta,
`y_Σ = (p·q_h) / (p·q_h + p·k')`. -/
theorem sigmaMethod_y_eq (g : Bilin V) (k p kPrime pX : V) :
    (sigmaMethod g k p kPrime pX).y = g p (pX - p) / (g p (pX - p) + g p kPrime) :=
  rfl

/-- The Sigma-method Bjorken variable in terms of the measured momenta,
`x_Σ = Q²_e (p·q_h + p·k') / (2 (p·k) (p·q_h))`. -/
theorem sigmaMethod_x_eq (g : Bilin V) (k p kPrime pX : V) :
    (sigmaMethod g k p kPrime pX).x = (electronMethod g k p kPrime).Q2 *
      (g p (pX - p) + g p kPrime) / (2 * g p k * g p (pX - p)) := by
  rw [sigmaMethod_x, ← sigmaMethod_y g k, sigmaMethod_y_eq]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- The mixed-method Bjorken variable is `Q²_e / (2 (p·k) y_h)` wherever `p·k ≠ 0`. -/
theorem mixedMethod_x_eq (g : Bilin V) (k p kPrime pX : V) (hpk : g p k ≠ 0) :
    (mixedMethod g k p kPrime pX).x =
      (mixedMethod g k p kPrime pX).Q2 / (2 * g p k * (mixedMethod g k p kPrime pX).y) := by
  rw [mixedMethod_x, mixedMethod_Q2, mixedMethod_y, hadronicMethod_y, mul_assoc,
    mul_div_cancel₀ _ hpk]

/-- The electron method applied to the lepton momenta of a DIS kinematic record returns its
canonical invariants. -/
theorem electronMethod_disKinematics (g : Bilin V) (K : DisKinematics V) :
    electronMethod g K.k K.p K.kPrime = ⟨K.xBj g, K.Q2 g, K.yInel g⟩ := by
  simp [electronMethod, DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel, ← K.hq]

end Covariant

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
