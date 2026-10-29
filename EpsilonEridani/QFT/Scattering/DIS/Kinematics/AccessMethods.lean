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
method reconstructs y, which is `DisKinematics.yInel` under energy-momentum conservation. Without
radiation the Sigma method needs no Q² of its own, since the lepton momentum transfer then gives
the canonical `DisKinematics.Q2` directly; after initial-state radiation it does not
(`Kinematics.Radiative`).

## Access Methods

- **Electron Method**: Reconstructs invariants from electron scattering
  kinematics (angle, energy loss)
- **Sigma Method**: Reconstructs y from the target momentum `P`, the hadronic final state `p_X`
  and the scattered lepton `k'`, as `y_Σ = P·(p_X - P) / (P·(p_X - P) + P·k')`; this y does not
  involve the incident lepton momentum
- **Covariant methods**: `electronMethod`, `hadronicMethod`, `sigmaMethod` and `mixedMethod`
  return the full triple `(x, Q², y)` as a `ReconstructedInvariants`, each as a function of
  exactly the momenta it measures. The electron and hadronic methods are the invariants
  `ReconstructedInvariants.ofTransfer` of the lepton and of the hadronic momentum transfer. In
  the target rest frame `electronMethod` reduces to `ElectronMethodData`
  (`ElectronMethodData.electronMethod_eq`).
- **True invariants and shifts**: `TrueInvariants` carries the invariants of the hard scattering,
  kept apart from `ReconstructedInvariants`; `ReconstructedInvariants.shiftXQ2` and
  `ReconstructedInvariants.shiftXY` are the shift of reconstructed from true invariants.

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
    E_e' is final electron energy, and θ is the scattering angle. Its `yElectron` and
    `xBjElectron` are the target-rest-frame (fixed-target) expressions, which use
    `p·k = M_p E_e`; there the covariant `electronMethod` reduces to them
    (`ElectronMethodData.electronMethod_eq`). -/
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

namespace ReconstructedInvariants

/-- The invariants of a momentum transfer `q` from a lepton of momentum `k` to a target of
momentum `p`: `Q² = -q²`, `y = (p·q) / (p·k)` and `x = Q² / (2 p·q)`, the canonical invariants of
any DIS kinematic record with these momenta (`ofTransfer_eq_xBj_Q2_yInel`). -/
@[simps]
def ofTransfer (g : Bilin V) (k p q : V) : ReconstructedInvariants where
  x := -g q q / (2 * g p q)
  Q2 := -g q q
  y := g p q / g p k

/-- The invariants of the momentum transfer of a DIS kinematic record are its canonical
`DisKinematics.xBj`, `DisKinematics.Q2` and `DisKinematics.yInel`. -/
theorem ofTransfer_eq_xBj_Q2_yInel (g : Bilin V) (K : DisKinematics V) :
    ofTransfer g K.k K.p K.q = ⟨K.xBj g, K.Q2 g, K.yInel g⟩ := by
  ext <;> simp [DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel]

/-- The Bjorken variable of a momentum transfer is `Q² / (2 (p·k) y)` wherever `p·k ≠ 0`. -/
theorem ofTransfer_x_eq (g : Bilin V) (k p q : V) (hpk : g p k ≠ 0) :
    (ofTransfer g k p q).x = (ofTransfer g k p q).Q2 / (2 * g p k * (ofTransfer g k p q).y) := by
  rw [ofTransfer_x, ofTransfer_Q2, ofTransfer_y, mul_assoc, mul_div_cancel₀ _ hpk]

end ReconstructedInvariants

/-- The electron method, from the incoming lepton `k`, the target `p` and the scattered lepton
`k'`: the invariants of the lepton momentum transfer `q_e = k - k'`, that is `Q²_e = -q_e²`,
`y_e = (p·q_e) / (p·k)` and `x_e = Q²_e / (2 p·q_e)`. In the target rest frame it reduces to the
expressions of `ElectronMethodData` in terms of the beam energy, the scattered energy, the
scattering angle and the target mass (`ElectronMethodData.electronMethod_eq`). -/
@[simps (rhsMd := .default)]
def electronMethod (g : Bilin V) (k p kPrime : V) : ReconstructedInvariants :=
  .ofTransfer g k p (k - kPrime)

/-- The hadronic method of Jacquet and Blondel, from the incoming lepton `k`, the target `p` and
the hadronic final state `p_X`: the invariants of the hadronic momentum transfer `q_h = p_X - p`,
that is `Q²_h = -q_h²`, `y_h = (p·q_h) / (p·k)` and `x_h = Q²_h / (2 p·q_h)`. -/
@[simps (rhsMd := .default)]
def hadronicMethod (g : Bilin V) (k p pX : V) : ReconstructedInvariants :=
  .ofTransfer g k p (pX - p)

/-- The Sigma method, from all four measured momenta: the virtuality `Q²_e` of the electron
method, the inelasticity `y_Σ = (p·q_h) / (p·q_h + p·k')` of Bassler and Bernardi
(`SigmaMethodData.ySigma`), in which the incoming lepton does not appear, and
`x_Σ = Q²_e / (2 (p·k) y_Σ)`. Bassler and Bernardi build their own virtuality from the
transverse momentum of the scattered lepton; it is not used here. Initial-state radiation shifts
this virtuality even where `x_Σ` and `y_Σ` are exact
(`RadiativeEvent.trueInvariants_Q2_of_collinear_initialState`,
`RadiativeEvent.shiftXY_sigmaMethod_eq_zero_of_collinear_initialState`). -/
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
    (sigmaMethod g k p kPrime pX).y = g p (pX - p) / (g p (pX - p) + g p kPrime) := by
  rw [sigmaMethod_y, SigmaMethodData.ySigma]

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
theorem electronMethod_eq_xBj_Q2_yInel (g : Bilin V) (K : DisKinematics V) :
    electronMethod g K.k K.p K.kPrime = ⟨K.xBj g, K.Q2 g, K.yInel g⟩ := by
  rw [electronMethod, ← K.hq, ReconstructedInvariants.ofTransfer_eq_xBj_Q2_yInel]

/-- In the rest frame of a target of mass `M`, where `p·k = M E` and `p·k' = M E'` for the beam
energy `E` and the scattered energy `E'`, and for massless leptons with `k·k' = E E' (1 - cos θ)`
at the scattering angle `θ`, the covariant electron method returns the target-rest-frame
expressions `xBjElectron`, `q2Electron` and `yElectron`. -/
theorem ElectronMethodData.electronMethod_eq (d : ElectronMethodData) (g : Bilin V)
    (hg : g.IsSymm) {k p kPrime : V} {M : ℝ} (hM : M ≠ 0) (hk : g k k = 0)
    (hk' : g kPrime kPrime = 0)
    (hkk' : g k kPrime = d.initialEnergy * d.finalEnergy * (1 - Real.cos d.theta))
    (hpk : g p k = M * d.initialEnergy) (hpk' : g p kPrime = M * d.finalEnergy) :
    electronMethod g k p kPrime = ⟨d.xBjElectron M, d.q2Electron, d.yElectron⟩ := by
  have hE : d.initialEnergy ≠ 0 := (d.energy_loss.1.trans d.energy_loss.2).ne'
  have hQ : -g (k - kPrime) (k - kPrime) = d.q2Electron := by
    rw [q2Electron, Real.sin_sq_eq_half_sub, mul_div_cancel₀ _ two_ne_zero]
    simp only [map_sub, LinearMap.sub_apply, hk, hk', hg.eq kPrime k, hkk']
    ring
  ext
  · rw [electronMethod_x, hQ, map_sub, hpk, hpk', xBjElectron, yElectron]
    field_simp
  · exact hQ
  · rw [electronMethod_y, map_sub, hpk, hpk', yElectron]
    field_simp

/-- The invariants of the hard lepton–hadron scattering of an event: the Bjorken variable `x`,
the photon virtuality `Q² = -q²` and the inelasticity `y`. -/
@[ext] structure TrueInvariants where
  /-- The Bjorken variable `x = Q² / (2 p·q)`, with `q` the momentum transferred to the
  hadrons. -/
  x : ℝ
  /-- The photon virtuality `Q² = -q²`. -/
  Q2 : ℝ
  /-- The inelasticity `y = (p·q) / (p·k_hard)`, where `k_hard` is the lepton momentum entering
  the hard scattering (`k - ℓ` after initial-state emission of a photon `ℓ`). -/
  y : ℝ

/-- The reconstruction returned by an exact measurement of the true invariants `t`. -/
@[simps]
def TrueInvariants.toReconstructedInvariants (t : TrueInvariants) : ReconstructedInvariants where
  x := t.x
  Q2 := t.Q2
  y := t.y

namespace ReconstructedInvariants

/-- The shift `r - t` of the reconstructed invariants `r` from the true invariants `t`,
componentwise in `(x, Q²)`. -/
@[simps]
def shiftXQ2 (r : ReconstructedInvariants) (t : TrueInvariants) : ℝ × ℝ :=
  (r.x - t.x, r.Q2 - t.Q2)

/-- The shift `r - t` of the reconstructed invariants `r` from the true invariants `t`,
componentwise in `(x, y)`. -/
@[simps]
def shiftXY (r : ReconstructedInvariants) (t : TrueInvariants) : ℝ × ℝ :=
  (r.x - t.x, r.y - t.y)

/-- The `(x, Q²)` shift vanishes exactly when `x` and `Q²` are reconstructed exactly. -/
@[simp] theorem shiftXQ2_eq_zero_iff {r : ReconstructedInvariants} {t : TrueInvariants} :
    r.shiftXQ2 t = 0 ↔ r.x = t.x ∧ r.Q2 = t.Q2 := by
  simp [Prod.ext_iff, sub_eq_zero]

/-- The `(x, y)` shift vanishes exactly when `x` and `y` are reconstructed exactly. -/
@[simp] theorem shiftXY_eq_zero_iff {r : ReconstructedInvariants} {t : TrueInvariants} :
    r.shiftXY t = 0 ↔ r.x = t.x ∧ r.y = t.y := by
  simp [Prod.ext_iff, sub_eq_zero]

/-- An exact measurement has no `(x, Q²)` shift. -/
theorem shiftXQ2_toReconstructedInvariants_self (t : TrueInvariants) :
    t.toReconstructedInvariants.shiftXQ2 t = 0 := by
  simp

/-- An exact measurement has no `(x, y)` shift. -/
theorem shiftXY_toReconstructedInvariants_self (t : TrueInvariants) :
    t.toReconstructedInvariants.shiftXY t = 0 := by
  simp

end ReconstructedInvariants

end Covariant

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
