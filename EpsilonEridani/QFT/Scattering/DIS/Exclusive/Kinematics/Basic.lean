/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# Exclusive DIS Kinematics Interfaces

This module extends the inclusive kinematics layer with off-forward variables used by
DVCS and DVMP interfaces.

-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]

/-- A bilinear form used to evaluate Lorentz-invariant scalar products. -/
abbrev Bilin := LinearMap.BilinForm ℝ V

/-- Minimal off-forward exclusive kinematics container. -/
structure ExclKinematics where
  /-- Incoming hadron momentum. -/
  p : V
  /-- Outgoing hadron momentum. -/
  pPrime : V
  /-- Incoming lepton momentum. -/
  k : V
  /-- Outgoing lepton momentum. -/
  kPrime : V
  /-- Momentum of the exchanged virtual photon, `q = k - k'` by `hqLepton`. -/
  q : V
  /-- Momentum of the produced real photon (DVCS) or meson (DVMP). -/
  qPrime : V
  /-- Azimuthal angle of the lepton plane. -/
  phiL : ℝ
  /-- Azimuthal angle of the hadron plane. -/
  phiH : ℝ
  /-- The virtual photon carries the lepton momentum transfer. -/
  hqLepton : q = k - kPrime
  /-- Momentum conservation at the hadronic vertex, `p + q = p' + q'`. -/
  hMomentum : p + q = pPrime + qPrime

namespace ExclKinematics

variable {V}

/-- Hard scale in the exclusive channel. -/
def Q2 (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  - g K.q K.q

omit [Module ℝ V] in
/-- Momentum transfer to the hadron, `Δ = p' - p`. -/
def delta (K : ExclKinematics V) : V :=
  K.pPrime - K.p

/-- Momentum-transfer invariant `t = Δ² = (p' - p)²` in the exclusive channel. -/
def tMom (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  g K.delta K.delta

/-- Skewness-style variable with a regularized denominator interface. -/
noncomputable def xiSkew (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  K.Q2 g / (2 * g K.p K.q + 1)

/-- Relative azimuthal angle between hadron and lepton planes. -/
def phiDiff (K : ExclKinematics V) : ℝ :=
  K.phiH - K.phiL

omit [Module ℝ V] in
lemma q_eq_lepton_transfer (K : ExclKinematics V) :
    K.q = K.k - K.kPrime :=
  K.hqLepton

omit [Module ℝ V] in
/-- Momentum conservation expresses the hadron momentum transfer through the photon side,
`Δ = q - q'`. -/
lemma delta_eq_q_sub_qPrime (K : ExclKinematics V) :
    K.delta = K.q - K.qPrime := by
  rw [delta, sub_eq_sub_iff_add_eq_add, ← K.hMomentum]
  exact add_comm _ _

lemma tMom_eq_hadronic_transfer_sq
    (g : Bilin V) (K : ExclKinematics V) :
    K.tMom g = g (K.pPrime - K.p) (K.pPrime - K.p) :=
  rfl

/-- `t` evaluated on the photon side of the hadronic vertex, `t = (q - q')²`. -/
lemma tMom_eq_photon_transfer_sq
    (g : Bilin V) (K : ExclKinematics V) :
    K.tMom g = g (K.q - K.qPrime) (K.q - K.qPrime) := by
  rw [tMom, delta_eq_q_sub_qPrime]

end ExclKinematics

end Kinematics
end Exclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
