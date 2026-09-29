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

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin)

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
  /-- Exchanged momentum, tied to both momentum pairs by `hqLepton` and `hqHadron`. -/
  q : V
  /-- Momentum of the produced photon or meson. -/
  qPrime : V
  /-- Azimuthal angle of the lepton plane. -/
  phiL : ℝ
  /-- Azimuthal angle of the hadron plane. -/
  phiH : ℝ
  hqLepton : q = k - kPrime
  hqHadron : q = pPrime - p

namespace ExclKinematics

variable {V}

/-- Hard scale in the exclusive channel. -/
def Q2 (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  - g K.q K.q

/-- Momentum-transfer invariant in the exclusive channel. -/
def tMom (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  g K.q K.q

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
lemma q_eq_hadron_transfer (K : ExclKinematics V) :
    K.q = K.pPrime - K.p :=
  K.hqHadron

lemma tMom_eq_hadronic_transfer_sq
    (g : Bilin V) (K : ExclKinematics V) :
    K.tMom g = g (K.pPrime - K.p) (K.pPrime - K.p) := by
  simp [tMom, K.hqHadron]

end ExclKinematics

end Kinematics
end Exclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
