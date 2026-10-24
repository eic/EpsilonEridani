/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# DIS Kinematic Bounds

This module provides baseline positivity and unit-interval lemmas for the DIS kinematics layer.
All bounds are stated under explicit assumptions.

-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]

namespace DisKinematics

variable {V}

/-- A minimal assumption bundle used to establish canonical DIS bounds. -/
structure BasicAssumptions (g : Bilin V) (K : DisKinematics V) : Prop where
  q2_pos : 0 < K.Q2 g
  q2_le_two_p_dot_q : K.Q2 g ≤ 2 * g K.p K.q
  p_dot_q_le_p_dot_k : g K.p K.q ≤ g K.p K.k

lemma xBj_pos (g : Bilin V) (K : DisKinematics V) (hQ : 0 < K.Q2 g) (hpq : 0 < g K.p K.q) :
    0 < K.xBj g := by
  unfold xBj
  have hden : 0 < 2 * g K.p K.q := by linarith
  exact div_pos hQ hden

lemma xBj_le_one (g : Bilin V) (K : DisKinematics V) (hpq : 0 < g K.p K.q)
    (h : K.Q2 g ≤ 2 * g K.p K.q) : K.xBj g ≤ 1 := by
  unfold xBj
  have hden : 0 < 2 * g K.p K.q := by linarith
  exact (div_le_one hden).2 h

lemma yInel_pos (g : Bilin V) (K : DisKinematics V) (hpq : 0 < g K.p K.q)
    (hpk : 0 < g K.p K.k) : 0 < K.yInel g := by
  unfold yInel
  exact div_pos hpq hpk

lemma yInel_le_one (g : Bilin V) (K : DisKinematics V) (hpk : 0 < g K.p K.k)
    (h : g K.p K.q ≤ g K.p K.k) : K.yInel g ≤ 1 := by
  unfold yInel
  exact (div_le_one hpk).2 h

/-- Under `BasicAssumptions`, `P·q > 0`, since `0 < Q² ≤ 2 P·q`. -/
lemma BasicAssumptions.p_dot_q_pos {g : Bilin V} {K : DisKinematics V}
    (h : BasicAssumptions g K) : 0 < g K.p K.q := by
  linarith [h.q2_pos, h.q2_le_two_p_dot_q]

/-- Under `BasicAssumptions`, `P·k > 0`, since `0 < P·q ≤ P·k`. -/
lemma BasicAssumptions.p_dot_k_pos {g : Bilin V} {K : DisKinematics V}
    (h : BasicAssumptions g K) : 0 < g K.p K.k :=
  h.p_dot_q_pos.trans_le h.p_dot_q_le_p_dot_k

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
