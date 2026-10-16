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
  p_dot_q_pos : 0 < g K.p K.q
  p_dot_k_pos : 0 < g K.p K.k
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

lemma xBj_in_unitInterval (g : Bilin V) (K : DisKinematics V) (h : BasicAssumptions g K) :
    0 < K.xBj g ∧ K.xBj g ≤ 1 :=
  ⟨xBj_pos g K h.q2_pos h.p_dot_q_pos, xBj_le_one g K h.p_dot_q_pos h.q2_le_two_p_dot_q⟩

lemma yInel_in_unitInterval (g : Bilin V) (K : DisKinematics V) (h : BasicAssumptions g K) :
    0 < K.yInel g ∧ K.yInel g ≤ 1 :=
  ⟨yInel_pos g K h.p_dot_q_pos h.p_dot_k_pos, yInel_le_one g K h.p_dot_k_pos h.p_dot_q_le_p_dot_k⟩

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
