/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Deep Inelastic Scattering Kinematics

This module introduces the abstract bilinear form `Bilin` used to evaluate Lorentz-invariant
scalar products, with its symmetric square expansions, and a minimal kinematic record with the
canonical DIS invariants. The design follows the architecture freeze document.

-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]

/-- A bilinear form used to evaluate Lorentz-invariant scalar products in abstract form. -/
abbrev Bilin (V : Type) [AddCommGroup V] [Module ℝ V] := LinearMap.BilinForm ℝ V

namespace Bilin

variable {V}

/-- Square of a sum for a symmetric form: `(u + v)² = u² + 2 u·v + v²`. -/
lemma apply_add_self (g : Bilin V) (hg : g.IsSymm) (u v : V) :
    g (u + v) (u + v) = g u u + 2 * g u v + g v v := by
  linarith [hg.polarization u v]

/-- Square of a difference for a symmetric form: `(u - v)² = u² - 2 u·v + v²`. -/
lemma apply_sub_self (g : Bilin V) (hg : g.IsSymm) (u v : V) :
    g (u - v) (u - v) = g u u - 2 * g u v + g v v := by
  rw [sub_eq_add_neg, apply_add_self g hg]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  ring

end Bilin

/-- Minimal process-level kinematics for inclusive DIS. -/
structure DisKinematics where
  /-- Incoming hadron momentum. -/
  p : V
  /-- Outgoing hadron momentum in exclusive/semi-inclusive projections.
    For inclusive DIS this field can be carried as background data. -/
  pPrime : V
  /-- Incoming lepton momentum. -/
  k : V
  /-- Outgoing hadron-side aggregate not represented explicitly here; outgoing lepton momentum. -/
  kPrime : V
  /-- Momentum transfer to the hadronic system. -/
  q : V
  /-- Kinematic relation `q = k - kPrime`. -/
  hq : q = k - kPrime

namespace DisKinematics

variable {V}

/-- The hard scale `Q2 := - q^2`. -/
def Q2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  - g K.q K.q

/-- The Bjorken scaling variable `xBj := Q2 / (2 p·q)`. -/
noncomputable def xBj (g : Bilin V) (K : DisKinematics V) : ℝ :=
  K.Q2 g / (2 * g K.p K.q)

/-- The inelasticity variable `y := (p·q)/(p·k)`. -/
noncomputable def yInel (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g K.p K.q / g K.p K.k

/-- The hadronic invariant mass squared `W2 := (p + q)^2`. -/
def W2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (K.p + K.q) (K.p + K.q)

omit [Module ℝ V] in
lemma q_eq_sub (K : DisKinematics V) : K.q = K.k - K.kPrime := K.hq

omit [Module ℝ V] in
lemma kPrime_eq (K : DisKinematics V) : K.kPrime = K.k - K.q := by
  have hSub : K.k - K.q = K.kPrime := by
    calc
      K.k - K.q = K.k - (K.k - K.kPrime) := by rw [K.hq]
      _ = K.kPrime := by abel
  exact hSub.symm

/-- A direct expansion of `W2` in terms of bilinear pieces. -/
lemma W2_expand (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    K.W2 g = g K.p K.p + 2 * g K.p K.q + g K.q K.q := by
  unfold W2
  rw [Bilin.apply_add_self g hSymm]

/-- Rewrite `W2` using `Q2 = -q^2`. -/
lemma W2_eq_with_Q2 (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    K.W2 g = g K.p K.p + 2 * g K.p K.q - K.Q2 g := by
  rw [W2_expand g K hSymm]
  unfold Q2
  ring

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
