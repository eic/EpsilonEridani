/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# Diffractive Deep Inelastic Scattering Kinematics

This module introduces the kinematics of diffractive DIS: events in which the target either
stays intact or dissociates into a low-mass system, identified by a large rapidity gap.

Following the conventions of [Wolf, *Rept. Prog. Phys.* **73** (2010) 116202] and
the EIC Yellow Report §7.1.6.

## Main definitions

* `DiffractiveKinematics`: the data of a diffractive DIS event with an identified surviving
  target-like momentum `P'` and the mass of the remaining system.
* `xi`: the momentum fraction lost by the target, `ξ = Δ·q / P·q`.
* `beta`: the parton's fraction of the exchange, `β = Q² / (2 Δ·q)`.
* `t`: the invariant momentum transfer to the target, `t = Δ²`.
* `MX2`: the invariant mass squared of the diffractive system `X`.

## Main results

* `xi_beta_eq_x`: the key identity `x = ξ β` relating the inclusive Bjorken variable to
the diffractive variables ("the single most important identity in the layer", proved as a
two-line cancellation).

## References

* EIC Yellow Report §7.1.6
* Wolf, *Rept. Prog. Phys.* **73** (2010) 116202, §2
-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS

/-!
## Diffractive kinematics record

A diffractive DIS event is identified by, in addition to the inclusive kinematics `K`,
a surviving target-like momentum `P'` and the invariant mass squared `MX2` of the
remaining system `X`.
-/

variable (V : Type) [AddCommGroup V] [Module ℝ V]

open EpsilonEridani.QFT.Scattering.DIS.Kinematics

/-- Diffractive DIS kinematics: the data of a diffractive event. -/
structure DiffractiveKinematics (V : Type) [AddCommGroup V] [Module ℝ V] where
  /-- Inclusive DIS kinematics (provides `p`, `k`, `q`, `q = k - kPrime`). -/
  K : DisKinematics V
  /-- The surviving target-like four-momentum. -/
  P' : V
  /-- The invariant mass squared of the remaining system `X`, i.e. `(q + P - P')²`. -/
  MX2 : ℝ

namespace DiffractiveKinematics

variable {V} [AddCommGroup V] [Module ℝ V]

/-- The momentum transfer to the target: `Δ = P - P'`. -/
def Delta (D : DiffractiveKinematics V) : V := D.K.p - D.P'

@[simp]
lemma hDelta (D : DiffractiveKinematics V) : D.Delta = D.K.p - D.P' := rfl

/-- The invariant momentum transfer `t = Δ²`. -/
def t (D : DiffractiveKinematics V) (g : Bilin V) : ℝ := g D.Delta D.Delta

omit [AddCommGroup V] [Module ℝ V] in
@[simp]
lemma h_t (D : DiffractiveKinematics V) (g : Bilin V) : D.t g = g D.Delta D.Delta := rfl

/-- The variable `ξ = Δ·q / P·q`. -/
noncomputable def xi (D : DiffractiveKinematics V) (g : Bilin V) : ℝ :=
  g D.Delta D.K.q / g D.K.p D.K.q

/-- The variable `β = Q² / (2 Δ·q)`. -/
noncomputable def beta (D : DiffractiveKinematics V) (g : Bilin V) : ℝ :=
  D.K.Q2 g / (2 * g D.Delta D.K.q)

/-!
### The key identity: `x = ξ β`

This is the single most important identity in the layer, proved as a two-line cancellation.
-/

/-- The identity `x = ξ β` relating the inclusive Bjorken variable `x` to the diffractive
variables `ξ` and `β`. This is an exact cancellation requiring no mass or high-energy
approximation. -/
theorem xi_beta_eq_x (D : DiffractiveKinematics V) (g : Bilin V)
    (hPq : g D.K.p D.K.q ≠ 0) (hDeltaq : g D.Delta D.K.q ≠ 0) :
    D.K.xBj g = D.xi g * D.beta g := by
  unfold DisKinematics.xBj xi beta
  dsimp [DisKinematics.Q2]
  field_simp [hPq, hDeltaq]
  ring_nf

end DiffractiveKinematics

end DIS
end Scattering
end QFT
end EpsilonEridani
