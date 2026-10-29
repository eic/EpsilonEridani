/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic
/-!

# Diffractive Deep Inelastic Scattering Kinematics

This module introduces the kinematics of diffractive DIS: events in which the target either
stays intact or dissociates into a low-mass system, identified by a large rapidity gap.

A diffractive event `P + q = P' + X` has a distinguished outgoing target-like momentum `P'`.
The variables `ξ`, `β` and `M_Y²` are functions of `q`, `P`, `P'` alone, so they are stated on the
inclusive record `DisKinematics`, whose `pPrime` field carries `P'`; the identity `x = ξ β` is
then a statement about the inclusive Bjorken variable `DisKinematics.xBj` of the same record. The
mass `M_X²` of the remaining system `X` is stated on the exclusive-type record `ExclKinematics`,
whose `qPrime` field carries the momentum of `X` and whose momentum-conservation law gives the
defining form `M_X² = (q + Δ)²`. The invariant momentum transfer `t = Δ²` is
`ExclKinematics.tMom`.

Following the conventions of [Wolf, *Rept. Prog. Phys.* **73** (2010) 116202] and
the EIC Yellow Report §7.1.6.

## Main definitions

* `Diffractive.xi`: the momentum fraction lost by the target, `ξ = Δ·q / P·q` with
  `Δ = P - P'`.
* `Diffractive.beta`: the parton's fraction of the exchange, `β = Q² / (2 Δ·q)`.
* `Diffractive.MY2`: the invariant mass squared `M_Y² = P'²` of the target-like system.
* `Diffractive.MX2`: the invariant mass squared of the diffractive system `X`.

## Main results

* `Diffractive.MX2_eq_q_sub_delta_sq`: `M_X² = (q + Δ)²`.
* `Diffractive.xBj_eq_xi_mul_beta`: the key identity `x = ξ β` relating the inclusive Bjorken
  variable to the diffractive variables, as an exact cancellation requiring no mass or
  high-energy approximation.

## References

* EIC Yellow Report §7.1.6
* Wolf, *Rept. Prog. Phys.* **73** (2010) 116202, §2
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)
open EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics (ExclKinematics)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-!
## The diffractive variables

The target with incoming momentum `p` absorbs the virtual photon `q` and emerges as the
surviving target-like momentum `pPrime`, together with the remaining system `X`. The momentum
transfer to the target is `Δ = P - P'`, written inline as `K.p - K.pPrime`.
-/

/-- The variable `ξ = Δ·q / P·q`, the momentum fraction lost by the target, where
`Δ = P - P'` is the momentum transfer to the target. This is the diffractive momentum fraction,
not the skewness `ExclKinematics.xiSkew` of the exclusive channels. Like any real division in
Lean, it is `0` when the denominator vanishes. -/
noncomputable def xi (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (K.p - K.pPrime) K.q / g K.p K.q

lemma xi_def (g : Bilin V) (K : DisKinematics V) :
    xi g K = g (K.p - K.pPrime) K.q / g K.p K.q := (rfl)

/-- The variable `β = Q² / (2 Δ·q)`, the parton's fraction of the exchange, where
`Δ = P - P'` is the momentum transfer to the target. Like any real division in Lean, it is `0`
when the denominator vanishes. -/
noncomputable def beta (g : Bilin V) (K : DisKinematics V) : ℝ :=
  K.Q2 g / (2 * g (K.p - K.pPrime) K.q)

lemma beta_def (g : Bilin V) (K : DisKinematics V) :
    beta g K = K.Q2 g / (2 * g (K.p - K.pPrime) K.q) := (rfl)

/-- The invariant mass squared of the surviving target-like system, `M_Y² = P'²`. -/
def MY2 (g : Bilin V) (K : DisKinematics V) : ℝ := g K.pPrime K.pPrime

lemma MY2_def (g : Bilin V) (K : DisKinematics V) :
    MY2 g K = g K.pPrime K.pPrime := (rfl)

/-- The invariant mass squared of the diffractive system `X`, `M_X² = q'²`: by the momentum
conservation `p + q = p' + q'` of `ExclKinematics.hMomentum` the remaining system carries the
momentum `q' = q + Δ` (see `MX2_eq_q_sub_delta_sq`). -/
def MX2 (g : Bilin V) (K : ExclKinematics V) : ℝ := g K.qPrime K.qPrime

lemma MX2_def (g : Bilin V) (K : ExclKinematics V) :
    MX2 g K = g K.qPrime K.qPrime := (rfl)

/-- The invariant mass squared of the diffractive system in its defining form `M_X² = (q + Δ)²`,
with `Δ = P - P' = -ExclKinematics.delta`. -/
lemma MX2_eq_q_sub_delta_sq (g : Bilin V) (K : ExclKinematics V) :
    MX2 g K = g (K.q - K.delta) (K.q - K.delta) := by
  rw [MX2_def, ExclKinematics.delta_eq_q_sub_qPrime, sub_sub_cancel]

/-!
### The key identity: `x = ξ β`

`x = ξ β` is what justifies calling `β` a momentum fraction of the exchange.
-/

/-- The identity `x = ξ β` relating the inclusive Bjorken variable `x` of the event to the
diffractive variables `ξ` and `β`. This is an exact cancellation requiring no mass or
high-energy approximation. The cancellation needs the momentum transfer `Δ = P - P'` to have
`Δ·q ≠ 0`; when `P·q = 0` both sides vanish, so no non-degeneracy of `P·q` is needed. -/
theorem xBj_eq_xi_mul_beta (g : Bilin V) (K : DisKinematics V)
    (hDeltaq : g (K.p - K.pPrime) K.q ≠ 0) :
    K.xBj g = xi g K * beta g K := by
  rw [DisKinematics.xBj, xi_def, beta_def]
  rcases eq_or_ne (g K.p K.q) 0 with hPq | hPq
  · simp [hPq]
  · field_simp

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
