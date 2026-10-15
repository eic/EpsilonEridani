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

A diffractive event `P + q = P' + X` is an exclusive-type event: it is carried by the
`ExclKinematics` record, whose `pPrime` field is the surviving target-like momentum `P'` and
whose `qPrime` field is the momentum of the remaining system `X`. No data beyond the
exclusive record is needed, so the diffractive variables are defined directly on
`ExclKinematics`: the inclusive variables (`x`, `Q²`, `y`) apply through
`ExclKinematics.toDisKinematics`, and the invariant momentum transfer `t = Δ²` is the
momentum-transfer invariant `ExclKinematics.tMom` of the hadronic vertex.

Following the conventions of [Wolf, *Rept. Prog. Phys.* **73** (2010) 116202] and
the EIC Yellow Report §7.1.6.

## Main definitions

* `xi`: the momentum fraction lost by the target, `ξ = Δ·q / P·q` with `Δ = P - P'`.
* `beta`: the parton's fraction of the exchange, `β = Q² / (2 Δ·q)`.
* `MX2`: the invariant mass squared of the diffractive system `X`.

## Main results

* `x_eq_xi_mul_beta`: the key identity `x = ξ β` relating the inclusive Bjorken variable to
the diffractive variables, as an exact cancellation requiring no mass or high-energy
approximation.

## References

* EIC Yellow Report §7.1.6
* Wolf, *Rept. Prog. Phys.* **73** (2010) 116202, §2
-/

@[expose] public section

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

A diffractive DIS event is an exclusive-type event `P + q = P' + X` carried by the
`ExclKinematics` record: the target with incoming momentum `p` absorbs the virtual photon `q`
and emerges as the surviving target-like momentum `pPrime` together with the remaining system
`X`, carried by the `qPrime` field. The diffractive variables below are therefore stated
directly on `ExclKinematics`. The momentum transfer to the target is `Δ = P - P'`, the
negative of `ExclKinematics.delta = P' - P`; its square is the invariant momentum transfer
`t = Δ²` carried by `ExclKinematics.tMom`.
-/

/-- The variable `ξ = Δ·q / P·q`, the momentum fraction lost by the target, where
`Δ = P - P'` is the momentum transfer to the target, the negative of `ExclKinematics.delta`.
Like any real division in Lean, it is `0` when the denominator vanishes. -/
noncomputable def xi (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  -g K.delta K.q / g K.p K.q

/-- The variable `β = Q² / (2 Δ·q)`, the parton's fraction of the exchange, where
`Δ = P - P'` is the momentum transfer to the target, the negative of `ExclKinematics.delta`.
Like any real division in Lean, it is `0` when the denominator vanishes. -/
noncomputable def beta (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  K.Q2 g / (2 * -g K.delta K.q)

/-- The invariant mass squared of the diffractive system `X`, `M_X² = q'²`: by the momentum
conservation `p + q = p' + q'` of `ExclKinematics.hMomentum` the remaining system carries the
momentum `q' = q + Δ`. -/
def MX2 (g : Bilin V) (K : ExclKinematics V) : ℝ := g K.qPrime K.qPrime

@[simp]
lemma MX2_def (g : Bilin V) (K : ExclKinematics V) :
    MX2 g K = g K.qPrime K.qPrime := rfl

/-!
### The key identity: `x = ξ β`

This is the single most important identity in the layer.
-/

/-- The identity `x = ξ β` relating the inclusive Bjorken variable `x` of the event to the
diffractive variables `ξ` and `β`. This is an exact cancellation requiring no mass or
high-energy approximation. The cancellation needs the momentum transfer `Δ = P - P'` to have
`Δ·q ≠ 0`, i.e. `ExclKinematics.delta·q ≠ 0`; when `P·q = 0` both sides vanish, so no
non-degeneracy of `P·q` is needed. -/
theorem x_eq_xi_mul_beta (g : Bilin V) (K : ExclKinematics V)
    (hdeltaq : g K.delta K.q ≠ 0) :
    K.toDisKinematics.xBj g = xi g K * beta g K := by
  unfold DisKinematics.xBj ExclKinematics.toDisKinematics xi beta DisKinematics.Q2
    ExclKinematics.Q2
  rcases eq_or_ne (g K.p K.q) 0 with hPq | hPq
  · simp [hPq]
  · field_simp

end Diffractive

end DIS
end Scattering
end QFT
end EpsilonEridani
