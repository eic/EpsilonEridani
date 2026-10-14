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
`ExclKinematics` record, whose `qPrime` field is the momentum of the remaining system `X`.
The inclusive variables (`x`, `Q²`, `y`) therefore apply through
`ExclKinematics.toDisKinematics`, and the invariant momentum transfer `t = Δ²` is the
momentum-transfer invariant `ExclKinematics.tMom` of the hadronic vertex.

Following the conventions of [Wolf, *Rept. Prog. Phys.* **73** (2010) 116202] and
the EIC Yellow Report §7.1.6.

## Main definitions

* `DiffractiveKinematics`: the data of a diffractive DIS event, as an exclusive-type event
  `P + q = P' + X` whose `qPrime` field is the momentum of the remaining system `X`.
* `Delta`: the momentum transfer to the target, `Δ = P - P'`.
* `xi`: the momentum fraction lost by the target, `ξ = Δ·q / P·q`.
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

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)
open EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics (ExclKinematics)

/-!
## Diffractive kinematics record

A diffractive DIS event is an exclusive-type event: the target with incoming momentum `p`
absorbs the virtual photon `q` and emerges as the surviving target-like momentum `pPrime`
together with the remaining system `X`, carried by the inherited `qPrime` field. No data
beyond the exclusive record is needed at this layer.
-/

variable (V : Type) [AddCommGroup V] [Module ℝ V]

/-- Diffractive DIS kinematics: an event in which the target either stays intact or
dissociates into a low-mass system. The event extends `ExclKinematics`: the inherited
`pPrime` field is the surviving target-like momentum `P'`, the inherited `qPrime` field is
the momentum of the remaining system `X` (so `M_X² = q'²` is `MX2`), the invariant momentum
transfer `t = Δ²` is `ExclKinematics.tMom`, and the inclusive variables apply through
`ExclKinematics.toDisKinematics`. -/
structure DiffractiveKinematics (V : Type) [AddCommGroup V] [Module ℝ V] extends
  ExclKinematics V

namespace DiffractiveKinematics

variable {V}

/-- The momentum transfer to the target, `Δ = P - P'`, the negative of the exclusive
`ExclKinematics.delta = P' - P`. Its square is the invariant momentum transfer `t = Δ²`
carried by `ExclKinematics.tMom`. -/
def Delta (D : DiffractiveKinematics V) : V := -D.delta

@[simp]
lemma Delta_def (D : DiffractiveKinematics V) : D.Delta = -D.delta := rfl

/-- The momentum transfer to the target on the photon side of the hadronic vertex,
`Δ = q' - q`, with `q'` the momentum of the system `X`. This is the diffractive counterpart
of `ExclKinematics.delta_eq_q_sub_qPrime`. -/
lemma Delta_eq_qPrime_sub_q (D : DiffractiveKinematics V) : D.Delta = D.qPrime - D.q := by
  rw [Delta_def, ExclKinematics.delta_eq_q_sub_qPrime, neg_sub]

/-- The variable `ξ = Δ·q / P·q`. Like any real division in Lean, it is `0` when the
denominator vanishes. -/
noncomputable def xi (g : Bilin V) (D : DiffractiveKinematics V) : ℝ :=
  g D.Delta D.q / g D.p D.q

/-- The variable `β = Q² / (2 Δ·q)`. Like any real division in Lean, it is `0` when the
denominator vanishes. -/
noncomputable def beta (g : Bilin V) (D : DiffractiveKinematics V) : ℝ :=
  D.Q2 g / (2 * g D.Delta D.q)

/-- The invariant mass squared of the diffractive system `X`, `M_X² = q'²`: by the inherited
momentum conservation `p + q = p' + q'` the remaining system carries the momentum
`q' = q + Δ`. -/
def MX2 (g : Bilin V) (D : DiffractiveKinematics V) : ℝ := g D.qPrime D.qPrime

@[simp]
lemma MX2_def (g : Bilin V) (D : DiffractiveKinematics V) :
    D.MX2 g = g D.qPrime D.qPrime := rfl

/-!
### The key identity: `x = ξ β`

This is the single most important identity in the layer.
-/

/-- The identity `x = ξ β` relating the inclusive Bjorken variable `x` of the event to the
diffractive variables `ξ` and `β`. This is an exact cancellation requiring no mass or
high-energy approximation. The cancellation needs the scalar product `Δ·q` to be non-zero;
when `P·q = 0` both sides vanish, so no non-degeneracy of `P·q` is needed. -/
theorem x_eq_xi_mul_beta (g : Bilin V) (D : DiffractiveKinematics V)
    (hDeltaq : g D.Delta D.q ≠ 0) :
    D.toExclKinematics.toDisKinematics.xBj g = D.xi g * D.beta g := by
  unfold DisKinematics.xBj ExclKinematics.toDisKinematics xi beta DisKinematics.Q2
    ExclKinematics.Q2
  rcases eq_or_ne (g D.p D.q) 0 with hPq | hPq
  · simp [hPq]
  · field_simp

end DiffractiveKinematics

end DIS
end Scattering
end QFT
end EpsilonEridani
