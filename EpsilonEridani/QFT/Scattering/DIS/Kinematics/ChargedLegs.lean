/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic

/-!
# Charged external legs of a scattering process

An external charged leg of a scattering process is described by its momentum `p`, its charge `Q`
and whether it enters or leaves the process. The sign `η` is `+1` for an outgoing and `-1` for an
incoming leg, and `η Q` is the charge the leg carries out of the process. Summed over the legs this
is the net outgoing charge `∑ᵢ ηᵢ Qᵢ`, which vanishes for a process that conserves charge.

## Main definitions

* `LegDirection`, `LegDirection.sign`: incoming or outgoing, with the sign `η = ∓1`.
* `ChargedLeg`: the momentum, charge and direction of an external charged leg, and
  `ChargedLeg.signedCharge`, the product `η Q`.
* `netCharge L`: the net outgoing charge `∑ᵢ ηᵢ Qᵢ` of a family of legs.
* `chargedLine p p' Q`: a charged particle entering the hard scattering with momentum `p` and
  leaving it with momentum `p'`.
* `DisKinematics.chargedLegs`: the lepton line and the hadron line of lepton–hadron scattering.

## Main statements

* `netCharge_sumElim`: the net charge of a union of legs is the sum of the net charges.
* `netCharge_chargedLine`, `DisKinematics.netCharge_chargedLegs`: a charged line, and hence
  lepton–hadron scattering, conserves charge.
-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

/-- Whether an external leg of a scattering process is incoming or outgoing. -/
inductive LegDirection
  /-- The leg enters the process. -/
  | incoming
  /-- The leg leaves the process. -/
  | outgoing
  deriving DecidableEq

namespace LegDirection

/-- The sign `η` of a leg: `-1` for incoming and `+1` for outgoing. -/
noncomputable def sign : LegDirection → ℝ
  | incoming => -1
  | outgoing => 1

@[simp] theorem sign_incoming : incoming.sign = -1 := (rfl)

@[simp] theorem sign_outgoing : outgoing.sign = 1 := (rfl)

@[simp] theorem sign_mul_self (d : LegDirection) : d.sign * d.sign = 1 := by
  cases d <;> norm_num

end LegDirection

variable {V : Type}

/-- An external charged leg of a scattering process: its four-momentum, its electric charge in
units of the positron charge, and whether it is incoming or outgoing. -/
@[ext] structure ChargedLeg (V : Type) where
  /-- The four-momentum of the leg. -/
  momentum : V
  /-- The electric charge of the leg, in units of the positron charge. -/
  charge : ℝ
  /-- Whether the leg is incoming or outgoing. -/
  direction : LegDirection

namespace ChargedLeg

/-- The signed charge `η Q` of a leg: the charge it carries out of the process. -/
noncomputable def signedCharge (L : ChargedLeg V) : ℝ := L.direction.sign * L.charge

@[simp] theorem signedCharge_mk (p : V) (Q : ℝ) (d : LegDirection) :
    (ChargedLeg.mk p Q d).signedCharge = d.sign * Q := (rfl)

end ChargedLeg

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The net charge `∑ᵢ ηᵢ Qᵢ` flowing out of a process with charged legs `L`: the outgoing charge
minus the incoming charge. Charge conservation is the statement that it vanishes. -/
noncomputable def netCharge (L : ι → ChargedLeg V) : ℝ := ∑ i, (L i).signedCharge

/-- The net charge of a union of two families of legs is the sum of their net charges. -/
@[simp] theorem netCharge_sumElim (L₁ : ι → ChargedLeg V) (L₂ : κ → ChargedLeg V) :
    netCharge (Sum.elim L₁ L₂) = netCharge L₁ + netCharge L₂ := by
  simp [netCharge, Fintype.sum_sum_type]

/-- A charged particle passing through the hard scattering: it enters with momentum `p` and
charge `Q`, and leaves with momentum `p'` and the same charge. -/
def chargedLine (p p' : V) (Q : ℝ) : Fin 2 → ChargedLeg V :=
  ![⟨p, Q, .incoming⟩, ⟨p', Q, .outgoing⟩]

@[simp] theorem chargedLine_zero (p p' : V) (Q : ℝ) :
    chargedLine p p' Q 0 = ⟨p, Q, .incoming⟩ := (rfl)

@[simp] theorem chargedLine_one (p p' : V) (Q : ℝ) :
    chargedLine p p' Q 1 = ⟨p', Q, .outgoing⟩ := (rfl)

/-- A charged line carries no net charge out of the process. -/
@[simp] theorem netCharge_chargedLine (p p' : V) (Q : ℝ) : netCharge (chargedLine p p' Q) = 0 := by
  simp [netCharge, chargedLine]

namespace DisKinematics

variable [AddCommGroup V]

/-- The charged legs of lepton–hadron scattering with the kinematics `K`: the lepton line
from `K.k` to `K.kPrime` with charge `eLepton`, and the hadron line from `K.p` to `K.pPrime`
with charge `eHadron`. -/
def chargedLegs (K : DisKinematics V) (eLepton eHadron : ℝ) : Fin 2 ⊕ Fin 2 → ChargedLeg V :=
  Sum.elim (chargedLine K.k K.kPrime eLepton) (chargedLine K.p K.pPrime eHadron)

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
