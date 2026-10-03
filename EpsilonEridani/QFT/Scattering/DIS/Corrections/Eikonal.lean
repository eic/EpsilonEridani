/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic

/-!
# The eikonal current of soft-photon emission

When a photon of momentum `ℓ` is radiated from an external charged leg of momentum `p` and charge
`Q`, and `ℓ` is soft compared with every external momentum, the emission amplitude factorises
into the amplitude without the photon times the eikonal factor `η Q p^μ / (p·ℓ)`, where the sign
`η` is `+1` for an outgoing and `-1` for an incoming leg. Summed over the charged legs of a process
this is the eikonal current

  `J^μ(ℓ) = ∑ᵢ ηᵢ Qᵢ pᵢ^μ / (pᵢ·ℓ)`.

Its square `J(ℓ)·J(ℓ)`, integrated over the soft region, is the infrared exponent of the
Yennie–Frautschi–Suura exponentiation, and its contraction with the photon momentum is the
eikonal form of the Ward identity: `J(ℓ)·ℓ = ∑ᵢ ηᵢ Qᵢ`, which vanishes exactly when the charge
flowing out of the process equals the charge flowing in. This is the gauge invariance of the
soft-photon factor.

Scalar products are taken with an arbitrary bilinear form `g` in the sense of
`EpsilonEridani.QFT.Scattering.DIS.Kinematics.Bilin`; nothing here uses its signature. A leg
orthogonal to `ℓ` contributes `0` (division by zero), so the results that depend on the
denominators assume each `pᵢ·ℓ` to be non-zero.

## Main definitions

* `LegDirection`, `LegDirection.sign`: incoming or outgoing, with the sign `η = ∓1`.
* `ChargedLeg`: the momentum, charge and direction of an external charged leg, and
  `ChargedLeg.signedCharge`, the product `η Q`.
* `netCharge L`: the net outgoing charge `∑ᵢ ηᵢ Qᵢ` of a family of legs.
* `eikonalCurrent g L ℓ`: the eikonal current `J(ℓ)`.
* `chargedLine p p' Q`: a charged particle entering the hard scattering with momentum `p` and
  leaving it with momentum `p'`.
* `Kinematics.DisKinematics.elasticLegs`: the lepton line and the hadron line of elastic
  lepton–hadron scattering.

## Main statements

* `eikonalCurrent_conserved`: `J(ℓ)·ℓ = ∑ᵢ ηᵢ Qᵢ`.
* `eikonalCurrent_conserved_of_netCharge_eq_zero`: charge conservation gives `J(ℓ)·ℓ = 0`.
* `eikonalCurrent_smul`: `J(c ℓ) = c⁻¹ J(ℓ)`, the homogeneity behind the logarithmic infrared
  divergence of `∫ dω/ω`.
* `apply_eikonalCurrent_eikonalCurrent`: `J·J` as a double sum over pairs of legs.
* `eikonalCurrent_sumElim`: the current of a union of legs is the sum of the currents, so the
  current of a scattering process splits into a lepton current and a hadron current.
* `eikonalCurrent_elasticLegs_conserved`: the eikonal current of elastic lepton–hadron scattering
  satisfies `J(ℓ)·ℓ = 0`, and so does each of its lepton and hadron parts separately.

## References

* D. R. Yennie, S. C. Frautschi and H. Suura, *The infrared divergence phenomena and high-energy
  processes*, Ann. Phys. 13 (1961) 379.
* S. Weinberg, *Infrared photons and gravitons*, Phys. Rev. 140 (1965) B516.
* S. Weinberg, *The Quantum Theory of Fields*, Vol. I, §13.1.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Corrections

open Kinematics

/-- Whether an external leg of a scattering process is incoming or outgoing. -/
inductive LegDirection
  /-- The leg enters the process. -/
  | incoming
  /-- The leg leaves the process. -/
  | outgoing
  deriving DecidableEq

namespace LegDirection

/-- The sign `η` of a leg in the eikonal current: `-1` for incoming and `+1` for outgoing. -/
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

theorem signedCharge_def (L : ChargedLeg V) : L.signedCharge = L.direction.sign * L.charge :=
  (rfl)

@[simp] theorem signedCharge_mk (p : V) (Q : ℝ) (d : LegDirection) :
    (ChargedLeg.mk p Q d).signedCharge = d.sign * Q := (rfl)

end ChargedLeg

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The net charge `∑ᵢ ηᵢ Qᵢ` flowing out of a process with charged legs `L`: the outgoing charge
minus the incoming charge. Charge conservation is the statement that it vanishes. -/
noncomputable def netCharge (L : ι → ChargedLeg V) : ℝ := ∑ i, (L i).signedCharge

theorem netCharge_def (L : ι → ChargedLeg V) : netCharge L = ∑ i, (L i).signedCharge := (rfl)

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

variable [AddCommGroup V] [Module ℝ V]

/-- The **eikonal current** `J(ℓ) = ∑ᵢ ηᵢ Qᵢ pᵢ / (pᵢ·ℓ)` of the charged legs `L` for a soft
photon of momentum `ℓ`, with scalar products taken with `g`. -/
noncomputable def eikonalCurrent (g : Bilin V) (L : ι → ChargedLeg V) (ℓ : V) : V :=
  ∑ i, ((L i).signedCharge / g (L i).momentum ℓ) • (L i).momentum

theorem eikonalCurrent_def (g : Bilin V) (L : ι → ChargedLeg V) (ℓ : V) :
    eikonalCurrent g L ℓ = ∑ i, ((L i).signedCharge / g (L i).momentum ℓ) • (L i).momentum :=
  (rfl)

/-- **Conservation of the eikonal current**: `J(ℓ)·ℓ` is the net outgoing charge, provided no leg
is orthogonal to `ℓ`. -/
theorem eikonalCurrent_conserved (g : Bilin V) (L : ι → ChargedLeg V) (ℓ : V)
    (hL : ∀ i, g (L i).momentum ℓ ≠ 0) :
    g (eikonalCurrent g L ℓ) ℓ = netCharge L := by
  simp only [eikonalCurrent, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, netCharge]
  exact Finset.sum_congr rfl fun i _ => div_mul_cancel₀ _ (hL i)

/-- For a process that conserves charge, the eikonal current is orthogonal to the photon
momentum, `J(ℓ)·ℓ = 0`. This is the gauge invariance of the soft-photon factor. -/
theorem eikonalCurrent_conserved_of_netCharge_eq_zero (g : Bilin V) (L : ι → ChargedLeg V)
    (ℓ : V) (hL : ∀ i, g (L i).momentum ℓ ≠ 0) (hQ : netCharge L = 0) :
    g (eikonalCurrent g L ℓ) ℓ = 0 := by
  rw [eikonalCurrent_conserved g L ℓ hL, hQ]

/-- The eikonal current is homogeneous of degree `-1` in the photon momentum:
`J(c ℓ) = c⁻¹ J(ℓ)`. Integrated over the photon energy this is the origin of the logarithmic
infrared divergence. -/
theorem eikonalCurrent_smul (g : Bilin V) (L : ι → ChargedLeg V) (c : ℝ) (ℓ : V) :
    eikonalCurrent g L (c • ℓ) = c⁻¹ • eikonalCurrent g L ℓ := by
  simp only [eikonalCurrent, map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_mul_eq_div_div_swap, div_eq_mul_inv _ c, mul_comm _ c⁻¹]

/-- The square of the eikonal current as a sum over ordered pairs of legs:
`J·J = ∑ᵢ ∑ⱼ ηᵢ Qᵢ ηⱼ Qⱼ (pᵢ·pⱼ) / ((pᵢ·ℓ)(pⱼ·ℓ))`. -/
theorem apply_eikonalCurrent_eikonalCurrent (g : Bilin V) (L : ι → ChargedLeg V) (ℓ : V) :
    g (eikonalCurrent g L ℓ) (eikonalCurrent g L ℓ) =
      ∑ i, ∑ j, (L i).signedCharge * (L j).signedCharge * g (L i).momentum (L j).momentum /
        (g (L i).momentum ℓ * g (L j).momentum ℓ) := by
  simp only [eikonalCurrent, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The eikonal current of a union of two families of legs is the sum of their currents. -/
theorem eikonalCurrent_sumElim (g : Bilin V) (L₁ : ι → ChargedLeg V) (L₂ : κ → ChargedLeg V)
    (ℓ : V) :
    eikonalCurrent g (Sum.elim L₁ L₂) ℓ = eikonalCurrent g L₁ ℓ + eikonalCurrent g L₂ ℓ := by
  simp [eikonalCurrent, Fintype.sum_sum_type]

/-- The eikonal current of a charged line: `J(ℓ) = Q (p' / (p'·ℓ) - p / (p·ℓ))`. -/
theorem eikonalCurrent_chargedLine (g : Bilin V) (p p' : V) (Q : ℝ) (ℓ : V) :
    eikonalCurrent g (chargedLine p p' Q) ℓ = Q • ((g p' ℓ)⁻¹ • p' - (g p ℓ)⁻¹ • p) := by
  simp only [eikonalCurrent, chargedLine, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, ChargedLeg.signedCharge_mk, LegDirection.sign_incoming,
    LegDirection.sign_outgoing, smul_sub, smul_smul]
  rw [sub_eq_neg_add, ← neg_smul]
  congr 2 <;> ring

/-- The eikonal current of a single charged line is conserved by itself: `J(ℓ)·ℓ = 0` whenever
neither momentum of the line is orthogonal to `ℓ`. -/
theorem eikonalCurrent_chargedLine_conserved (g : Bilin V) (p p' : V) (Q : ℝ) (ℓ : V)
    (hp : g p ℓ ≠ 0) (hp' : g p' ℓ ≠ 0) :
    g (eikonalCurrent g (chargedLine p p' Q) ℓ) ℓ = 0 :=
  eikonalCurrent_conserved_of_netCharge_eq_zero g _ ℓ
    (fun i => by fin_cases i <;> simpa [chargedLine]) (netCharge_chargedLine p p' Q)

end Corrections

namespace Kinematics.DisKinematics

open Corrections

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The charged legs of elastic lepton–hadron scattering with the kinematics `K`: the lepton line
from `K.k` to `K.kPrime` with charge `eLepton`, and the hadron line from `K.p` to `K.pPrime` with
charge `eHadron`. -/
def elasticLegs (K : DisKinematics V) (eLepton eHadron : ℝ) : Fin 2 ⊕ Fin 2 → ChargedLeg V :=
  Sum.elim (chargedLine K.k K.kPrime eLepton) (chargedLine K.p K.pPrime eHadron)

omit [Module ℝ V] in
theorem elasticLegs_def (K : DisKinematics V) (eLepton eHadron : ℝ) :
    K.elasticLegs eLepton eHadron =
      Sum.elim (chargedLine K.k K.kPrime eLepton) (chargedLine K.p K.pPrime eHadron) :=
  (rfl)

omit [Module ℝ V] in
/-- Elastic lepton–hadron scattering conserves charge. -/
@[simp] theorem netCharge_elasticLegs (K : DisKinematics V) (eLepton eHadron : ℝ) :
    netCharge (K.elasticLegs eLepton eHadron) = 0 := by
  simp [elasticLegs]

/-- The eikonal current of elastic lepton–hadron scattering is the sum of the lepton current and
the hadron current. -/
theorem eikonalCurrent_elasticLegs (g : Bilin V) (K : DisKinematics V) (eLepton eHadron : ℝ)
    (ℓ : V) :
    eikonalCurrent g (K.elasticLegs eLepton eHadron) ℓ =
      eikonalCurrent g (chargedLine K.k K.kPrime eLepton) ℓ +
        eikonalCurrent g (chargedLine K.p K.pPrime eHadron) ℓ :=
  eikonalCurrent_sumElim g _ _ ℓ

/-- **Conservation of the eikonal current of elastic lepton–hadron scattering**: `J(ℓ)·ℓ = 0`
whenever none of the four external momenta is orthogonal to `ℓ`. -/
theorem eikonalCurrent_elasticLegs_conserved (g : Bilin V) (K : DisKinematics V)
    (eLepton eHadron : ℝ) (ℓ : V) (hk : g K.k ℓ ≠ 0) (hk' : g K.kPrime ℓ ≠ 0)
    (hp : g K.p ℓ ≠ 0) (hp' : g K.pPrime ℓ ≠ 0) :
    g (eikonalCurrent g (K.elasticLegs eLepton eHadron) ℓ) ℓ = 0 := by
  rw [eikonalCurrent_elasticLegs, map_add, LinearMap.add_apply,
    eikonalCurrent_chargedLine_conserved g _ _ _ ℓ hk hk',
    eikonalCurrent_chargedLine_conserved g _ _ _ ℓ hp hp', add_zero]

end Kinematics.DisKinematics

end DIS
end Scattering
end QFT
end EpsilonEridani
