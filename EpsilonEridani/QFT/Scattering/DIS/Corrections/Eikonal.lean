/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.ChargedLegs

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

The charged legs `L`, their net charge `netCharge L = ∑ᵢ ηᵢ Qᵢ`, the charged lines and the legs
`Kinematics.DisKinematics.chargedLegs` of lepton–hadron scattering are defined in
`EpsilonEridani.QFT.Scattering.DIS.Kinematics.ChargedLegs`.

## Main definitions

* `eikonalCurrent g L ℓ`: the eikonal current `J(ℓ)`.

## Main statements

* `apply_eikonalCurrent`: `J(ℓ)·ℓ = ∑ᵢ ηᵢ Qᵢ`.
* `eikonalCurrent_conserved_of_netCharge_eq_zero`: charge conservation gives `J(ℓ)·ℓ = 0`.
* `eikonalCurrent_smul`: `J(c ℓ) = c⁻¹ J(ℓ)`, the homogeneity behind the logarithmic infrared
  divergence of `∫ dω/ω`.
* `apply_eikonalCurrent_eikonalCurrent`: the contraction `J_L·J_M` of the currents of two
  families of legs as a double sum over pairs of legs; for `M = L` this is `J·J`.
* `eikonalCurrent_sumElim`: the current of a union of legs is the sum of the currents, so the
  current of a scattering process splits into a lepton current and a hadron current.
* `eikonalCurrent_chargedLegs_conserved`: the eikonal current of lepton–hadron scattering
  satisfies `J(ℓ)·ℓ = 0`.

## References

* D. R. Yennie, S. C. Frautschi and H. Suura, *The infrared divergence phenomena and high-energy
  processes*, Ann. Phys. 13 (1961) 379.
* S. Weinberg, *Infrared photons and gravitons*, Phys. Rev. 140 (1965) B516.
* S. Weinberg, *The Quantum Theory of Fields*, Vol. I, §13.1.
-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Corrections

open Kinematics

variable {V : Type} {ι κ : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℝ V]

/-- The **eikonal current** `J(ℓ) = ∑ᵢ ηᵢ Qᵢ pᵢ / (pᵢ·ℓ)` of the charged legs `L` for a soft
photon of momentum `ℓ`, with scalar products taken with `g`. -/
noncomputable def eikonalCurrent (g : Bilin V) (L : ι → ChargedLeg V) (ℓ : V) : V :=
  ∑ i, ((L i).signedCharge / g (L i).momentum ℓ) • (L i).momentum

/-- The eikonal current contracted with the photon momentum equals the net charge, provided no leg
is orthogonal to `ℓ`. -/
theorem apply_eikonalCurrent (g : Bilin V) (L : ι → ChargedLeg V) (ℓ : V)
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
  rw [apply_eikonalCurrent g L ℓ hL, hQ]

/-- The eikonal current is homogeneous of degree `-1` in the photon momentum:
`J(c ℓ) = c⁻¹ J(ℓ)`. Integrated over the photon energy this is the origin of the logarithmic
infrared divergence. -/
theorem eikonalCurrent_smul (g : Bilin V) (L : ι → ChargedLeg V) (c : ℝ) (ℓ : V) :
    eikonalCurrent g L (c • ℓ) = c⁻¹ • eikonalCurrent g L ℓ := by
  simp only [eikonalCurrent, map_smul, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring

/-- The contraction of the eikonal currents of two families of legs as a double sum over pairs of
legs: `J_L·J_M = ∑ᵢ ∑ⱼ ηᵢ Qᵢ ηⱼ Qⱼ (pᵢ·pⱼ) / ((pᵢ·ℓ)(pⱼ·ℓ))`. For `M = L` this is the square
`J·J`. -/
theorem apply_eikonalCurrent_eikonalCurrent (g : Bilin V) (L : ι → ChargedLeg V)
    (M : κ → ChargedLeg V) (ℓ : V) :
    g (eikonalCurrent g L ℓ) (eikonalCurrent g M ℓ) =
      ∑ i, ∑ j, (L i).signedCharge * (M j).signedCharge * g (L i).momentum (M j).momentum /
        (g (L i).momentum ℓ * g (M j).momentum ℓ) := by
  simp only [eikonalCurrent, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The eikonal current of a union of two families of legs is the sum of their currents. -/
@[simp] theorem eikonalCurrent_sumElim (g : Bilin V) (L₁ : ι → ChargedLeg V)
    (L₂ : κ → ChargedLeg V) (ℓ : V) :
    eikonalCurrent g (Sum.elim L₁ L₂) ℓ = eikonalCurrent g L₁ ℓ + eikonalCurrent g L₂ ℓ := by
  simp [eikonalCurrent, Fintype.sum_sum_type]

/-- The eikonal current of a charged line: `J(ℓ) = Q (p' / (p'·ℓ) - p / (p·ℓ))`. -/
@[simp] theorem eikonalCurrent_chargedLine (g : Bilin V) (p p' : V) (Q : ℝ) (ℓ : V) :
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

/-- The eikonal current of lepton–hadron scattering is the sum of the lepton current and
the hadron current. -/
@[simp] theorem eikonalCurrent_chargedLegs (g : Bilin V) (K : DisKinematics V)
    (eLepton eHadron : ℝ) (ℓ : V) :
    eikonalCurrent g (K.chargedLegs eLepton eHadron) ℓ =
      eikonalCurrent g (chargedLine K.k K.kPrime eLepton) ℓ +
        eikonalCurrent g (chargedLine K.p K.pPrime eHadron) ℓ :=
  eikonalCurrent_sumElim g _ _ ℓ

/-- **Conservation of the eikonal current of lepton–hadron scattering**: `J(ℓ)·ℓ = 0`
whenever none of the four external momenta is orthogonal to `ℓ`. -/
theorem eikonalCurrent_chargedLegs_conserved (g : Bilin V) (K : DisKinematics V)
    (eLepton eHadron : ℝ) (ℓ : V) (hk : g K.k ℓ ≠ 0) (hk' : g K.kPrime ℓ ≠ 0)
    (hp : g K.p ℓ ≠ 0) (hp' : g K.pPrime ℓ ≠ 0) :
    g (eikonalCurrent g (K.chargedLegs eLepton eHadron) ℓ) ℓ = 0 := by
  rw [eikonalCurrent_chargedLegs, map_add, LinearMap.add_apply,
    eikonalCurrent_chargedLine_conserved g _ _ _ ℓ hk hk',
    eikonalCurrent_chargedLine_conserved g _ _ _ ℓ hp hp', add_zero]

end Kinematics.DisKinematics

end DIS
end Scattering
end QFT
end EpsilonEridani
