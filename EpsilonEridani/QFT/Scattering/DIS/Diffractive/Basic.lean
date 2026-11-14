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

A diffractive event `P + q = P' + X` has a distinguished outgoing target-like momentum `P'`;
write `Δ = P - P'`. The variables `ξ`, `β`, `M_X²` and `M_Y²` are functions of `q`, `P`, `P'`
alone, so they are all stated on the inclusive record `DisKinematics`, whose `pPrime` field
carries `P'`; the identity `x = ξ β` is then a statement about the inclusive Bjorken variable
`DisKinematics.xBj` of the same record. By the momentum conservation `P + q = P' + q_X` of the
event, the remaining system `X` carries the momentum `q_X = q + Δ`, and its invariant mass
squared `M_X² = (q + Δ)²` is stated on the same record.

Following the conventions of [Wolf, *Rept. Prog. Phys.* **73** (2010) 116202] and
the EIC Yellow Report §7.1.6.

## Main definitions

* `Diffractive.xi`: the momentum fraction lost by the target, `ξ = Δ·q / P·q` with
  `Δ = P - P'`.
* `Diffractive.beta`: the parton's fraction of the exchange, `β = Q² / (2 Δ·q)`.
* `Diffractive.MY2`: the invariant mass squared `M_Y² = P'²` of the target-like system.
* `Diffractive.MX2`: the invariant mass squared `M_X² = (q + Δ)²` of the diffractive system `X`.

## Main results

* `Diffractive.MX2_expand`: the bilinear expansion of `M_X² = (q + Δ)²`, the diffractive
  counterpart of `DisKinematics.W2_expand`.
* `Diffractive.MX2_eq_with_Q2`: `M_X² = -Q² + 2 Δ·q + t`, with `t = Δ²` the invariant
  `DisKinematics.tMom`.
* `Diffractive.beta_eq_Q2_div_Q2_add_MX2_sub_tMom`: the exact relation
  `β = Q² / (Q² + M_X² - t)` between the parton fraction and the invariant mass of the
  diffractive system, and its inverse `Diffractive.MX2_eq_Q2_mul_inv_beta_sub_one_add_tMom`:
  `M_X² = Q² (1/β - 1) + t`.
* `Diffractive.xi_congr`, `Diffractive.beta_congr`: `ξ` and `β` depend on the record only
  through `q`, `P` and `P'`.
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

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-!
## The diffractive variables

The target with incoming momentum `p` emits a colour-singlet exchange and emerges as the
surviving momentum `pPrime`; the exchange and the virtual photon `q` form the system `X`, so
`P + q = P' + q_X`. The momentum lost by the target (carried by the colour-singlet exchange) is
`Δ = P - P'`, written inline as `K.p - K.pPrime`.
-/

/-- The variable `ξ = Δ·q / P·q`, the momentum fraction lost by the target, where `Δ = P - P'`
is the momentum lost by the target (carried by the colour-singlet exchange), the negative of
`ExclKinematics.delta`. This is the diffractive momentum fraction, not the skewness
`ExclKinematics.xiSkew` of the exclusive channels. Like any real division in Lean, it is `0`
when the denominator vanishes. -/
noncomputable def xi (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (K.p - K.pPrime) K.q / g K.p K.q

lemma xi_def (g : Bilin V) (K : DisKinematics V) :
    xi g K = g (K.p - K.pPrime) K.q / g K.p K.q := (rfl)

/-- The variable `β = Q² / (2 Δ·q)`, the parton's fraction of the exchange, where `Δ = P - P'`
is the momentum lost by the target (carried by the colour-singlet exchange). Like any real
division in Lean, it is `0` when the denominator vanishes. -/
noncomputable def beta (g : Bilin V) (K : DisKinematics V) : ℝ :=
  K.Q2 g / (2 * g (K.p - K.pPrime) K.q)

lemma beta_def (g : Bilin V) (K : DisKinematics V) :
    beta g K = K.Q2 g / (2 * g (K.p - K.pPrime) K.q) := (rfl)

/-- The invariant mass squared of the surviving target-like system, `M_Y² = P'²`. -/
def MY2 (g : Bilin V) (K : DisKinematics V) : ℝ := g K.pPrime K.pPrime

lemma MY2_def (g : Bilin V) (K : DisKinematics V) :
    MY2 g K = g K.pPrime K.pPrime := (rfl)

/-- The invariant mass squared of the diffractive system `X`, `M_X² = (q + Δ)²` with
`Δ = P - P'`: by the momentum conservation `P + q = P' + q_X` of the diffractive event, the
system `X` carries the momentum `q_X = q + Δ`. -/
def MX2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (K.q + (K.p - K.pPrime)) (K.q + (K.p - K.pPrime))

lemma MX2_def (g : Bilin V) (K : DisKinematics V) :
    MX2 g K = g (K.q + (K.p - K.pPrime)) (K.q + (K.p - K.pPrime)) := (rfl)

/-- A direct expansion of `MX2` in terms of bilinear pieces, the diffractive counterpart of
`DisKinematics.W2_expand`: for a symmetric `g`, the cross term is the denominator `2 Δ·q` of
`beta`. -/
lemma MX2_expand (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    MX2 g K = g K.q K.q + 2 * g (K.p - K.pPrime) K.q
      + g (K.p - K.pPrime) (K.p - K.pPrime) := by
  rw [MX2_def, add_comm K.q, hSymm.apply_add_self]
  ring

/-- `MX2` in terms of the hard scale and the momentum transfer,
`M_X² = -Q² + 2 Δ·q + t`, the diffractive counterpart of `DisKinematics.W2_eq_with_Q2`. -/
lemma MX2_eq_with_Q2 (g : Bilin V) (K : DisKinematics V) (hSymm : g.IsSymm) :
    MX2 g K = -K.Q2 g + 2 * g (K.p - K.pPrime) K.q + K.tMom g := by
  rw [MX2_expand g K hSymm, DisKinematics.Q2_def, DisKinematics.tMom_def]
  ring

/-- The exact relation `β = Q² / (Q² + M_X² - t)` between the parton fraction and the invariant
mass of the diffractive system. The denominator `Q² + M_X² - t` equals the `2 Δ·q` of `beta`
identically for a symmetric `g`, so no non-degeneracy hypothesis is needed. -/
theorem beta_eq_Q2_div_Q2_add_MX2_sub_tMom (g : Bilin V) (K : DisKinematics V)
    (hSymm : g.IsSymm) :
    beta g K = K.Q2 g / (K.Q2 g + MX2 g K - K.tMom g) := by
  rw [MX2_eq_with_Q2 g K hSymm, beta_def]
  ring

/-- The invariant mass of the diffractive system in terms of `β`,
`M_X² = Q² (1/β - 1) + t`, the inverse of `beta_eq_Q2_div_Q2_add_MX2_sub_tMom`. It needs
`Q² ≠ 0`; when `Δ·q = 0` both sides equal `-Q² + t` by the convention `0⁻¹ = 0`. -/
theorem MX2_eq_Q2_mul_inv_beta_sub_one_add_tMom (g : Bilin V) (K : DisKinematics V)
    (hSymm : g.IsSymm) (hQ2 : K.Q2 g ≠ 0) :
    MX2 g K = K.Q2 g * ((beta g K)⁻¹ - 1) + K.tMom g := by
  rw [MX2_eq_with_Q2 g K hSymm, beta_def]
  rcases eq_or_ne (g (K.p - K.pPrime) K.q) 0 with hDq | hDq
  · rw [hDq]
    simp only [mul_zero, div_zero, inv_zero]
    ring
  · field_simp
    ring

/-- `ξ` depends on the record only through `q`, `P` and `P'`. -/
lemma xi_congr (g : Bilin V) {K₁ K₂ : DisKinematics V} (hp : K₁.p = K₂.p)
    (hpPrime : K₁.pPrime = K₂.pPrime) (hq : K₁.q = K₂.q) : xi g K₁ = xi g K₂ := by
  simp only [xi_def, hp, hpPrime, hq]

/-- `β` depends on the record only through `q`, `P` and `P'`. -/
lemma beta_congr (g : Bilin V) {K₁ K₂ : DisKinematics V} (hp : K₁.p = K₂.p)
    (hpPrime : K₁.pPrime = K₂.pPrime) (hq : K₁.q = K₂.q) : beta g K₁ = beta g K₂ := by
  simp only [beta_def, DisKinematics.Q2_def, hp, hpPrime, hq]

/-!
### The key identity: `x = ξ β`

`x = ξ β` is what justifies calling `β` a momentum fraction of the exchange.
-/

/-- The identity `x = ξ β` relating the inclusive Bjorken variable `x` of the event to the
diffractive variables `ξ` and `β`. This is an exact cancellation requiring no mass or
high-energy approximation. The cancellation needs the momentum lost by the target,
`Δ = P - P'`, to have `Δ·q ≠ 0`; when `P·q = 0` both sides vanish, so no non-degeneracy of
`P·q` is needed. -/
theorem xBj_eq_xi_mul_beta (g : Bilin V) (K : DisKinematics V)
    (hDeltaq : g (K.p - K.pPrime) K.q ≠ 0) :
    K.xBj g = xi g K * beta g K := by
  rw [DisKinematics.xBj_def, xi_def, beta_def]
  rcases eq_or_ne (g K.p K.q) 0 with hPq | hPq
  · simp [hPq]
  · field_simp

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
