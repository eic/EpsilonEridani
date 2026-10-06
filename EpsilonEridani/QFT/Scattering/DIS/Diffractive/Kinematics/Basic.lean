/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# Diffractive DIS kinematics

A diffractive deep-inelastic event `e(k) + p(P) → e(k') + X + Y(P')` is described by the
inclusive kinematic record `DisKinematics`, whose field `pPrime` is the distinguished outgoing
target-like momentum `P'` (the surviving target, or a low-mass dissociated system `Y`).
With `q = k - k'` and `Δ = P - P'` the momentum lost by the target, this file defines

* `t = Δ²`, the invariant momentum transfer to the target (`tMom`);
* `ξ = Δ·q / P·q`, the fraction of the target momentum carried by the exchange (`xi`);
* `β = Q² / (2 Δ·q)`, the fraction of the exchange momentum carried by the struck parton
  (`beta`);
* `M_X² = (q + Δ)²` and `M_Y² = P'²`, the invariant masses squared of the diffractive system
  and of the target-side system (`MX2`, `MY2`),

and proves, with no mass or high-energy approximation,

* `x = ξ β` (`xBj_eq_xi_mul_beta`), which is why `β` is a momentum fraction of the exchange;
* `β = Q² / (Q² + M_X² - t)` (`beta_eq_Q2_div`), equivalently
  `M_X² = Q² (1/β - 1) + t` (`MX2_eq_Q2_mul_inv_beta_sub_one_add_tMom`);
* `ξ = (Q² + M_X² - t) / (Q² + W² - M²)` with `M² = P²` (`xi_eq_div`), so that `ξ` is fixed by the
  measured mass of the diffractive system and the inclusive kinematics;
* that `ξ`, `β`, `t` and `M_X²` depend on the event only through `q`, `P` and `P'`, and hence not
  on the inelasticity `y` (`xi_congr`, `beta_congr`, `tMom_congr`, `MX2_congr`).

As elsewhere in the DIS kinematics layer, Lorentz products are taken with respect to an abstract
bilinear form `g`, assumed symmetric where needed, and real division follows Lean's convention
`a / 0 = 0`.

## References

* G. Wolf, *Review of high energy diffraction in real and virtual photon proton scattering at
  HERA*, Rept. Prog. Phys. **73** (2010) 116202, §2.
* V. Barone and E. Predazzi, *High-Energy Particle Diffraction*, Springer (2002), ch. 1–2.

-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive
namespace Kinematics

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

omit [Module ℝ V] in
/-- The momentum lost by the target, `Δ = P - P'`. With this sign `Δ·q > 0` in the physical
region, so that `ξ` and `β` are positive. -/
def delta (K : DisKinematics V) : V :=
  K.p - K.pPrime

/-- The momentum of the diffractive system `X`, `p_X = q + Δ = P + q - P'`. -/
def pX (K : DisKinematics V) : V :=
  K.q + delta K

/-- The invariant momentum transfer to the target, `t = Δ² = (P - P')²`. -/
def tMom (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (delta K) (delta K)

/-- The fraction of the target momentum carried by the exchange, `ξ = Δ·q / P·q`. -/
noncomputable def xi (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (delta K) K.q / g K.p K.q

/-- The fraction of the exchange momentum carried by the struck parton, `β = Q² / (2 Δ·q)`. -/
noncomputable def beta (g : Bilin V) (K : DisKinematics V) : ℝ :=
  K.Q2 g / (2 * g (delta K) K.q)

/-- The invariant mass squared of the diffractive system, `M_X² = (q + Δ)²`. -/
def MX2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (pX K) (pX K)

/-- The invariant mass squared of the target-side system, `M_Y² = P'²`. -/
def MY2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g K.pPrime K.pPrime

omit [Module ℝ V] in
/-- Momentum conservation at the hadronic vertex, `P + q = P' + p_X`. -/
lemma p_add_q_eq_pPrime_add_pX (K : DisKinematics V) : K.p + K.q = K.pPrime + pX K := by
  rw [pX, delta]
  abel

/-- `t` is also the square of `P' - P`, the opposite sign convention for the transfer. -/
lemma tMom_eq_pPrime_sub_p_sq (g : Bilin V) (K : DisKinematics V) :
    tMom g K = g (K.pPrime - K.p) (K.pPrime - K.p) := by
  simp only [tMom, delta, ← neg_sub K.pPrime K.p, map_neg, LinearMap.neg_apply, neg_neg]

/-- Expansion of the diffractive mass: `M_X² = 2 Δ·q - Q² + t`. -/
lemma MX2_eq (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V) :
    MX2 g K = 2 * g (delta K) K.q - K.Q2 g + tMom g K := by
  rw [MX2, pX, tMom, DisKinematics.Q2]
  simp only [map_add, LinearMap.add_apply]
  rw [hg.eq K.q (delta K)]
  ring

/-- The denominator of `β` in terms of the event invariants: `2 Δ·q = Q² + M_X² - t`. -/
lemma two_mul_delta_q_eq (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V) :
    2 * g (delta K) K.q = K.Q2 g + MX2 g K - tMom g K := by
  rw [MX2_eq g hg K]
  ring

/-- Expansion of the target-side mass: `M_Y² = M² - 2 P·Δ + t` with `M² = P²`. -/
lemma MY2_eq (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V) :
    MY2 g K = g K.p K.p - 2 * g K.p (delta K) + tMom g K := by
  have hpPrime : K.pPrime = K.p - delta K := by
    rw [delta]
    abel
  rw [MY2, tMom, hpPrime]
  simp only [map_sub, LinearMap.sub_apply]
  rw [hg.eq (delta K) K.p]
  ring

/-- **`x = ξ β`.** The Bjorken variable is the product of the momentum fraction `ξ` lost by
the target and the fraction `β` of that momentum carried by the struck parton. The only
hypothesis is `Δ·q ≠ 0`, without which `ξ = β = 0` by the convention `a / 0 = 0`. -/
theorem xBj_eq_xi_mul_beta (g : Bilin V) (K : DisKinematics V) (hΔq : g (delta K) K.q ≠ 0) :
    K.xBj g = xi g K * beta g K := by
  rw [DisKinematics.xBj, ← mul_div_mul_left (K.Q2 g) (2 * g K.p K.q) hΔq, xi, beta]
  ring

/-- `β = Q² / (Q² + M_X² - t)`: `β` is determined by the photon virtuality, the mass of the
diffractive system and the momentum transfer. -/
theorem beta_eq_Q2_div (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V) :
    beta g K = K.Q2 g / (K.Q2 g + MX2 g K - tMom g K) := by
  rw [beta, two_mul_delta_q_eq g hg K]

/-- The inverse of `beta_eq_Q2_div`: `M_X² = Q² (1/β - 1) + t` whenever `β ≠ 0`. -/
theorem MX2_eq_Q2_mul_inv_beta_sub_one_add_tMom (g : Bilin V) (hg : g.IsSymm)
    (K : DisKinematics V) (hβ : beta g K ≠ 0) :
    MX2 g K = K.Q2 g * ((beta g K)⁻¹ - 1) + tMom g K := by
  have hQ2 : K.Q2 g ≠ 0 := by
    rintro h
    exact hβ (by rw [beta, h, zero_div])
  rw [beta_eq_Q2_div g hg K, inv_div, mul_sub, mul_div_cancel₀ _ hQ2]
  ring

/-- `ξ = (Q² + M_X² - t) / (Q² + W² - M²)` with `W² = (P + q)²` and `M² = P²`: `ξ` is fixed by
the measured mass of the diffractive system and the inclusive kinematics. -/
theorem xi_eq_div (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V) :
    xi g K = (K.Q2 g + MX2 g K - tMom g K) / (K.Q2 g + K.W2 g - g K.p K.p) := by
  have hden : K.Q2 g + K.W2 g - g K.p K.p = 2 * g K.p K.q := by
    rw [DisKinematics.W2_eq_with_Q2 g K hg]
    ring
  rw [← two_mul_delta_q_eq g hg K, hden, mul_div_mul_left _ _ two_ne_zero, xi]

/-! ### Independence of the lepton momenta

`ξ`, `β`, `t` and `M_X²` are functions of the hadronic-side momenta `q`, `P` and `P'` alone. Two
events with the same `q`, `P` and `P'` but different lepton momenta, and hence in general
different inelasticity `y = P·q / P·k`, have the same diffractive variables. -/

section congr

variable {K K' : DisKinematics V}

omit [Module ℝ V] in
lemma delta_congr (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime) :
    delta K = delta K' := by
  rw [delta, delta, hp, hpPrime]

omit [Module ℝ V] in
lemma pX_congr (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime) (hq : K.q = K'.q) :
    pX K = pX K' := by
  rw [pX, pX, delta_congr hp hpPrime, hq]

lemma tMom_congr (g : Bilin V) (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime) :
    tMom g K = tMom g K' := by
  rw [tMom, tMom, delta_congr hp hpPrime]

lemma xi_congr (g : Bilin V) (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime)
    (hq : K.q = K'.q) : xi g K = xi g K' := by
  rw [xi, xi, delta_congr hp hpPrime, hp, hq]

lemma beta_congr (g : Bilin V) (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime)
    (hq : K.q = K'.q) : beta g K = beta g K' := by
  rw [beta, beta, DisKinematics.Q2, DisKinematics.Q2, delta_congr hp hpPrime, hq]

lemma MX2_congr (g : Bilin V) (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime)
    (hq : K.q = K'.q) : MX2 g K = MX2 g K' := by
  rw [MX2, MX2, pX_congr hp hpPrime hq]

end congr

end Kinematics
end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
