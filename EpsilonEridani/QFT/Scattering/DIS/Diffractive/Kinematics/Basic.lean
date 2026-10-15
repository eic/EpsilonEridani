/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic
/-!

# Diffractive DIS kinematics

A diffractive deep-inelastic event `e(k) + p(P) → e(k') + X + Y(P')` is described by the
inclusive kinematic record `DisKinematics`, whose field `pPrime` is the distinguished outgoing
target-like momentum `P'` (the surviving target, or a low-mass dissociated system `Y`).
With `q = k - k'` and `Δ = P - P'` the momentum lost by the target (`deltaTarget`; note the sign
is opposite to the exclusive layer's `ExclKinematics.delta = P' - P`), this file defines

* `t = Δ²`, the invariant momentum transfer to the target (`tMom`);
* `ξ = Δ·q / P·q`, the fraction of the target momentum carried by the exchange (`xi`);
* `β = Q² / (2 Δ·q)`, the fraction of the exchange momentum carried by the struck parton
  (`beta`);
* `M_X² = (q + Δ)²` and `M_Y² = P'²`, the invariant masses squared of the diffractive system
  and of the target-side system (`MX2`, `MY2`),

and proves, with no mass or high-energy approximation,

* `x = ξ β` whenever `Δ·q ≠ 0` (`xBj_eq_xi_mul_beta`), which is why `β` is a momentum fraction
  of the exchange;
* `β = Q² / (Q² + M_X² - t)` (`beta_eq_Q2_div`), equivalently, for `Q² ≠ 0`,
  `M_X² = Q² (1/β - 1) + t` (`MX2_eq_Q2_mul_inv_beta_sub_one_add_tMom`);
* `ξ = (Q² + M_X² - t) / (Q² + W² - M²)` with `M² = P²` (`xi_eq_Q2_add_MX2_sub_tMom_div`), so
  that `ξ` is fixed by the measured mass of the diffractive system and the inclusive kinematics;
* that `ξ`, `β`, `t` and `M_X²` depend on the event only through `q`, `P` and `P'`, and hence not
  on the inelasticity `y` (`xi_congr`, `beta_congr`, `tMom_congr`, `MX2_congr`).

The event is also exclusive kinematics with `X` as the produced system (`toExclKinematics`), and
`t` is the exclusive momentum-transfer invariant `ExclKinematics.tMom` of that event
(`tMom_toExclKinematics`).

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
open EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics (ExclKinematics)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

omit [Module ℝ V] in
/-- The momentum lost by the target, `Δ = P - P'`. With this sign `Δ·q > 0` in the physical
region, so that `ξ` and `β` are positive. This is the opposite sign to the exclusive layer's
`Exclusive.Kinematics.ExclKinematics.delta = P' - P`; only `t = Δ²` agrees between the two
conventions (`tMom_toExclKinematics`), while `Δ`-linear quantities such as `P·Δ` flip sign. -/
def deltaTarget (K : DisKinematics V) : V :=
  K.p - K.pPrime

omit [Module ℝ V] in
lemma deltaTarget_def (K : DisKinematics V) : deltaTarget K = K.p - K.pPrime := (rfl)

omit [Module ℝ V] in
/-- The momentum of the diffractive system `X`, `p_X = q + Δ = P + q - P'`. -/
def pX (K : DisKinematics V) : V :=
  K.q + deltaTarget K

omit [Module ℝ V] in
lemma pX_def (K : DisKinematics V) : pX K = K.q + deltaTarget K := (rfl)

/-- The invariant momentum transfer to the target, `t = Δ² = (P - P')²`. -/
def tMom (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (deltaTarget K) (deltaTarget K)

lemma tMom_def (g : Bilin V) (K : DisKinematics V) :
    tMom g K = g (deltaTarget K) (deltaTarget K) := (rfl)

/-- The fraction of the target momentum carried by the exchange, `ξ = Δ·q / P·q`. -/
noncomputable def xi (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (deltaTarget K) K.q / g K.p K.q

lemma xi_def (g : Bilin V) (K : DisKinematics V) :
    xi g K = g (deltaTarget K) K.q / g K.p K.q := (rfl)

/-- The fraction of the exchange momentum carried by the struck parton, `β = Q² / (2 Δ·q)`. -/
noncomputable def beta (g : Bilin V) (K : DisKinematics V) : ℝ :=
  K.Q2 g / (2 * g (deltaTarget K) K.q)

lemma beta_def (g : Bilin V) (K : DisKinematics V) :
    beta g K = K.Q2 g / (2 * g (deltaTarget K) K.q) := (rfl)

/-- The invariant mass squared of the diffractive system, `M_X² = (q + Δ)²`. -/
def MX2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g (pX K) (pX K)

lemma MX2_def (g : Bilin V) (K : DisKinematics V) : MX2 g K = g (pX K) (pX K) := (rfl)

/-- The invariant mass squared of the target-side system, `M_Y² = P'²`. -/
def MY2 (g : Bilin V) (K : DisKinematics V) : ℝ :=
  g K.pPrime K.pPrime

lemma MY2_def (g : Bilin V) (K : DisKinematics V) : MY2 g K = g K.pPrime K.pPrime := (rfl)

/-- Products with `Δ` in the first slot, in terms of the momenta: `Δ·v = P·v - P'·v`. -/
lemma apply_deltaTarget_left (g : Bilin V) (K : DisKinematics V) (v : V) :
    g (deltaTarget K) v = g K.p v - g K.pPrime v := by
  rw [deltaTarget, map_sub, LinearMap.sub_apply]

/-- Products with `Δ` in the second slot, in terms of the momenta: `v·Δ = v·P - v·P'`. -/
lemma apply_deltaTarget_right (g : Bilin V) (K : DisKinematics V) (v : V) :
    g v (deltaTarget K) = g v K.p - g v K.pPrime := by
  rw [deltaTarget, map_sub]

/-- `ξ = 1 - P'·q / P·q` whenever `P·q ≠ 0`. -/
lemma xi_eq_one_sub_div (g : Bilin V) (K : DisKinematics V) (hpq : g K.p K.q ≠ 0) :
    xi g K = 1 - g K.pPrime K.q / g K.p K.q := by
  rw [xi, apply_deltaTarget_left, sub_div, div_self hpq]

omit [Module ℝ V] in
/-- `p_X` is defined as `q + Δ`, so momentum conservation `P + q = P' + p_X` at the hadronic
vertex holds by construction. -/
lemma p_add_q_eq_pPrime_add_pX (K : DisKinematics V) : K.p + K.q = K.pPrime + pX K := by
  rw [pX, deltaTarget]
  abel

/-- A diffractive event as exclusive kinematics with the diffractive system `X` in the role of the
produced particle, `q' = p_X`, and given azimuthal angles `phiL`, `phiH` of the lepton and hadron
planes. This is the bridge to the momentum-transfer layer of `Exclusive.Kinematics`. -/
def toExclKinematics (K : DisKinematics V) (phiL phiH : ℝ) : ExclKinematics V where
  p := K.p
  pPrime := K.pPrime
  k := K.k
  kPrime := K.kPrime
  q := K.q
  qPrime := pX K
  phiL := phiL
  phiH := phiH
  hqLepton := K.hq
  hMomentum := p_add_q_eq_pPrime_add_pX K

section toExclKinematics

variable (K : DisKinematics V) (phiL phiH : ℝ)

omit [Module ℝ V]

@[simp] lemma toExclKinematics_p : (toExclKinematics K phiL phiH).p = K.p := (rfl)

@[simp] lemma toExclKinematics_pPrime : (toExclKinematics K phiL phiH).pPrime = K.pPrime := (rfl)

@[simp] lemma toExclKinematics_k : (toExclKinematics K phiL phiH).k = K.k := (rfl)

@[simp] lemma toExclKinematics_kPrime : (toExclKinematics K phiL phiH).kPrime = K.kPrime := (rfl)

@[simp] lemma toExclKinematics_q : (toExclKinematics K phiL phiH).q = K.q := (rfl)

@[simp] lemma toExclKinematics_qPrime : (toExclKinematics K phiL phiH).qPrime = pX K := (rfl)

@[simp] lemma toExclKinematics_phiL : (toExclKinematics K phiL phiH).phiL = phiL := (rfl)

@[simp] lemma toExclKinematics_phiH : (toExclKinematics K phiL phiH).phiH = phiH := (rfl)

end toExclKinematics

omit [Module ℝ V] in
/-- The exclusive transfer `P' - P` of the bridged event is `-Δ`. -/
@[simp]
lemma delta_toExclKinematics (K : DisKinematics V) (phiL phiH : ℝ) :
    (toExclKinematics K phiL phiH).delta = -deltaTarget K := by
  rw [ExclKinematics.delta, toExclKinematics_pPrime, toExclKinematics_p, deltaTarget, neg_sub]

/-- The diffractive `t` is the exclusive `t` of the bridged event, `t = (P' - P)²`. -/
@[simp]
lemma tMom_toExclKinematics (g : Bilin V) (K : DisKinematics V) (phiL phiH : ℝ) :
    (toExclKinematics K phiL phiH).tMom g = tMom g K := by
  simp only [ExclKinematics.tMom, delta_toExclKinematics, map_neg, LinearMap.neg_apply, neg_neg,
    tMom]

/-- Expansion of the diffractive mass: `M_X² = 2 Δ·q - Q² + t`. -/
lemma MX2_eq_two_mul_apply_deltaTarget_q_sub_Q2_add_tMom (g : Bilin V) (hg : g.IsSymm)
    (K : DisKinematics V) :
    MX2 g K = 2 * g (deltaTarget K) K.q - K.Q2 g + tMom g K := by
  have h := hg.polarization (deltaTarget K) K.q
  rw [add_comm] at h
  rw [MX2, pX, tMom, DisKinematics.Q2]
  linarith

/-- The denominator of `β` in terms of the event invariants: `2 Δ·q = Q² + M_X² - t`. -/
lemma two_mul_apply_deltaTarget_q_eq_Q2_add_MX2_sub_tMom (g : Bilin V) (hg : g.IsSymm)
    (K : DisKinematics V) :
    2 * g (deltaTarget K) K.q = K.Q2 g + MX2 g K - tMom g K := by
  rw [MX2_eq_two_mul_apply_deltaTarget_q_sub_Q2_add_tMom g hg K]
  ring

/-- Expansion of the target-side mass: `M_Y² = M² - 2 P·Δ + t` with `M² = P²`. -/
lemma MY2_eq_p_sq_sub_two_mul_apply_p_deltaTarget_add_tMom (g : Bilin V) (hg : g.IsSymm)
    (K : DisKinematics V) :
    MY2 g K = g K.p K.p - 2 * g K.p (deltaTarget K) + tMom g K := by
  have h := hg.polarization K.p (-deltaTarget K)
  rw [← sub_eq_add_neg, deltaTarget, sub_sub_cancel] at h
  simp only [map_neg, LinearMap.neg_apply, neg_neg] at h
  rw [MY2, tMom, deltaTarget]
  linarith

/-- `t = M² - 2 P·P' + M_Y²` with `M² = P²`. -/
lemma tMom_eq_p_sq_sub_two_mul_apply_p_pPrime_add_MY2 (g : Bilin V) (hg : g.IsSymm)
    (K : DisKinematics V) :
    tMom g K = g K.p K.p - 2 * g K.p K.pPrime + MY2 g K := by
  rw [MY2_eq_p_sq_sub_two_mul_apply_p_deltaTarget_add_tMom g hg K, apply_deltaTarget_right]
  ring

/-- **`x = ξ β`.** The Bjorken variable is the product of the momentum fraction `ξ` lost by
the target and the fraction `β` of that momentum carried by the struck parton. The only
hypothesis is `Δ·q ≠ 0`, without which `ξ = β = 0` by the convention `a / 0 = 0`. -/
theorem xBj_eq_xi_mul_beta (g : Bilin V) (K : DisKinematics V)
    (hΔq : g (deltaTarget K) K.q ≠ 0) :
    K.xBj g = xi g K * beta g K := by
  rw [DisKinematics.xBj, ← mul_div_mul_left (K.Q2 g) (2 * g K.p K.q) hΔq, xi, beta]
  ring

/-- `β = Q² / (Q² + M_X² - t)`: `β` is determined by the photon virtuality, the mass of the
diffractive system and the momentum transfer. -/
theorem beta_eq_Q2_div (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V) :
    beta g K = K.Q2 g / (K.Q2 g + MX2 g K - tMom g K) := by
  rw [beta, two_mul_apply_deltaTarget_q_eq_Q2_add_MX2_sub_tMom g hg K]

/-- The inverse of `beta_eq_Q2_div`: `M_X² = Q² (1/β - 1) + t` whenever `Q² ≠ 0`. -/
theorem MX2_eq_Q2_mul_inv_beta_sub_one_add_tMom (g : Bilin V) (hg : g.IsSymm)
    (K : DisKinematics V) (hQ2 : K.Q2 g ≠ 0) :
    MX2 g K = K.Q2 g * ((beta g K)⁻¹ - 1) + tMom g K := by
  rw [beta_eq_Q2_div g hg K, inv_div, mul_sub, mul_div_cancel₀ _ hQ2]
  ring

/-- `ξ = (Q² + M_X² - t) / (Q² + W² - M²)` with `W² = (P + q)²` and `M² = P²`: `ξ` is fixed by
the measured mass of the diffractive system and the inclusive kinematics. -/
theorem xi_eq_Q2_add_MX2_sub_tMom_div (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V) :
    xi g K = (K.Q2 g + MX2 g K - tMom g K) / (K.Q2 g + K.W2 g - g K.p K.p) := by
  have hden : K.Q2 g + K.W2 g - g K.p K.p = 2 * g K.p K.q := by
    rw [DisKinematics.W2_eq_with_Q2 g K hg]
    ring
  rw [← two_mul_apply_deltaTarget_q_eq_Q2_add_MX2_sub_tMom g hg K, hden,
    mul_div_mul_left _ _ two_ne_zero, xi]

/-! ### Independence of the lepton momenta

`ξ`, `β`, `t` and `M_X²` are functions of the hadronic-side momenta `q`, `P` and `P'` alone. Two
events with the same `q`, `P` and `P'` but different lepton momenta, and hence in general
different inelasticity `y = P·q / P·k`, have the same diffractive variables. -/

section congr

variable {K K' : DisKinematics V}

omit [Module ℝ V] in
lemma deltaTarget_congr (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime) :
    deltaTarget K = deltaTarget K' := by
  rw [deltaTarget, deltaTarget, hp, hpPrime]

omit [Module ℝ V] in
lemma pX_congr (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime) (hq : K.q = K'.q) :
    pX K = pX K' := by
  rw [pX, pX, deltaTarget_congr hp hpPrime, hq]

lemma tMom_congr (g : Bilin V) (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime) :
    tMom g K = tMom g K' := by
  rw [tMom, tMom, deltaTarget_congr hp hpPrime]

lemma xi_congr (g : Bilin V) (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime)
    (hq : K.q = K'.q) : xi g K = xi g K' := by
  rw [xi, xi, deltaTarget_congr hp hpPrime, hp, hq]

lemma beta_congr (g : Bilin V) (hp : K.p = K'.p) (hpPrime : K.pPrime = K'.pPrime)
    (hq : K.q = K'.q) : beta g K = beta g K' := by
  rw [beta, beta, DisKinematics.Q2, DisKinematics.Q2, deltaTarget_congr hp hpPrime, hq]

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
