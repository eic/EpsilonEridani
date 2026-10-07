/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# Exclusive DIS Kinematics Interfaces

This module extends the inclusive kinematics layer with off-forward variables used by
DVCS and DVMP interfaces.

-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Exclusive
namespace Kinematics

variable (V : Type) [AddCommGroup V] [Module ℝ V]

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin)

/-- Minimal off-forward exclusive kinematics container. -/
structure ExclKinematics where
  /-- Incoming hadron momentum. -/
  p : V
  /-- Outgoing hadron momentum. -/
  pPrime : V
  /-- Incoming lepton momentum. -/
  k : V
  /-- Outgoing lepton momentum. -/
  kPrime : V
  /-- Momentum of the exchanged virtual photon, `q = k - k'` by `hqLepton`. -/
  q : V
  /-- Momentum of the produced real photon (DVCS) or meson (DVMP). -/
  qPrime : V
  /-- Azimuthal angle of the lepton plane. -/
  phiL : ℝ
  /-- Azimuthal angle of the hadron plane. -/
  phiH : ℝ
  /-- The virtual photon carries the lepton momentum transfer. -/
  hqLepton : q = k - kPrime
  /-- Momentum conservation at the hadronic vertex, `p + q = p' + q'`. -/
  hMomentum : p + q = pPrime + qPrime

namespace ExclKinematics

variable {V}

/-- Hard scale in the exclusive channel. -/
def Q2 (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  - g K.q K.q

omit [Module ℝ V] in
/-- Momentum transfer to the hadron, `Δ = p' - p`. -/
def delta (K : ExclKinematics V) : V :=
  K.pPrime - K.p

/-- Momentum-transfer invariant `t = Δ² = (p' - p)²` in the exclusive channel. -/
def tMom (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  g K.delta K.delta

/-- Skewness `ξ = -Δ·qbar / (2 Pbar·qbar)` with `Pbar = (p + p') / 2` and `qbar = (q + q') / 2`
(Belitsky-Müller-Kirchner's `η`). The halves cancel, so this is
`-Δ·(q + q') / ((p + p')·(q + q'))`. For DVCS (`q'² = 0`, `p² = p'²`) it equals
`x_B / (2 - x_B + x_B t / Q²)` with `x_B = Q² / (2 p·q)`, i.e. `x_B / (2 - x_B)` as `t → 0`.
Like any real division in Lean, it is `0` when the denominator vanishes. -/
noncomputable def xiSkew (g : Bilin V) (K : ExclKinematics V) : ℝ :=
  -g K.delta (K.q + K.qPrime) / g (K.p + K.pPrime) (K.q + K.qPrime)

/-- Relative azimuthal angle between hadron and lepton planes. -/
def phiDiff (K : ExclKinematics V) : ℝ :=
  K.phiH - K.phiL

omit [Module ℝ V] in
lemma q_eq_lepton_transfer (K : ExclKinematics V) :
    K.q = K.k - K.kPrime :=
  K.hqLepton

omit [Module ℝ V] in
/-- Momentum conservation expresses the hadron momentum transfer through the photon side,
`Δ = q - q'`. -/
lemma delta_eq_q_sub_qPrime (K : ExclKinematics V) :
    K.delta = K.q - K.qPrime := by
  rw [delta, sub_eq_sub_iff_add_eq_add, ← K.hMomentum]
  exact add_comm _ _

lemma tMom_eq_hadronic_transfer_sq
    (g : Bilin V) (K : ExclKinematics V) :
    K.tMom g = g (K.pPrime - K.p) (K.pPrime - K.p) :=
  rfl

/-- `t` evaluated on the photon side of the hadronic vertex, `t = (q - q')²`. -/
lemma tMom_eq_photon_transfer_sq
    (g : Bilin V) (K : ExclKinematics V) :
    K.tMom g = g (K.q - K.qPrime) (K.q - K.qPrime) := by
  rw [tMom, delta_eq_q_sub_qPrime]

/-- For a symmetric `g`, the numerator of `xiSkew` is `-Δ·(q + q') = q'² - q²`, which is
`Q²` for DVCS (`q'² = 0`). -/
lemma neg_delta_apply_q_add_qPrime
    (g : Bilin V) (hg : g.IsSymm) (K : ExclKinematics V) :
    -g K.delta (K.q + K.qPrime) = g K.qPrime K.qPrime - g K.q K.q := by
  rw [K.delta_eq_q_sub_qPrime]
  simp only [map_sub, map_add, LinearMap.sub_apply]
  rw [hg.eq K.qPrime K.q]
  ring

/-- For DVCS kinematics (`q'² = 0`, `p'² = p²`) and a symmetric `g`, the denominator of
`xiSkew` is `(p + p')·(q + q') = 4 p·q + t - Q²`. -/
lemma apply_p_add_pPrime_q_add_qPrime
    (g : Bilin V) (hg : g.IsSymm) (K : ExclKinematics V)
    (hqPrime : g K.qPrime K.qPrime = 0) (hp : g K.pPrime K.pPrime = g K.p K.p) :
    g (K.p + K.pPrime) (K.q + K.qPrime) = 4 * g K.p K.q + K.tMom g - K.Q2 g := by
  have hp' : K.pPrime = K.p + K.delta := by
    rw [delta]
    abel
  have hq' : K.qPrime = K.q - K.delta := by
    rw [delta_eq_q_sub_qPrime]
    abel
  -- `p'² = p²` gives `2 p·Δ + Δ² = 0`.
  have hpΔ : g K.p K.delta + g K.delta K.p + g K.delta K.delta = 0 := by
    have h := hp
    rw [hp'] at h
    simp only [map_add, LinearMap.add_apply] at h
    linarith
  -- `q'² = 0` gives `q² - 2 q·Δ + Δ² = 0`.
  have hqΔ : g K.q K.q - g K.q K.delta - g K.delta K.q + g K.delta K.delta = 0 := by
    have h := hqPrime
    rw [hq'] at h
    simp only [map_sub, LinearMap.sub_apply] at h
    linarith
  rw [tMom, Q2, hp', hq']
  simp only [map_add, map_sub, LinearMap.add_apply]
  linear_combination (-1 : ℝ) * hpΔ + hg.eq K.delta K.p - hqΔ + hg.eq K.delta K.q

/-- For DVCS kinematics (`q'² = 0`, `p'² = p²`) and a symmetric `g`, `xiSkew` takes the
standard form `ξ = x_B / (2 - x_B + x_B t / Q²)` with `x_B = Q² / (2 p·q)`. -/
lemma xiSkew_eq_xB_form
    (g : Bilin V) (hg : g.IsSymm) (K : ExclKinematics V)
    (hqPrime : g K.qPrime K.qPrime = 0) (hp : g K.pPrime K.pPrime = g K.p K.p)
    (hpq : g K.p K.q ≠ 0) (hQ2 : K.Q2 g ≠ 0) :
    K.xiSkew g =
      K.Q2 g / (2 * g K.p K.q) /
        (2 - K.Q2 g / (2 * g K.p K.q) + K.Q2 g / (2 * g K.p K.q) * K.tMom g / K.Q2 g) := by
  have hnum : -g K.delta (K.q + K.qPrime) = K.Q2 g := by
    rw [neg_delta_apply_q_add_qPrime g hg K, hqPrime, Q2, zero_sub]
  have h2pq : 2 * g K.p K.q ≠ 0 := mul_ne_zero two_ne_zero hpq
  have hden : 2 - K.Q2 g / (2 * g K.p K.q) + K.Q2 g / (2 * g K.p K.q) * K.tMom g / K.Q2 g
      = (4 * g K.p K.q + K.tMom g - K.Q2 g) / (2 * g K.p K.q) := by
    rw [div_mul_eq_mul_div, div_div, mul_comm (K.Q2 g) (K.tMom g),
      mul_div_mul_right _ _ hQ2, eq_div_iff h2pq, add_mul, sub_mul,
      div_mul_cancel₀ _ h2pq, div_mul_cancel₀ _ h2pq]
    ring
  rw [xiSkew, hnum, apply_p_add_pPrime_q_add_qPrime g hg K hqPrime hp, hden,
    div_div_div_cancel_right₀ h2pq]

end ExclKinematics

end Kinematics
end Exclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
