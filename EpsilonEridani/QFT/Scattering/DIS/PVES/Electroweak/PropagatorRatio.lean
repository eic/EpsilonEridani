/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.Parameters
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity

/-!
# The `Z`-to-photon propagator ratio

The relative normalisation of `Z` and photon exchange in neutral-current scattering at
virtuality `Q²` is the ratio `η` of the `Z`-exchange to the photon-exchange
propagator-and-coupling factor (`Electroweak.zToPhotonRatio`). At tree level, with
`e² = g² sin²θ_W`, it is `η = Q² / (4 sin²θ_W cos²θ_W (Q² + M_Z²))`
(`Electroweak.zToPhotonRatio_eq`), and it is non-negative for spacelike momentum transfer and
`cos²θ_W ≥ 0` (`Electroweak.zToPhotonRatio_nonneg`).
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

/-- The ratio `η` of the `Z`-exchange to the photon-exchange propagator-and-coupling factor at
virtuality `Q²`: the `Z` vertex `(g / (2 cos θ_W)) γ^μ (g_V - g_A γ⁵)` and propagator
`1 / (Q² + M_Z²)` against the photon vertex `e γ^μ` and propagator `1 / Q²`, that is
`(g² / (4 cos²θ_W)) / (Q² + M_Z²)` divided by `e² / Q²`. -/
def zToPhotonRatio (P : Parameters) (Q2 : ℝ) : ℝ :=
  P.gSU2 ^ 2 / (4 * cos2ThetaW P) / (Q2 + P.mZ ^ 2) / (P.electricCharge ^ 2 / Q2)

theorem zToPhotonRatio_def (P : Parameters) (Q2 : ℝ) :
    zToPhotonRatio P Q2 =
      P.gSU2 ^ 2 / (4 * cos2ThetaW P) / (Q2 + P.mZ ^ 2) / (P.electricCharge ^ 2 / Q2) :=
  (rfl)

/-- **The tree-level propagator ratio.** With `e² = g² sin²θ_W`, which follows from the
weak-mixing and electric-charge relations, `η = Q² / (4 sin²θ_W cos²θ_W (Q² + M_Z²))`. In the
degenerate cases `g = 0` (where `cos²θ_W = 0`) and `sin²θ_W = 0` (where `e = 0`) both sides are
`0` by the convention `a / 0 = 0`. -/
theorem zToPhotonRatio_eq (P : Parameters) (hMix : weakMixingConsistency P)
    (hEM : electricChargeConsistency P) (hNe : P.gSU2 ^ 2 + P.gU1 ^ 2 ≠ 0) (Q2 : ℝ) :
    zToPhotonRatio P Q2 = Q2 / (4 * P.sin2ThetaW * cos2ThetaW P * (Q2 + P.mZ ^ 2)) := by
  rw [zToPhotonRatio_def, electricCharge_sq_eq_gSU2_sq_mul_sin2ThetaW P hMix hEM hNe]
  rcases eq_or_ne P.gSU2 0 with hg | hg
  · -- `g = 0` forces `cos²θ_W = 0`, so both sides vanish.
    have hc : cos2ThetaW P = 0 := by
      have h := cos2ThetaW_mul_couplingSq P hMix
      rw [hg, zero_pow two_ne_zero, zero_add] at h
      rw [hg, zero_pow two_ne_zero, zero_add] at hNe
      exact (mul_eq_zero.mp h).resolve_right hNe
    simp [hg, hc]
  rcases eq_or_ne P.sin2ThetaW 0 with hs | hs
  · -- `sin²θ_W = 0` makes `e² = 0` and the right-hand denominator `0`, so both sides vanish.
    simp [hs]
  · field_simp

/-- The propagator ratio is non-negative for spacelike momentum transfer and a mixing angle in
the physical range. -/
theorem zToPhotonRatio_nonneg (P : Parameters) (hc : 0 ≤ cos2ThetaW P) {Q2 : ℝ} (hQ : 0 ≤ Q2) :
    0 ≤ zToPhotonRatio P Q2 := by
  rw [zToPhotonRatio_def]
  positivity

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak
