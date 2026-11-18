/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.BesselK.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.ExpDecay

/-!
# The light-cone wave functions of a virtual photon

In the colour-dipole picture of deep-inelastic scattering at small `x`, the virtual photon of
virtuality `Q²` fluctuates into a quark-antiquark pair of flavour `f` (charge `e_f` in units of the
positron charge, mass `m_f`) long before the target. The quark carries the fraction `z` of the
photon's light-cone momentum and the pair has transverse separation `r`. The squared light-cone
wave functions, summed over helicities and colours, are (Nikolaev and Zakharov 1991; in the
normalisation of Kowalski and Teaney 2003)

```
|Ψ_T|² = (2 N_c α_em e_f² / π) [(z² + (1-z)²) ε² K₁(ε r)² + m_f² K₀(ε r)²],
|Ψ_L|² = (2 N_c α_em e_f² / π) [4 Q² z² (1-z)² K₀(ε r)²],
```

with `ε² = z (1 - z) Q² + m_f²` and `K₀`, `K₁` the modified Bessel functions of the second kind
(`EpsilonEridani.besselK`). With this normalisation the virtual-photon cross sections are
`σ_{T,L} = Σ_f ∫ d²r ∫₀¹ dz / (4π) |Ψ_{T,L}|² σ_dipole(r)`, so only the ratio of the two
prefactors is physical; the common factor `2 N_c α_em e_f² / π` cancels in every ratio of cross
sections.

The results are the analytic properties a dipole cross section is integrated against:

* both squared wave functions are non-negative, symmetric under `z ↦ 1 - z`, and positive away
  from the degenerate configurations;
* both are bounded by a multiple of `(ε + 1/r)² exp (-2 ε r)`, so dipoles much larger than `1 / ε`
  are exponentially suppressed, and uniformly in `z`, `Q²` and `m_f` by a multiple of `1 / r²`;
  hence both are integrable in `z` over `[0, 1]` at fixed `r ≠ 0`;
* the longitudinal one is integrable over the transverse plane, while the transverse one is
  *not* whenever `ε > 0`: it is bounded below by a multiple of `exp (-2 ε r) / r²`, so its
  normalisation diverges logarithmically at small `r`. Only after weighting by a dipole cross
  section that vanishes like `r²` at the origin (colour transparency) is the transverse cross
  section finite;
* at fixed `r ≠ 0` both depend continuously on `(m_f, Q²)` where `ε > 0`; in particular the
  massless limit of either exists at `Q² > 0` and `0 < z < 1`;
* the real-photon limit: as `Q² → 0` the longitudinal wave function vanishes, for every quark mass
  (including `m_f = 0`, where `ε → 0`), while for `m_f ≠ 0` the transverse one tends to the
  positive value `(2 N_c α_em e_f² / π) m_f² [(z² + (1-z)²) K₁(|m_f| r)² + K₀(|m_f| r)²]`.

## Main definitions

* `EpsilonEridani.QFT.SmallX.photonEpsilon m Q2 z`: the scale `ε = √(z (1 - z) Q² + m²)`.
* `EpsilonEridani.QFT.SmallX.photonWaveFunctionSqT`,
  `EpsilonEridani.QFT.SmallX.photonWaveFunctionSqL`: the squared transverse and longitudinal
  wave functions `|Ψ_T|²`, `|Ψ_L|²` as functions of the transverse separation vector `r`.

## Main statements

* `photonWaveFunctionSqT_nonneg`, `photonWaveFunctionSqL_nonneg`, `photonWaveFunctionSqT_pos`,
  `photonWaveFunctionSqL_pos`: positivity.
* `photonWaveFunctionSqT_le`, `photonWaveFunctionSqL_le`: exponential suppression of large dipoles.
* `photonWaveFunctionSqT_le_inv_sq`, `photonWaveFunctionSqL_le_inv_sq`: the uniform `1 / r²` bound,
  sharp for `|Ψ_T|²` by `mul_exp_neg_div_sq_le_photonWaveFunctionSqT`.
* `photonWaveFunctionSqL_le_div`: the bound on `|Ψ_L|²` through `K_{1/2}`, integrable at `r = 0`.
* `integrableOn_photonWaveFunctionSqT`, `integrableOn_photonWaveFunctionSqL`: integrability in `z`.
* `integrable_photonWaveFunctionSqL`: integrability of `|Ψ_L|²` over the transverse plane.
* `not_integrable_photonWaveFunctionSqT`: non-integrability of `|Ψ_T|²` over the transverse plane.
* `continuousAt_photonWaveFunctionSqT`, `continuousAt_photonWaveFunctionSqL`: continuity in the
  quark mass and the virtuality.
* `tendsto_photonWaveFunctionSqL_nhdsGE_zero`, `tendsto_photonWaveFunctionSqT_nhds_zero`: the
  real-photon limit.

## References

* N. N. Nikolaev and B. G. Zakharov, *Colour transparency and scaling properties of nuclear
  shadowing in deep inelastic scattering*, Z. Phys. C **49** (1991) 607.
* H. Kowalski and D. Teaney, *An impact parameter dipole saturation model*, Phys. Rev. D **68**
  (2003) 114005, eqs. (5)–(6).
* Yu. V. Kovchegov and E. Levin, *Quantum Chromodynamics at High Energy*, Cambridge University
  Press (2012), §4.1.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Real MeasureTheory Set Filter Topology

/-! ### The scale `ε` -/

/-- The scale `ε = √(z (1 - z) Q² + m²)` that governs the transverse extent of a quark-antiquark
fluctuation of mass `m` and light-cone momentum fraction `z` of a photon of virtuality `Q²`. -/
def photonEpsilon (m Q2 z : ℝ) : ℝ :=
  √(z * (1 - z) * Q2 + m ^ 2)

/-- The defining formula of `photonEpsilon`. -/
theorem photonEpsilon_def (m Q2 z : ℝ) : photonEpsilon m Q2 z = √(z * (1 - z) * Q2 + m ^ 2) :=
  (rfl)

/-- `ε` is a square root, hence non-negative. -/
theorem photonEpsilon_nonneg (m Q2 z : ℝ) : 0 ≤ photonEpsilon m Q2 z :=
  sqrt_nonneg _

/-- `ε > 0` exactly when its square `z (1 - z) Q² + m²` is positive. -/
theorem photonEpsilon_pos_iff {m Q2 z : ℝ} :
    0 < photonEpsilon m Q2 z ↔ 0 < z * (1 - z) * Q2 + m ^ 2 :=
  sqrt_pos

/-- At a positive virtuality and an interior momentum fraction, `ε > 0` for every quark mass. -/
theorem photonEpsilon_pos {m Q2 z : ℝ} (hQ : 0 < Q2) (hz : z ∈ Ioo 0 1) :
    0 < photonEpsilon m Q2 z :=
  photonEpsilon_pos_iff.2 (by have := hz.1; have := sub_pos.2 hz.2; positivity)

/-- `ε` is symmetric under exchanging the quark and the antiquark, `z ↦ 1 - z`. -/
theorem photonEpsilon_one_sub (m Q2 z : ℝ) : photonEpsilon m Q2 (1 - z) = photonEpsilon m Q2 z := by
  rw [photonEpsilon_def, photonEpsilon_def]
  ring_nf

/-- For a real photon, `ε = |m|`. -/
@[simp]
theorem photonEpsilon_zero_virtuality (m z : ℝ) : photonEpsilon m 0 z = |m| := by
  rw [photonEpsilon_def, mul_zero, zero_add, sqrt_sq_eq_abs]

/-- On the physical region `Q² ≥ 0`, `0 ≤ z ≤ 1`, `ε² = z (1 - z) Q² + m²`. -/
theorem photonEpsilon_sq {m Q2 z : ℝ} (hQ : 0 ≤ Q2) (hz : z ∈ Icc 0 1) :
    photonEpsilon m Q2 z ^ 2 = z * (1 - z) * Q2 + m ^ 2 :=
  sq_sqrt (by have := hz.1; have := sub_nonneg.2 hz.2; positivity)

/-! ### The squared wave functions -/

/-- The squared light-cone wave function `|Ψ_T|²` of a transversely polarised photon of virtuality
`Q2` splitting into a quark-antiquark pair of charge `e` (in units of the positron charge) and
mass `m`, with momentum fraction `z` and transverse separation `r`, summed over helicities and
the `Nc` colours, at fine-structure constant `αem`. -/
def photonWaveFunctionSqT (Nc : ℕ) (αem e m Q2 z : ℝ) (r : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  2 * Nc * αem * e ^ 2 / π *
    ((z ^ 2 + (1 - z) ^ 2) * photonEpsilon m Q2 z ^ 2 * besselK 1 (photonEpsilon m Q2 z * ‖r‖) ^ 2
      + m ^ 2 * besselK 0 (photonEpsilon m Q2 z * ‖r‖) ^ 2)

/-- The squared light-cone wave function `|Ψ_L|²` of a longitudinally polarised photon, in the
normalisation of `photonWaveFunctionSqT`. -/
def photonWaveFunctionSqL (Nc : ℕ) (αem e m Q2 z : ℝ) (r : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  2 * Nc * αem * e ^ 2 / π *
    (4 * Q2 * z ^ 2 * (1 - z) ^ 2 * besselK 0 (photonEpsilon m Q2 z * ‖r‖) ^ 2)

variable {Nc : ℕ} {αem e m Q2 z : ℝ} {r : EuclideanSpace ℝ (Fin 2)}

/-- The defining formula of `photonWaveFunctionSqT`. -/
theorem photonWaveFunctionSqT_def (Nc : ℕ) (αem e m Q2 z : ℝ) (r : EuclideanSpace ℝ (Fin 2)) :
    photonWaveFunctionSqT Nc αem e m Q2 z r = 2 * Nc * αem * e ^ 2 / π *
      ((z ^ 2 + (1 - z) ^ 2) * photonEpsilon m Q2 z ^ 2 *
          besselK 1 (photonEpsilon m Q2 z * ‖r‖) ^ 2 +
        m ^ 2 * besselK 0 (photonEpsilon m Q2 z * ‖r‖) ^ 2) :=
  (rfl)

/-- The defining formula of `photonWaveFunctionSqL`. -/
theorem photonWaveFunctionSqL_def (Nc : ℕ) (αem e m Q2 z : ℝ) (r : EuclideanSpace ℝ (Fin 2)) :
    photonWaveFunctionSqL Nc αem e m Q2 z r = 2 * Nc * αem * e ^ 2 / π *
      (4 * Q2 * z ^ 2 * (1 - z) ^ 2 * besselK 0 (photonEpsilon m Q2 z * ‖r‖) ^ 2) :=
  (rfl)

/-- `|Ψ_T|²` is symmetric under exchanging the quark and the antiquark. -/
theorem photonWaveFunctionSqT_one_sub :
    photonWaveFunctionSqT Nc αem e m Q2 (1 - z) r = photonWaveFunctionSqT Nc αem e m Q2 z r := by
  simp only [photonWaveFunctionSqT_def, photonEpsilon_one_sub]
  ring

/-- `|Ψ_L|²` is symmetric under exchanging the quark and the antiquark. -/
theorem photonWaveFunctionSqL_one_sub :
    photonWaveFunctionSqL Nc αem e m Q2 (1 - z) r = photonWaveFunctionSqL Nc αem e m Q2 z r := by
  simp only [photonWaveFunctionSqL_def, photonEpsilon_one_sub]
  ring

/-! ### Positivity -/

/-- `|Ψ_T|² ≥ 0` for every momentum fraction, virtuality, quark mass and separation. -/
theorem photonWaveFunctionSqT_nonneg (hα : 0 ≤ αem) :
    0 ≤ photonWaveFunctionSqT Nc αem e m Q2 z r := by
  rw [photonWaveFunctionSqT_def]
  positivity

/-- `|Ψ_L|² ≥ 0` at every non-negative virtuality. -/
theorem photonWaveFunctionSqL_nonneg (hα : 0 ≤ αem) (hQ : 0 ≤ Q2) :
    0 ≤ photonWaveFunctionSqL Nc αem e m Q2 z r := by
  rw [photonWaveFunctionSqL_def]
  positivity

/-- `|Ψ_T|² > 0` at every nonzero separation once `ε > 0`. -/
theorem photonWaveFunctionSqT_pos (hNc : Nc ≠ 0) (hα : 0 < αem) (he : e ≠ 0)
    (hε : 0 < photonEpsilon m Q2 z) (hr : r ≠ 0) : 0 < photonWaveFunctionSqT Nc αem e m Q2 z r := by
  have hz : 0 < z ^ 2 + (1 - z) ^ 2 := by nlinarith [sq_nonneg (2 * z - 1)]
  have hK := besselK_pos 1 (mul_pos hε (norm_pos_iff.2 hr))
  rw [photonWaveFunctionSqT_def]
  positivity

/-- `|Ψ_L|² > 0` at every nonzero separation for `Q² > 0` and `0 < z < 1`. -/
theorem photonWaveFunctionSqL_pos (hNc : Nc ≠ 0) (hα : 0 < αem) (he : e ≠ 0) (hQ : 0 < Q2)
    (hz : z ∈ Ioo 0 1) (hr : r ≠ 0) : 0 < photonWaveFunctionSqL Nc αem e m Q2 z r := by
  have hK := besselK_pos 0 (mul_pos (photonEpsilon_pos (m := m) hQ hz) (norm_pos_iff.2 hr))
  have := hz.1
  have := sub_pos.2 hz.2
  rw [photonWaveFunctionSqL_def]
  positivity

/-- The normalisation `2 N_c α_em e_f² / π` enters linearly, so statements that do not depend on
its sign reduce to `α_em = 1`. -/
private theorem photonWaveFunctionSqT_eq_mul :
    photonWaveFunctionSqT Nc αem e m Q2 z r = αem * photonWaveFunctionSqT Nc 1 e m Q2 z r := by
  simp only [photonWaveFunctionSqT_def]
  ring

private theorem photonWaveFunctionSqL_eq_mul :
    photonWaveFunctionSqL Nc αem e m Q2 z r = αem * photonWaveFunctionSqL Nc 1 e m Q2 z r := by
  simp only [photonWaveFunctionSqL_def]
  ring

/-! ### Bounds in the dipole size -/

/-- The estimate `ε K₁(ε r) ≤ (ε + 1/r) exp (-ε r)` underlying both large-dipole bounds, squared. -/
private theorem sq_photonEpsilon_mul_besselK_one_le (hr : r ≠ 0) :
    (photonEpsilon m Q2 z * besselK 1 (photonEpsilon m Q2 z * ‖r‖)) ^ 2 ≤
      (photonEpsilon m Q2 z + ‖r‖⁻¹) ^ 2 * exp (-(2 * (photonEpsilon m Q2 z * ‖r‖))) := by
  set ε := photonEpsilon m Q2 z
  have hρ : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hε : 0 ≤ ε := photonEpsilon_nonneg m Q2 z
  have hK : ε * besselK 1 (ε * ‖r‖) ≤ (ε + ‖r‖⁻¹) * exp (-(ε * ‖r‖)) := by
    rcases hε.eq_or_lt with h | h
    · rw [← h, zero_mul, zero_mul]
      positivity
    · calc ε * besselK 1 (ε * ‖r‖)
          ≤ ε * (exp (-(ε * ‖r‖)) * (1 + 1 / (ε * ‖r‖))) := by
            gcongr
            exact besselK_one_le_exp_neg_mul (mul_pos h hρ)
        _ = (ε + ‖r‖⁻¹) * exp (-(ε * ‖r‖)) := by
            field_simp
  calc (ε * besselK 1 (ε * ‖r‖)) ^ 2 ≤ ((ε + ‖r‖⁻¹) * exp (-(ε * ‖r‖))) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg hε (besselK_nonneg _ _)) hK 2
    _ = (ε + ‖r‖⁻¹) ^ 2 * exp (-(2 * (ε * ‖r‖))) := by
        rw [mul_pow, sq (exp _), ← exp_add]
        ring_nf

/-- The large-dipole bound `(ε + 1/r)² exp (-2 ε r) ≤ 1 / r²`, uniform in `ε ≥ 0`. -/
private theorem photonEpsilon_add_inv_sq_mul_exp_le (hr : r ≠ 0) :
    (photonEpsilon m Q2 z + ‖r‖⁻¹) ^ 2 * exp (-(2 * (photonEpsilon m Q2 z * ‖r‖))) ≤
      1 / ‖r‖ ^ 2 := by
  set ε := photonEpsilon m Q2 z
  have hρ : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hε : 0 ≤ ε := photonEpsilon_nonneg m Q2 z
  -- `(1 + y) exp (-y) ≤ exp y exp (-y) = 1` at `y = ε r`.
  have hy : (1 + ε * ‖r‖) * exp (-(ε * ‖r‖)) ≤ 1 := by
    calc (1 + ε * ‖r‖) * exp (-(ε * ‖r‖)) ≤ exp (ε * ‖r‖) * exp (-(ε * ‖r‖)) := by
          gcongr
          linarith [add_one_le_exp (ε * ‖r‖)]
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  have hy0 : 0 ≤ (1 + ε * ‖r‖) * exp (-(ε * ‖r‖)) := by positivity
  calc (ε + ‖r‖⁻¹) ^ 2 * exp (-(2 * (ε * ‖r‖)))
      = ((1 + ε * ‖r‖) * exp (-(ε * ‖r‖))) ^ 2 / ‖r‖ ^ 2 := by
        rw [mul_pow, sq (exp _), ← exp_add]
        field_simp
        ring_nf
    _ ≤ 1 / ‖r‖ ^ 2 := by
        gcongr
        exact pow_le_one₀ hy0 hy

/-- Large dipoles are exponentially suppressed in the transverse wave function:
`|Ψ_T|² ≤ (4 N_c α_em e_f² / π) (ε + 1/r)² exp (-2 ε r)`. -/
theorem photonWaveFunctionSqT_le (hα : 0 ≤ αem) (hQ : 0 ≤ Q2) (hz : z ∈ Icc 0 1) (hr : r ≠ 0) :
    photonWaveFunctionSqT Nc αem e m Q2 z r ≤ 4 * Nc * αem * e ^ 2 / π *
      ((photonEpsilon m Q2 z + ‖r‖⁻¹) ^ 2 * exp (-(2 * (photonEpsilon m Q2 z * ‖r‖)))) := by
  set ε := photonEpsilon m Q2 z
  have hK := sq_photonEpsilon_mul_besselK_one_le (m := m) (Q2 := Q2) (z := z) hr
  set K₀ := besselK 0 (ε * ‖r‖)
  set K₁ := besselK 1 (ε * ‖r‖)
  have hzz : z ^ 2 + (1 - z) ^ 2 ≤ 1 := by nlinarith [hz.1, hz.2]
  have hm : m ^ 2 ≤ ε ^ 2 := by
    rw [photonEpsilon_sq hQ hz]
    nlinarith [mul_nonneg (mul_nonneg hz.1 (sub_nonneg.2 hz.2)) hQ]
  have hK₀ : K₀ ^ 2 ≤ K₁ ^ 2 :=
    pow_le_pow_left₀ (besselK_nonneg _ _) (besselK_le_besselK (by norm_num) _) 2
  have h₁ : (z ^ 2 + (1 - z) ^ 2) * ε ^ 2 * K₁ ^ 2 ≤ (ε * K₁) ^ 2 := by
    rw [mul_assoc, mul_pow]
    exact mul_le_of_le_one_left (by positivity) hzz
  have h₂ : m ^ 2 * K₀ ^ 2 ≤ (ε * K₁) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul hm hK₀ (sq_nonneg _) (sq_nonneg _)
  rw [photonWaveFunctionSqT_def]
  calc 2 * Nc * αem * e ^ 2 / π * ((z ^ 2 + (1 - z) ^ 2) * ε ^ 2 * K₁ ^ 2 + m ^ 2 * K₀ ^ 2)
      ≤ 2 * Nc * αem * e ^ 2 / π * (2 * ((ε + ‖r‖⁻¹) ^ 2 * exp (-(2 * (ε * ‖r‖))))) := by
        gcongr
        linarith
    _ = _ := by ring

/-- Large dipoles are exponentially suppressed in the longitudinal wave function:
`|Ψ_L|² ≤ (2 N_c α_em e_f² / π) (ε + 1/r)² exp (-2 ε r)`. -/
theorem photonWaveFunctionSqL_le (hα : 0 ≤ αem) (hQ : 0 ≤ Q2) (hz : z ∈ Icc 0 1) (hr : r ≠ 0) :
    photonWaveFunctionSqL Nc αem e m Q2 z r ≤ 2 * Nc * αem * e ^ 2 / π *
      ((photonEpsilon m Q2 z + ‖r‖⁻¹) ^ 2 * exp (-(2 * (photonEpsilon m Q2 z * ‖r‖)))) := by
  set ε := photonEpsilon m Q2 z
  have hK := sq_photonEpsilon_mul_besselK_one_le (m := m) (Q2 := Q2) (z := z) hr
  set K₀ := besselK 0 (ε * ‖r‖)
  set K₁ := besselK 1 (ε * ‖r‖)
  have hzQ : 0 ≤ z * (1 - z) * Q2 := mul_nonneg (mul_nonneg hz.1 (sub_nonneg.2 hz.2)) hQ
  have hε : 4 * Q2 * z ^ 2 * (1 - z) ^ 2 ≤ ε ^ 2 := by
    rw [photonEpsilon_sq hQ hz]
    nlinarith [sq_nonneg (2 * z - 1), sq_nonneg m]
  have hK₀ : K₀ ^ 2 ≤ K₁ ^ 2 :=
    pow_le_pow_left₀ (besselK_nonneg _ _) (besselK_le_besselK (by norm_num) _) 2
  have h : 4 * Q2 * z ^ 2 * (1 - z) ^ 2 * K₀ ^ 2 ≤ (ε * K₁) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul hε hK₀ (sq_nonneg _) (sq_nonneg _)
  rw [photonWaveFunctionSqL_def]
  exact mul_le_mul_of_nonneg_left (h.trans hK) (by positivity)

/-- The transverse wave function is bounded by `4 N_c α_em e_f² / (π r²)`, uniformly in the
momentum fraction, the virtuality and the quark mass. -/
theorem photonWaveFunctionSqT_le_inv_sq (hα : 0 ≤ αem) (hQ : 0 ≤ Q2) (hz : z ∈ Icc 0 1)
    (hr : r ≠ 0) :
    photonWaveFunctionSqT Nc αem e m Q2 z r ≤ 4 * Nc * αem * e ^ 2 / π * (1 / ‖r‖ ^ 2) :=
  (photonWaveFunctionSqT_le hα hQ hz hr).trans
    (by gcongr; exact photonEpsilon_add_inv_sq_mul_exp_le hr)

/-- The longitudinal wave function is bounded by `2 N_c α_em e_f² / (π r²)`, uniformly in the
momentum fraction, the virtuality and the quark mass. -/
theorem photonWaveFunctionSqL_le_inv_sq (hα : 0 ≤ αem) (hQ : 0 ≤ Q2) (hz : z ∈ Icc 0 1)
    (hr : r ≠ 0) :
    photonWaveFunctionSqL Nc αem e m Q2 z r ≤ 2 * Nc * αem * e ^ 2 / π * (1 / ‖r‖ ^ 2) :=
  (photonWaveFunctionSqL_le hα hQ hz hr).trans
    (by gcongr; exact photonEpsilon_add_inv_sq_mul_exp_le hr)

/-- The longitudinal wave function in terms of `K_{1/2}`: since `K₀(y) ≤ √(π / 2y) exp (-y)`,
`|Ψ_L|² ≤ 4 N_c α_em e_f² Q² z² (1-z)² exp (-2 ε r) / (ε r)`. Unlike `photonWaveFunctionSqL_le`
this is integrable against `d²r` at the origin. -/
theorem photonWaveFunctionSqL_le_div (hα : 0 ≤ αem) (hQ : 0 ≤ Q2) (hr : r ≠ 0)
    (hε : 0 < photonEpsilon m Q2 z) :
    photonWaveFunctionSqL Nc αem e m Q2 z r ≤ 4 * Nc * αem * e ^ 2 *
      (Q2 * z ^ 2 * (1 - z) ^ 2) * exp (-(2 * (photonEpsilon m Q2 z * ‖r‖))) /
        (photonEpsilon m Q2 z * ‖r‖) := by
  set y := photonEpsilon m Q2 z * ‖r‖
  have hy : 0 < y := mul_pos hε (norm_pos_iff.2 hr)
  have hK : besselK 0 y ^ 2 ≤ π / (2 * y) * exp (-(2 * y)) := by
    calc besselK 0 y ^ 2 ≤ (√(π / (2 * y)) * exp (-y)) ^ 2 :=
          pow_le_pow_left₀ (besselK_nonneg _ _) (besselK_le_sqrt_mul_exp (by norm_num) hy) 2
      _ = π / (2 * y) * exp (-(2 * y)) := by
          rw [mul_pow, sq_sqrt (by positivity), sq (exp _), ← exp_add]
          ring_nf
  rw [photonWaveFunctionSqL_def]
  calc 2 * Nc * αem * e ^ 2 / π * (4 * Q2 * z ^ 2 * (1 - z) ^ 2 * besselK 0 y ^ 2)
      ≤ 2 * Nc * αem * e ^ 2 / π * (4 * Q2 * z ^ 2 * (1 - z) ^ 2 *
          (π / (2 * y) * exp (-(2 * y)))) := by
        gcongr
    _ = _ := by
        field_simp

/-! ### Integrability -/

/-- At fixed nonzero separation, `|Ψ_T|²` is integrable in the momentum fraction. -/
theorem integrableOn_photonWaveFunctionSqT (hQ : 0 ≤ Q2) (hr : r ≠ 0) :
    IntegrableOn (fun z ↦ photonWaveFunctionSqT Nc αem e m Q2 z r) (Icc 0 1) := by
  simp_rw [photonWaveFunctionSqT_eq_mul (αem := αem)]
  have h1 : IntegrableOn (fun z ↦ photonWaveFunctionSqT Nc 1 e m Q2 z r) (Icc 0 1) :=
    IntegrableOn.of_bound measure_Icc_lt_top ?_ (4 * Nc * 1 * e ^ 2 / π * (1 / ‖r‖ ^ 2))
      ((ae_restrict_mem measurableSet_Icc).mono fun z hz ↦ ?_)
  · exact h1.const_mul αem
  · simp only [photonWaveFunctionSqT_def, photonEpsilon_def]
    fun_prop
  · rw [Real.norm_of_nonneg (photonWaveFunctionSqT_nonneg zero_le_one)]
    exact photonWaveFunctionSqT_le_inv_sq zero_le_one hQ hz hr

/-- At fixed nonzero separation, `|Ψ_L|²` is integrable in the momentum fraction. -/
theorem integrableOn_photonWaveFunctionSqL (hQ : 0 ≤ Q2) (hr : r ≠ 0) :
    IntegrableOn (fun z ↦ photonWaveFunctionSqL Nc αem e m Q2 z r) (Icc 0 1) := by
  simp_rw [photonWaveFunctionSqL_eq_mul (αem := αem)]
  have h1 : IntegrableOn (fun z ↦ photonWaveFunctionSqL Nc 1 e m Q2 z r) (Icc 0 1) :=
    IntegrableOn.of_bound measure_Icc_lt_top ?_ (2 * Nc * 1 * e ^ 2 / π * (1 / ‖r‖ ^ 2))
      ((ae_restrict_mem measurableSet_Icc).mono fun z hz ↦ ?_)
  · exact h1.const_mul αem
  · simp only [photonWaveFunctionSqL_def, photonEpsilon_def]
    fun_prop
  · rw [Real.norm_of_nonneg (photonWaveFunctionSqL_nonneg zero_le_one hQ)]
    exact photonWaveFunctionSqL_le_inv_sq zero_le_one hQ hz hr

/-- `|Ψ_L|²` is integrable over the transverse plane: `K₀` diverges only logarithmically at
the origin. -/
theorem integrable_photonWaveFunctionSqL :
    Integrable (photonWaveFunctionSqL Nc αem e m Q2 z) := by
  set ε := photonEpsilon m Q2 z
  have hfun : photonWaveFunctionSqL Nc αem e m Q2 z = fun r ↦
      2 * Nc * αem * e ^ 2 / π * (4 * Q2 * z ^ 2 * (1 - z) ^ 2) * besselK 0 (ε * ‖r‖) ^ 2 := by
    ext r
    rw [photonWaveFunctionSqL_def]
    ring
  rw [hfun]
  refine Integrable.const_mul ?_ _
  rw [integrable_fun_norm_addHaar volume (f := fun ρ ↦ besselK 0 (ε * ρ) ^ 2),
    finrank_euclideanSpace_fin]
  simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul]
  rcases (show 0 ≤ ε from photonEpsilon_nonneg m Q2 z).eq_or_lt with h | h
  · simp [← h, besselK_of_nonpos 0 le_rfl]
  -- `ρ K₀(ε ρ)² ≤ π / (2 ε) exp (-2 ε ρ)`.
  refine ((exp_neg_integrableOn_Ioi 0 (mul_pos two_pos h)).const_mul (π / (2 * ε))).mono'
    (by fun_prop) ((ae_restrict_mem measurableSet_Ioi).mono fun ρ (hρ : 0 < ρ) ↦ ?_)
  have hy : 0 < ε * ρ := mul_pos h hρ
  have hK : besselK 0 (ε * ρ) ^ 2 ≤ π / (2 * (ε * ρ)) * exp (-(2 * (ε * ρ))) := by
    calc besselK 0 (ε * ρ) ^ 2 ≤ (√(π / (2 * (ε * ρ))) * exp (-(ε * ρ))) ^ 2 :=
          pow_le_pow_left₀ (besselK_nonneg _ _) (besselK_le_sqrt_mul_exp (by norm_num) hy) 2
      _ = π / (2 * (ε * ρ)) * exp (-(2 * (ε * ρ))) := by
          rw [mul_pow, sq_sqrt (by positivity), sq (exp _), ← exp_add]
          ring_nf
  rw [Real.norm_of_nonneg (by positivity)]
  calc ρ * besselK 0 (ε * ρ) ^ 2 ≤ ρ * (π / (2 * (ε * ρ)) * exp (-(2 * (ε * ρ)))) := by gcongr
    _ = π / (2 * ε) * exp (-(2 * ε) * ρ) := by
        field_simp

/-- The `1 / r²` behaviour of `|Ψ_T|²` at small `r` is sharp: once `ε > 0`,
`(N_c α_em e_f² / π) exp (-2 ε r) / r² ≤ |Ψ_T|²`, from `exp (-y) / y < K₁(y)`. -/
theorem mul_exp_neg_div_sq_le_photonWaveFunctionSqT (hα : 0 ≤ αem)
    (hε : 0 < photonEpsilon m Q2 z) (hr : r ≠ 0) :
    Nc * αem * e ^ 2 / π * (exp (-(2 * (photonEpsilon m Q2 z * ‖r‖))) / ‖r‖ ^ 2) ≤
      photonWaveFunctionSqT Nc αem e m Q2 z r := by
  set ε := photonEpsilon m Q2 z
  have hρ : 0 < ‖r‖ := norm_pos_iff.2 hr
  have hy : 0 < ε * ‖r‖ := mul_pos hε hρ
  -- `exp (-ε r) / r < ε K₁(ε r)`, squared.
  have hK : exp (-(ε * ‖r‖)) / ‖r‖ < ε * besselK 1 (ε * ‖r‖) := by
    have := exp_neg_div_lt_besselK_one hy
    rw [div_lt_iff₀ hy] at this
    rw [div_lt_iff₀ hρ]
    linarith
  have hK2 : exp (-(2 * (ε * ‖r‖))) / ‖r‖ ^ 2 ≤ ε ^ 2 * besselK 1 (ε * ‖r‖) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hK.le 2
    rw [div_pow, sq (exp _), ← exp_add] at this
    rw [← mul_pow]
    convert this using 3
    ring
  have hzz : 1 / 2 ≤ z ^ 2 + (1 - z) ^ 2 := by nlinarith [sq_nonneg (2 * z - 1)]
  rw [photonWaveFunctionSqT_def]
  calc Nc * αem * e ^ 2 / π * (exp (-(2 * (ε * ‖r‖))) / ‖r‖ ^ 2)
      = 2 * Nc * αem * e ^ 2 / π * (1 / 2 * (exp (-(2 * (ε * ‖r‖))) / ‖r‖ ^ 2)) := by ring
    _ ≤ 2 * Nc * αem * e ^ 2 / π * ((z ^ 2 + (1 - z) ^ 2) * ε ^ 2 * besselK 1 (ε * ‖r‖) ^ 2 +
          m ^ 2 * besselK 0 (ε * ‖r‖) ^ 2) := by
        gcongr ?_ * ?_
        have : 0 ≤ m ^ 2 * besselK 0 (ε * ‖r‖) ^ 2 := by positivity
        nlinarith [mul_le_mul hzz hK2 (by positivity) (by positivity)]

/-- `|Ψ_T|²` is **not** integrable over the transverse plane once `ε > 0`: by
`mul_exp_neg_div_sq_le_photonWaveFunctionSqT` its integral against `d²r` diverges
logarithmically at the origin. A dipole cross section vanishing like `r²` at the origin is needed
to make the transverse cross section finite. -/
theorem not_integrable_photonWaveFunctionSqT (hNc : Nc ≠ 0) (hα : αem ≠ 0) (he : e ≠ 0)
    (hε : 0 < photonEpsilon m Q2 z) :
    ¬ Integrable (photonWaveFunctionSqT Nc αem e m Q2 z) := by
  set ε := photonEpsilon m Q2 z
  intro hint
  -- Reduce to `α_em = 1`.
  have h1 : Integrable (photonWaveFunctionSqT Nc 1 e m Q2 z) := by
    have := hint.const_mul αem⁻¹
    simp_rw [photonWaveFunctionSqT_eq_mul (αem := αem), ← mul_assoc, inv_mul_cancel₀ hα,
      one_mul] at this
    exact this
  -- Pass to the radial integral `∫₀^∞ ρ f(ρ) dρ`.
  set f : ℝ → ℝ := fun ρ ↦ 2 * Nc * 1 * e ^ 2 / π * ((z ^ 2 + (1 - z) ^ 2) * ε ^ 2 *
    besselK 1 (ε * ρ) ^ 2 + m ^ 2 * besselK 0 (ε * ρ) ^ 2)
  have hfun : photonWaveFunctionSqT Nc 1 e m Q2 z = fun r ↦ f ‖r‖ := (rfl)
  rw [hfun, integrable_fun_norm_addHaar volume, finrank_euclideanSpace_fin] at h1
  simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul] at h1
  -- On `(0, 1)`, `1 / ρ ≤ (π exp (2 ε) / (N_c e_f²)) ρ f(ρ)`, so `1 / ρ` would be integrable there.
  set c := Nc * 1 * e ^ 2 / π
  have hc : 0 < c := by positivity
  have hinv : IntegrableOn (fun ρ : ℝ ↦ ρ⁻¹) (Ioo 0 1) := by
    refine ((h1.mono_set Ioo_subset_Ioi_self).const_mul (exp (2 * ε) / c)).mono'
      (by fun_prop) ((ae_restrict_mem measurableSet_Ioo).mono fun ρ hρ ↦ ?_)
    have hρ0 : 0 < ρ := hρ.1
    obtain ⟨r, hr⟩ : ∃ r : EuclideanSpace ℝ (Fin 2), ‖r‖ = ρ :=
      ⟨ρ • EuclideanSpace.single 0 1, by simp [norm_smul, hρ0.le]⟩
    have hf := mul_exp_neg_div_sq_le_photonWaveFunctionSqT (Nc := Nc) (e := e) zero_le_one hε
      (r := r) (by rintro rfl; simp at hr; linarith)
    simp only [hfun, hr] at hf
    have hexp : exp (-(2 * ε)) ≤ exp (-(2 * (ε * ρ))) := by
      gcongr
      nlinarith [hρ.2]
    rw [Real.norm_of_nonneg (inv_pos.2 hρ0).le]
    calc ρ⁻¹ = exp (2 * ε) / c * (ρ * (c * (exp (-(2 * ε)) / ρ ^ 2))) := by
          rw [exp_neg]
          field_simp
      _ ≤ exp (2 * ε) / c * (ρ * f ρ) := by
          gcongr
          refine (mul_le_mul_of_nonneg_left ?_ hc.le).trans hf
          exact div_le_div_of_nonneg_right hexp (by positivity)
  have := (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).2 hinv
  simp at this

/-! ### Dependence on the quark mass and the virtuality -/

/-- `|Ψ_T|²` is jointly continuous in the quark mass and the virtuality wherever `ε > 0`. -/
theorem continuousAt_photonWaveFunctionSqT {p : ℝ × ℝ} (hε : 0 < photonEpsilon p.1 p.2 z)
    (hr : r ≠ 0) :
    ContinuousAt (fun q : ℝ × ℝ ↦ photonWaveFunctionSqT Nc αem e q.1 q.2 z r) p := by
  have hy : 0 < photonEpsilon p.1 p.2 z * ‖r‖ := mul_pos hε (norm_pos_iff.2 hr)
  have hK (ν : ℝ) : ContinuousAt (besselK ν) (photonEpsilon p.1 p.2 z * ‖r‖) :=
    (continuousOn_besselK ν).continuousAt (Ioi_mem_nhds hy)
  have := hK 0
  have := hK 1
  simp only [photonWaveFunctionSqT_def, photonEpsilon_def] at this ⊢
  fun_prop

/-- `|Ψ_L|²` is jointly continuous in the quark mass and the virtuality wherever `ε > 0`; in
particular its massless limit exists at `Q² > 0` and `0 < z < 1`. -/
theorem continuousAt_photonWaveFunctionSqL {p : ℝ × ℝ} (hε : 0 < photonEpsilon p.1 p.2 z)
    (hr : r ≠ 0) :
    ContinuousAt (fun q : ℝ × ℝ ↦ photonWaveFunctionSqL Nc αem e q.1 q.2 z r) p := by
  have hy : 0 < photonEpsilon p.1 p.2 z * ‖r‖ := mul_pos hε (norm_pos_iff.2 hr)
  have := (continuousOn_besselK 0).continuousAt (Ioi_mem_nhds hy)
  simp only [photonWaveFunctionSqL_def, photonEpsilon_def] at this ⊢
  fun_prop

/-- The real-photon limit of the transverse wave function: for a massive quark, as `Q² → 0`,
`|Ψ_T|²` tends to `(2 N_c α_em e_f² / π) m² [(z² + (1-z)²) K₁(|m| r)² + K₀(|m| r)²]`, which is
positive (`photonWaveFunctionSqT_pos`). -/
theorem tendsto_photonWaveFunctionSqT_nhds_zero (hm : m ≠ 0) (hr : r ≠ 0) :
    Tendsto (fun Q2 ↦ photonWaveFunctionSqT Nc αem e m Q2 z r) (𝓝 0)
      (𝓝 (2 * Nc * αem * e ^ 2 / π * m ^ 2 *
        ((z ^ 2 + (1 - z) ^ 2) * besselK 1 (|m| * ‖r‖) ^ 2 + besselK 0 (|m| * ‖r‖) ^ 2))) := by
  have h : ContinuousAt (fun Q2 ↦ photonWaveFunctionSqT Nc αem e m Q2 z r) 0 :=
    (continuousAt_photonWaveFunctionSqT (p := (m, 0)) (by simpa using hm) hr).comp
      (f := fun Q2 : ℝ ↦ (m, Q2)) (by fun_prop)
  convert h.tendsto using 2
  simp only [photonWaveFunctionSqT_def, photonEpsilon_zero_virtuality, sq_abs]
  ring

/-- The real-photon limit of the longitudinal wave function: as `Q² → 0⁺`, `|Ψ_L|² → 0`, for every
quark mass including `m = 0`. -/
theorem tendsto_photonWaveFunctionSqL_nhdsGE_zero (hz : z ∈ Icc 0 1) (hr : r ≠ 0) :
    Tendsto (fun Q2 ↦ photonWaveFunctionSqL Nc αem e m Q2 z r) (𝓝[≥] 0) (𝓝 0) := by
  simp_rw [photonWaveFunctionSqL_eq_mul (αem := αem)]
  suffices h : Tendsto (fun Q2 ↦ photonWaveFunctionSqL Nc 1 e m Q2 z r) (𝓝[≥] 0) (𝓝 0) by
    simpa using h.const_mul αem
  have hρ : 0 < ‖r‖ := norm_pos_iff.2 hr
  -- `|Ψ_L|² ≤ N_c e_f² √(z (1 - z) Q²) / r` for `Q² ≥ 0`.
  have hlim : Tendsto (fun Q2 ↦ Nc * e ^ 2 * √(z * (1 - z) * Q2) / ‖r‖) (𝓝[≥] 0) (𝓝 0) := by
    have : Tendsto (fun Q2 ↦ Nc * e ^ 2 * √(z * (1 - z) * Q2) / ‖r‖) (𝓝 0)
        (𝓝 (Nc * e ^ 2 * √(z * (1 - z) * 0) / ‖r‖)) :=
      (by fun_prop : Continuous fun Q2 ↦ Nc * e ^ 2 * √(z * (1 - z) * Q2) / ‖r‖).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with Q2 (hQ : 0 ≤ Q2)
    exact photonWaveFunctionSqL_nonneg zero_le_one hQ
  filter_upwards [self_mem_nhdsWithin] with Q2 (hQ : 0 ≤ Q2)
  set ε := photonEpsilon m Q2 z
  set w := z * (1 - z) * Q2
  have hw : 0 ≤ w := mul_nonneg (mul_nonneg hz.1 (sub_nonneg.2 hz.2)) hQ
  rcases (photonEpsilon_nonneg m Q2 z).eq_or_lt with h | h
  · rw [photonWaveFunctionSqL_def, ← h, zero_mul, besselK_of_nonpos 0 le_rfl]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    positivity
  have hwε : √w ≤ ε := sqrt_le_sqrt (by nlinarith [sq_nonneg m])
  -- `Q² z² (1 - z)² / ε = z (1 - z) w / ε ≤ √w / 4`.
  have hkey : Q2 * z ^ 2 * (1 - z) ^ 2 / ε ≤ √w / 4 := by
    rw [div_le_iff₀ h]
    have hsq : w = √w * √w := (mul_self_sqrt hw).symm
    have h4 : z * (1 - z) ≤ 1 / 4 := by nlinarith [sq_nonneg (2 * z - 1)]
    calc Q2 * z ^ 2 * (1 - z) ^ 2 = z * (1 - z) * w := by ring
      _ ≤ 1 / 4 * w := by gcongr
      _ = 1 / 4 * (√w * √w) := by rw [← hsq]
      _ ≤ √w / 4 * ε := by nlinarith [sqrt_nonneg w]
  calc photonWaveFunctionSqL Nc 1 e m Q2 z r
      ≤ 4 * Nc * 1 * e ^ 2 * (Q2 * z ^ 2 * (1 - z) ^ 2) * exp (-(2 * (ε * ‖r‖))) /
          (ε * ‖r‖) := photonWaveFunctionSqL_le_div zero_le_one hQ hr h
    _ ≤ 4 * Nc * e ^ 2 * (Q2 * z ^ 2 * (1 - z) ^ 2) / (ε * ‖r‖) := by
        rw [mul_one]
        gcongr ?_ / _
        have := mul_pos h hρ
        exact mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 (by linarith))
    _ = 4 * Nc * e ^ 2 * (Q2 * z ^ 2 * (1 - z) ^ 2 / ε) / ‖r‖ := by
        field_simp
    _ ≤ 4 * Nc * e ^ 2 * (√w / 4) / ‖r‖ := by gcongr
    _ = Nc * e ^ 2 * √w / ‖r‖ := by ring

end SmallX
end QFT
end EpsilonEridani
