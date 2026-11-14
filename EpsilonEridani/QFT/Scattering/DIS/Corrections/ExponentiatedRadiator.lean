/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Convolution.Mellin
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import EpsilonEridani.Mathematics.SpecialFunctions.Gamma.Bounds
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Probability.Distributions.Beta.Basic

/-!
# The exponentiated radiator

The density `D_ee(z, β)` of a lepton carrying momentum fraction `z` of a parent lepton, after
the parent has radiated photons, is concentrated at the soft-photon endpoint `z → 1`. There, the
sum of the leading logarithms to all orders has the closed form of Gribov and Lipatov,

  `D(z) = exp (β (3/4 - γ_E)) / Γ(1 + β) · β (1 - z) ^ (β - 1)`,  `0 < z < 1`,

where `γ_E` is the Euler-Mascheroni constant. Here `β` is the exponent appearing in
`(1 - z) ^ (β - 1)`. It is the QED coupling times the collinear logarithm: for a single lepton line
of mass `m` probed at virtuality `Q²`, leading logarithmic evolution in `ln (Q²/m²)` gives
`β = (α/π) ln (Q²/m²)`, and conventions differ in the non-logarithmic constant added to the
logarithm. Kuraev-Fadin and Skrzypek write the same radiator with exponent `β_ref/2` in place of
`β`, where `β_ref = (2α/π) (ln (Q²/m²) - 1)`, and the roadmap's `β = 2α(L-1)/π` is that `β_ref`;
so `β = β_ref/2`, a factor of two that must be taken into account when comparing. The profile
`β (1 - z) ^ (β - 1)` is the density of the Beta distribution with shape parameters `1` and `β`,
so the radiator is a constant multiple of `ProbabilityTheory.betaPDFReal 1 β`.

The Mellin moments of the radiator are a ratio of Gamma functions
(`mellinDis_exponentiatedRadiator`):

  `∫_{(0,1]} z ^ (N - 1) D(z) dz = exp (β (3/4 - γ_E)) Γ(N) / Γ(N + β)`,  `0 < Re N`.

Since `Γ(N) / Γ(N + β) ~ N ^ (-β)` as `N → ∞`, these moments agree at large `N` with those of the
leading-logarithmic solution of the QED evolution equation, whose diagonal anomalous dimension
behaves like `3/2 - 2 (ln N + γ_E)`. That large-`N` matching is what fixes the factor
`exp (β (3/4 - γ_E)) / Γ(1 + β)`.

The prefactor is fixed at large `N`, not at `N = 1`. So the zeroth moment
`∫_{(0,1]} D(z) dz` is `exp (β (3/4 - γ_E)) / Γ(1 + β)` (`integral_exponentiatedRadiator`), and
it is strictly larger than one for `0 < β ≤ 1` (`one_lt_integral_exponentiatedRadiator`): in that
range the Gribov-Lipatov form alone overstates the total probability. Only its normalised profile,
the Beta density, has zeroth moment one; that is Mathlib's
`ProbabilityTheory.lintegral_betaPDF_eq_one`, and `mellinDis_betaPDFReal_one`.

## Main definitions

* `exponentiatedRadiator β z`: the Gribov-Lipatov exponentiated radiator.

## Main results

* `exponentiatedRadiator_of_mem_Ioo`: the closed form on `0 < z < 1`.
* `mellinDis_exponentiatedRadiator`: its Mellin moments, a ratio of Gamma functions.
* `integral_exponentiatedRadiator`: its zeroth moment.
* `one_lt_integral_exponentiatedRadiator`: the zeroth moment exceeds one for `0 < β ≤ 1`.

## References

* V. N. Gribov and L. N. Lipatov, *Deep inelastic e p scattering in perturbation theory*,
  Sov. J. Nucl. Phys. **15** (1972) 438.
* E. A. Kuraev and V. S. Fadin, *On radiative corrections to e⁺e⁻ single photon annihilation at
  high energy*, Sov. J. Nucl. Phys. **41** (1985) 466.
* M. Skrzypek, *Leading logarithmic calculations of QED corrections at LEP*,
  Acta Phys. Pol. B **23** (1992) 135.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Corrections

open Set MeasureTheory ProbabilityTheory Factorization.Convolution Real

/-- The Gribov-Lipatov **exponentiated radiator** with exponent `β`:
`exp (β (3/4 - γ_E)) / Γ(1 + β) · β (1 - z) ^ (β - 1)` for `0 < z < 1`, and `0` otherwise
(`exponentiatedRadiator_of_mem_Ioo`, `exponentiatedRadiator_of_notMem_Ioo`). It is defined as
that constant times the density `ProbabilityTheory.betaPDFReal 1 β` of the Beta distribution
with shape parameters `1` and `β`. -/
def exponentiatedRadiator (β z : ℝ) : ℝ :=
  Real.exp (β * (3 / 4 - eulerMascheroniConstant)) / Real.Gamma (1 + β) * betaPDFReal 1 β z

/-- The exponentiated radiator is a constant multiple of the Beta density with shape parameters
`1` and `β`. -/
lemma exponentiatedRadiator_def (β : ℝ) :
    exponentiatedRadiator β = fun z =>
      Real.exp (β * (3 / 4 - eulerMascheroniConstant)) / Real.Gamma (1 + β) *
        betaPDFReal 1 β z := (rfl)

/-- The closed form of the exponentiated radiator on the open unit interval. -/
lemma exponentiatedRadiator_of_mem_Ioo {β z : ℝ} (hβ : 0 < β) (hz : z ∈ Ioo (0 : ℝ) 1) :
    exponentiatedRadiator β z =
      Real.exp (β * (3 / 4 - eulerMascheroniConstant)) / Real.Gamma (1 + β) *
        (β * (1 - z) ^ (β - 1)) := by
  simp [exponentiatedRadiator_def, betaPDFReal, hz.1, hz.2, beta_comm, beta_one_right hβ]

/-- The exponentiated radiator vanishes outside the open unit interval. -/
lemma exponentiatedRadiator_of_notMem_Ioo {β z : ℝ} (hz : z ∉ Ioo (0 : ℝ) 1) :
    exponentiatedRadiator β z = 0 := by
  rw [mem_Ioo] at hz
  simp only [exponentiatedRadiator_def, betaPDFReal, hz, ↓reduceIte, mul_zero]

/-- The exponentiated radiator is nonnegative. -/
lemma exponentiatedRadiator_nonneg {β : ℝ} (hβ : 0 < β) (z : ℝ) :
    0 ≤ exponentiatedRadiator β z :=
  mul_nonneg (div_nonneg (Real.exp_pos _).le (Real.Gamma_pos_of_pos (by linarith)).le)
    (TauCeti.Probability.betaPDFReal_nonneg one_pos hβ z)

/-- The Mellin transform of the exponentiated radiator converges on the half plane `0 < Re N`. -/
theorem mellinDisConvergent_exponentiatedRadiator {β : ℝ} (hβ : 0 < β) {N : ℂ}
    (hN : 0 < N.re) : MellinDisConvergent (exponentiatedRadiator β) N := by
  have h : IntegrableOn (fun x : ℝ =>
      ((exp (β * (3 / 4 - eulerMascheroniConstant)) / Gamma (1 + β) : ℝ) : ℂ) *
        ((x : ℂ) ^ (N - 1) * (betaPDFReal 1 β x : ℂ))) (Ioc 0 1) :=
    (mellinDisConvergent_betaPDFReal (a := 1) hβ (N := N) (by simpa using hN)).const_mul _
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioc
  simp only [exponentiatedRadiator_def, Complex.ofReal_mul]
  ring

/-- **Mellin moments of the exponentiated radiator.** On the half plane `0 < Re N`,
`∫_{(0,1]} z ^ (N - 1) D(z) dz = exp (β (3/4 - γ_E)) Γ(N) / Γ(N + β)`. -/
theorem mellinDis_exponentiatedRadiator {β : ℝ} (hβ : 0 < β) {N : ℂ} (hN : 0 < N.re) :
    mellinDis (exponentiatedRadiator β) N =
      exp (β * (3 / 4 - eulerMascheroniConstant)) * Complex.Gamma N /
        Complex.Gamma (N + β) := by
  have hΓ : Complex.Gamma (1 + β) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using (by linarith : (0 : ℝ) < 1 + β))
  have h := mellinDis_const_mul (exp (β * (3 / 4 - eulerMascheroniConstant)) / Gamma (1 + β))
    (betaPDFReal 1 β) N
  rw [mellinDis_betaPDFReal (a := 1) hβ (by simpa using hN)] at h
  rw [exponentiatedRadiator_def, h, Complex.ofReal_div, ← Complex.Gamma_ofReal]
  push_cast
  rw [Complex.Gamma_one, add_sub_cancel_right, show N + 1 + (β : ℂ) - 1 = N + β by ring]
  field_simp

/-- **The zeroth moment of the exponentiated radiator.**
`∫_{(0,1]} D(z) dz = exp (β (3/4 - γ_E)) / Γ(1 + β)`. -/
theorem integral_exponentiatedRadiator {β : ℝ} (hβ : 0 < β) :
    ∫ z in Ioc (0 : ℝ) 1, exponentiatedRadiator β z =
      exp (β * (3 / 4 - eulerMascheroniConstant)) / Gamma (1 + β) := by
  have h := mellinDis_exponentiatedRadiator hβ (N := (0 : ℕ) + 1) (by simp)
  rw [mellinDis_natCast_add_one_eq_ofReal] at h
  simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, Complex.Gamma_one, mul_one] at h
  apply Complex.ofReal_injective
  rw [h, Complex.ofReal_div, ← Complex.Gamma_ofReal, Complex.ofReal_add, Complex.ofReal_one]

/-- **The exponentiated radiator is not normalised.** For `0 < β ≤ 1` its zeroth moment
`exp (β (3/4 - γ_E)) / Γ(1 + β)` is strictly larger than one, so it is not a probability density
on `(0, 1]`. -/
theorem one_lt_integral_exponentiatedRadiator {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1 < ∫ z in Ioc (0 : ℝ) 1, exponentiatedRadiator β z := by
  rw [integral_exponentiatedRadiator hβ]
  have hΓpos : 0 < Real.Gamma (1 + β) := Real.Gamma_pos_of_pos (by linarith)
  have hΓle : Real.Gamma (1 + β) ≤ 1 := Gamma_le_one_of_mem_Icc ⟨by linarith, by linarith⟩
  -- The numerator exceeds one because `γ_E < 2/3 < 3/4`.
  have hexp : 1 < Real.exp (β * (3 / 4 - eulerMascheroniConstant)) :=
    Real.one_lt_exp_iff.mpr
      (mul_pos hβ (by linarith [eulerMascheroniConstant_lt_two_thirds]))
  rw [one_lt_div hΓpos]
  linarith

end Corrections
end DIS
end Scattering
end QFT
end EpsilonEridani
