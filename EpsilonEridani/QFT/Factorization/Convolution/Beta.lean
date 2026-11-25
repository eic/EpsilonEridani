/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Convolution.Strip
public import EpsilonEridani.Mathematics.Probability.Distributions.Beta
import TauCeti.Analysis.SpecialFunctions.Beta.Basic

/-!
# The Mellin transform of the Beta kernel and the Beta density

The endpoint kernel `x ^ (a - 1) (1 - x) ^ (b - 1)` is the standard shape of a parton or lepton
density at the endpoints of `(0, 1]`, and normalised by `Β(a, b)` it is the density
`ProbabilityTheory.betaPDFReal a b` of the Beta distribution. Its Mellin transform is Euler's beta
integral at `(N + a - 1, b)`, a ratio of Gamma functions.

## Main results

* `mellinDisConvergent_rpow_mul_one_sub_rpow_iff`: the transform of the kernel converges exactly
  when `1 - a < Re N` and `0 < b`, with no further hypothesis.
* `mellinDis_rpow_mul_one_sub_rpow_eq_betaIntegral`: the transform of the kernel is
  `Complex.betaIntegral (N + a - 1) b`, at every `N`;
  `mellinDis_rpow_mul_one_sub_rpow`: on the half plane of convergence it is
  `Γ(N + a - 1) Γ(b) / Γ(N + a + b - 1)`.
* `mellinDis_one_sub_rpow`: at `a = 1`, the transform of `(1 - x) ^ b` is `B(N, b + 1)`.
* `mellinDisConvergent_betaPDFReal`, `mellinDisConvergent_betaPDFReal_iff`,
  `mellinDis_betaPDFReal_eq_betaIntegral`, `mellinDis_betaPDFReal`: the same for the Beta density,
  whose transform is `Β(N + a - 1, b) / Β(a, b)`;
  `mellinDis_betaPDFReal_one`: at `N = 1` this is one, the normalisation of the density.

`mellinDis_betaPDFReal` and `mellinDisConvergent_betaPDFReal_iff` are the complex-index versions
of TauCeti's real-exponent moments of the Beta distribution:
`TauCeti.Probability.integral_rpow_mul_one_sub_rpow_betaMeasure` gives `∫ x ^ q (1 - x) ^ s`
against the Beta measure as `Β(a + q, b + s) / Β(a, b)` (the real-`N` case is `q = N - 1`,
`s = 0`), and `TauCeti.Probability.integrable_rpow_mul_one_sub_rpow_betaMeasure_iff` is the
matching integrability criterion `0 < a + q ∧ 0 < b + s`.
`TauCeti.Probability.integral_pow_betaMeasure` is their natural-index case, the raw moments as a
quotient of Gamma functions. The convergence criterion here reduces to TauCeti's
`TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff`, and the values follow the same route through
Euler's beta integral.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Convolution

/-!
## The Beta kernel
-/

/-- The transform of the Beta kernel `x ^ (a - 1) (1 - x) ^ (b - 1)` converges exactly on the
half plane `1 - a < Re N`, and only when `0 < b`. -/
theorem mellinDisConvergent_rpow_mul_one_sub_rpow_iff {a b : ℝ} {N : ℂ} :
    MellinDisConvergent (fun x => x ^ (a - 1) * (1 - x) ^ (b - 1)) N ↔
      0 < N.re + a - 1 ∧ 0 < b := by
  rw [mellinDisConvergent_iff_integrableOn_rpow_mul, integrableOn_Ioc_iff_integrableOn_Ioo,
    integrableOn_congr_fun (g := fun x : ℝ => x ^ ((N.re + a - 1) - 1) * (1 - x) ^ (b - 1))
      (fun x hx => by
        rw [← mul_assoc, ← Real.rpow_add hx.1, show N.re - 1 + (a - 1) = N.re + a - 1 - 1 by ring])
      measurableSet_Ioo,
    TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff]

/-- The transform of the Beta kernel is Euler's beta integral at `(N + a - 1, b)`. No convergence
hypothesis is needed: both sides are the same integral. -/
theorem mellinDis_rpow_mul_one_sub_rpow_eq_betaIntegral (a b : ℝ) (N : ℂ) :
    mellinDis (fun x => x ^ (a - 1) * (1 - x) ^ (b - 1)) N =
      Complex.betaIntegral (N + a - 1) b := by
  rw [mellinDis_def, Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  simp only [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le,
    Complex.ofReal_cpow (sub_nonneg.mpr hx.2.le), Complex.ofReal_sub, Complex.ofReal_one]
  rw [show N + a - 1 - 1 = (N - 1) + ((a : ℂ) - 1) by ring, Complex.cpow_add _ _ hx0]
  ring

/-- **Mellin moments of the Beta kernel.** On the half plane `1 - a < Re N`, for `0 < b`,
`∫_{(0,1]} x ^ (N - 1) x ^ (a - 1) (1 - x) ^ (b - 1) dx = Γ(N + a - 1) Γ(b) / Γ(N + a + b - 1)`. -/
theorem mellinDis_rpow_mul_one_sub_rpow {a b : ℝ} (hb : 0 < b) {N : ℂ} (hN : 0 < N.re + a - 1) :
    mellinDis (fun x => x ^ (a - 1) * (1 - x) ^ (b - 1)) N =
      Complex.Gamma (N + a - 1) * Complex.Gamma b / Complex.Gamma (N + a + b - 1) := by
  rw [mellinDis_rpow_mul_one_sub_rpow_eq_betaIntegral,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hN) (by simpa using hb),
    show N + a - 1 + b = N + a + b - 1 by ring]

/-- The transform of `(1 - x) ^ b` is Euler's beta integral `B(N, b + 1)`, at every `N`: the Beta
kernel with `a = 1`. Together with `mellinDis_rpow` for `x ^ a`, this evaluates the transform of
every finite combination of powers of `x` and of `1 - x`. -/
theorem mellinDis_one_sub_rpow (b : ℝ) (N : ℂ) :
    mellinDis (fun x => (1 - x) ^ b) N = Complex.betaIntegral N (b + 1) := by
  simpa using mellinDis_rpow_mul_one_sub_rpow_eq_betaIntegral 1 (b + 1) N

/-!
## The Beta density
-/

/-- For `0 < b`, the Mellin transform of the Beta density converges on the half plane
`1 - a < Re N`. -/
theorem mellinDisConvergent_betaPDFReal {a b : ℝ} (hb : 0 < b) {N : ℂ}
    (hN : 0 < N.re + a - 1) :
    MellinDisConvergent (ProbabilityTheory.betaPDFReal a b) N :=
  (mellinDisConvergent_congr (betaPDFReal_eqOn_Ioo a b)).mpr
    ((mellinDisConvergent_rpow_mul_one_sub_rpow_iff.mpr ⟨hN, hb⟩).const_mul _)

/-- For `Β(a, b) ≠ 0` (for instance `0 < a` and `0 < b`), the Mellin transform of the Beta density
converges exactly when `1 - a < Re N` and `0 < b`, as for the kernel. When `Β(a, b) = 0` the density
is identically zero and its transform converges everywhere, so the hypothesis cannot be dropped. -/
theorem mellinDisConvergent_betaPDFReal_iff {a b : ℝ} (hab : ProbabilityTheory.beta a b ≠ 0)
    {N : ℂ} :
    MellinDisConvergent (ProbabilityTheory.betaPDFReal a b) N ↔ 0 < N.re + a - 1 ∧ 0 < b := by
  rw [mellinDisConvergent_congr (betaPDFReal_eqOn_Ioo a b),
    mellinDisConvergent_const_mul_iff (one_div_ne_zero hab),
    mellinDisConvergent_rpow_mul_one_sub_rpow_iff]

/-- The transform of the Beta density is Euler's beta integral at `(N + a - 1, b)` divided by
`Β(a, b)`. No convergence hypothesis is needed: both sides are the same integral. -/
theorem mellinDis_betaPDFReal_eq_betaIntegral (a b : ℝ) (N : ℂ) :
    mellinDis (ProbabilityTheory.betaPDFReal a b) N =
      ((1 / ProbabilityTheory.beta a b : ℝ) : ℂ) * Complex.betaIntegral (N + a - 1) b := by
  rw [mellinDis_congr (betaPDFReal_eqOn_Ioo a b), mellinDis_const_mul,
    mellinDis_rpow_mul_one_sub_rpow_eq_betaIntegral]

/-- **Mellin moments of the Beta density.** For `0 < b`, on the half plane `1 - a < Re N`,
`∫_{(0,1]} x ^ (N - 1) x ^ (a - 1) (1 - x) ^ (b - 1) dx / Β(a, b)
  = Γ(N + a - 1) Γ(a + b) / (Γ(a) Γ(N + a + b - 1))`,
the ratio `Β(N + a - 1, b) / Β(a, b)` of Beta functions written through the Gamma function. -/
theorem mellinDis_betaPDFReal {a b : ℝ} (hb : 0 < b) {N : ℂ} (hN : 0 < N.re + a - 1) :
    mellinDis (ProbabilityTheory.betaPDFReal a b) N =
      Complex.Gamma (N + a - 1) * Complex.Gamma (a + b) /
        (Complex.Gamma a * Complex.Gamma (N + a + b - 1)) := by
  have hΓb : Complex.Gamma b ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using hb)
  rw [mellinDis_betaPDFReal_eq_betaIntegral,
    Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using hN) (by simpa using hb),
    Complex.ofReal_div, Complex.ofReal_one, ofReal_beta, show N + a - 1 + b = N + a + b - 1 by ring]
  field_simp

/-- **The Beta density is normalised**: its Mellin transform at `N = 1` is one. -/
@[simp]
theorem mellinDis_betaPDFReal_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    mellinDis (ProbabilityTheory.betaPDFReal a b) 1 = 1 := by
  have hΓa : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ha)
  have hΓab : Complex.Gamma (a + b) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simpa using add_pos ha hb)
  rw [mellinDis_betaPDFReal hb (by simpa using ha), add_sub_cancel_left,
    show (1 : ℂ) + a + b - 1 = a + b by ring, div_self (mul_ne_zero hΓa hΓab)]

end Convolution
end Factorization
end QFT
end EpsilonEridani
