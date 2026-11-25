/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Convolution.Strip
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.SpecialFunctions.Beta.Basic

/-!
# The Mellin transform of the Beta kernel

The endpoint kernel `x ^ (a - 1) (1 - x) ^ (b - 1)` is the standard shape of a parton or lepton
density at the endpoints of `(0, 1]`, and powers of `1 - x` are the building blocks, next to the
powers of `x` of `mellinDis_rpow`, of the regular parts of evolution kernels. Its Mellin transform
is Euler's beta integral at `(N + a - 1, b)`, a ratio of Gamma functions.

## Main results

* `mellinDisConvergent_rpow_mul_one_sub_rpow_iff`: the transform of the kernel converges exactly
  when `1 - a < Re N` and `0 < b`, with no further hypothesis.
* `mellinDis_rpow_mul_one_sub_rpow_eq_betaIntegral`: the transform of the kernel is
  `Complex.betaIntegral (N + a - 1) b`, at every `N`;
  `mellinDis_rpow_mul_one_sub_rpow`: on the half plane of convergence it is
  `Γ(N + a - 1) Γ(b) / Γ(N + a + b - 1)`.
* `mellinDisConvergent_one_sub_rpow_iff`, `mellinDis_one_sub_rpow`: at `a = 1`, the transform of
  `(1 - x) ^ b` converges exactly when `0 < Re N` and `-1 < b`, and is `B(N, b + 1)`.

The convergence criterion reduces to TauCeti's `TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff`,
and the values are the complex-index versions of TauCeti's real Euler beta integral
`TauCeti.integral_rpow_mul_one_sub_rpow`, following the same route through Mathlib's
`Complex.betaIntegral`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Convolution

/-- The transform of the Beta kernel `x ^ (a - 1) (1 - x) ^ (b - 1)` converges exactly on the
half plane `1 - a < Re N`, and only when `0 < b`. -/
@[simp]
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

/-- The transform of `(1 - x) ^ b` converges exactly on the half plane `0 < Re N`, and only when
`-1 < b`: the Beta kernel with `a = 1`. -/
@[simp]
theorem mellinDisConvergent_one_sub_rpow_iff {b : ℝ} {N : ℂ} :
    MellinDisConvergent (fun x => (1 - x) ^ b) N ↔ 0 < N.re ∧ -1 < b := by
  simpa [neg_lt_iff_pos_add] using
    mellinDisConvergent_rpow_mul_one_sub_rpow_iff (a := 1) (b := b + 1) (N := N)

/-- The transform of `(1 - x) ^ b` is Euler's beta integral `B(N, b + 1)`, at every `N`: the Beta
kernel with `a = 1`. Together with `mellinDis_rpow` for `x ^ a`, it gives the transforms of the
two families of powers of which the regular parts of evolution kernels are finite combinations. -/
theorem mellinDis_one_sub_rpow (b : ℝ) (N : ℂ) :
    mellinDis (fun x => (1 - x) ^ b) N = Complex.betaIntegral N (b + 1) := by
  simpa using mellinDis_rpow_mul_one_sub_rpow_eq_betaIntegral 1 (b + 1) N

end Convolution
end Factorization
end QFT
end EpsilonEridani
