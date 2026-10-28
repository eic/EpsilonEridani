/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Distribution.PlusFunctional
public import EpsilonEridani.QFT.Factorization.Convolution.Mellin

/-!
# Splitting kernels in distributional normal form

A collinear splitting kernel is not a function of the momentum fraction `z`. The diagonal
kernels have a non-integrable `1 / (1 - z)` singularity, regulated by the plus prescription,
and a `δ(1 - z)` term from virtual corrections. The momentum and quark-number sum rules are
identities between functionals, so they cannot be stated for a function with "the plus
prescription understood".

This file records a kernel in the normal form

  `P = r(z) + p [1 / (1 - z)]₊ + d δ(1 - z)`,

with a regular part `r`, integrable on the unit interval against the test functions in use,
a coefficient `p` of the plus distribution `[1 / (1 - z)]₊` and a coefficient `d` of
`δ(1 - z)`. The kernel acts on a test function `φ` by

  `⟨P, φ⟩ = ∫₀¹ r z * φ z dz + p ⟨[1 / (1 - z)]₊, φ⟩ + d φ 1`.

Its Mellin moment is the pairing with `z ^ (N - 1)`, indexed so that quark number is the moment
at `N = 1` and the momentum fraction the moment at `N = 2`, as for `Convolution.mellinDis`. The
moment-space evolution of `Evolution/MomentSpace.lean` indexes by the power of `z` instead
(`momentumMomentIndex = 1`, `valenceMomentIndex = 0`), so `KernelForm.moment P (n + 1)` is its
index-`n` moment. At natural indices the moments of the plus part are harmonic numbers
(`EpsilonEridani.plusOneMinus_pow`).

The regular part is a function on `ℝ`. Only its almost-everywhere class on `(0, 1)` enters the
pairing (`KernelForm.pair_congr_ae_left`), as for the densities on which kernels act, whose
support in `[0, 1]` is likewise a hypothesis and not part of their type.

The pairing and the moments are total functions. Where the integral defining them does not
converge they take the junk value of the Bochner integral, as `EpsilonEridani.plusFunctional`
does, so a closed-form evaluation of a moment carries the hypothesis on `N` under which it
converges.

## Main definitions

* `EpsilonEridani.QFT.Factorization.Evolution.KernelForm`: a kernel in normal form.
* `KernelForm.pair P φ`: the action `⟨P, φ⟩` of the kernel on a test function.
* `KernelForm.moment P N`: the Mellin moment `⟨P, z ^ (N - 1)⟩` at a real index `N`.

## Main results

* `KernelForm.pair_pow`: the pairing with `z ^ n` is
  `∫₀¹ r z * z ^ n dz - p H_n + d`, with `H_n` the `n`-th harmonic number.
* `KernelForm.moment_natCast_add_one`: the moments at natural indices are pairings with natural
  powers.
* `KernelForm.mellinDis_regular_eq_moment`: for a kernel without plus and delta parts the moment
  is the Mellin transform `Convolution.mellinDis` of its regular part.
* `KernelForm.pair_congr_ae_left`, `KernelForm.pair_congr_ae_right`, `KernelForm.moment_congr_ae`:
  the pairing sees only the almost-everywhere class of the regular part and of the test function.
* `KernelForm.pair_smul`, `KernelForm.moment_smul`: the pairing is homogeneous in the kernel, for
  the action of `ℝ` on kernels.

## References

* G. Altarelli and G. Parisi, *Asymptotic freedom in parton language*, Nucl. Phys. B 126 (1977)
  298.
* R. K. Ellis, W. J. Stirling and B. R. Webber, *QCD and Collider Physics*, Cambridge University
  Press (1996), §4.3.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

open MeasureTheory Set

/-- A splitting kernel in the distributional normal form
`r(z) + p [1 / (1 - z)]₊ + d δ(1 - z)` on the momentum-fraction interval: a regular part `r`,
the coefficient `p` of the plus distribution `[1 / (1 - z)]₊`, and the coefficient `d` of
`δ(1 - z)`. -/
@[ext]
structure KernelForm where
  /-- The regular part, integrated against test functions over `[0, 1]`. -/
  regular : ℝ → ℝ
  /-- The coefficient of the plus distribution `[1 / (1 - z)]₊`. -/
  plusCoeff : ℝ
  /-- The coefficient of `δ(1 - z)`. -/
  deltaCoeff : ℝ

namespace KernelForm

/-- The action of a kernel in normal form on a test function `φ`:
`⟨P, φ⟩ = ∫₀¹ r z * φ z dz + p ⟨[1 / (1 - z)]₊, φ⟩ + d φ 1`.

Integrability of `r * φ` on `[0, 1]` together with the hypotheses of
`EpsilonEridani.intervalIntegrable_plusOneMinus_integrand` on `φ` is sufficient for both integrals
to converge. Where an integral does not converge, its term takes the junk value of the Bochner
integral. -/
noncomputable def pair (P : KernelForm) (φ : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..1, P.regular z * φ z) + P.plusCoeff * plusOneMinus φ + P.deltaCoeff * φ 1

/-- Unfolding lemma for `KernelForm.pair`, whose body is not exposed. -/
theorem pair_def (P : KernelForm) (φ : ℝ → ℝ) :
    P.pair φ =
      (∫ z in (0 : ℝ)..1, P.regular z * φ z) + P.plusCoeff * plusOneMinus φ +
        P.deltaCoeff * φ 1 :=
  (rfl)

/-- The Mellin moment `M[P](N) = ⟨P, z ^ (N - 1)⟩` of a kernel, at a real index `N`. Quark
number is the moment at `N = 1` and the momentum fraction the moment at `N = 2`: this is the
literature's index convention, that of `Convolution.mellinDis`, the transform of functions it
extends (`mellinDis_regular_eq_moment`). It is shifted by one from the convention of
`EpsilonEridani.Particles.Parton.PDF.mellinMoment` (`∫ x ^ n * f`) used by the moment-space
evolution of `Evolution/MomentSpace.lean`: `P.moment (n + 1)` is the index-`n` moment there, so
the momentum moment `P.moment 2` sits at `momentumMomentIndex = 1` and the quark-number moment
`P.moment 1` at `valenceMomentIndex = 0`.

The regular part contributes `∫₀¹ z ^ (N - 1) r z dz`, whose convergence depends on `r`; every
statement that evaluates the moment in closed form carries the hypothesis on `N` under which it
converges. For a regular part integrable away from `z = 0`, as those of the leading-order kernels
are, it converges for `N` in a half-line determined by the singularity of `r` at `z = 0`. Where it
does not converge the moment takes the junk value of the Bochner integral, not a value of the
analytic continuation of the moment in `N`. -/
noncomputable def moment (P : KernelForm) (N : ℝ) : ℝ :=
  P.pair fun z => z ^ (N - 1)

/-- Unfolding lemma for `KernelForm.moment`, whose body is not exposed. -/
theorem moment_def (P : KernelForm) (N : ℝ) : P.moment N = P.pair fun z => z ^ (N - 1) :=
  (rfl)

/-- At the natural index `n + 1` the Mellin moment is the pairing with the monomial `z ^ n`. -/
theorem moment_natCast_add_one (P : KernelForm) (n : ℕ) :
    P.moment (n + 1) = P.pair fun z => z ^ n := by
  simp only [moment_def, add_sub_cancel_right, Real.rpow_natCast]

/-- **The pairing sees only the almost-everywhere class of the regular part.** Two kernels with
the same coefficients whose regular parts agree almost everywhere on `(0, 1]` pair equally with
every test function. -/
theorem pair_congr_ae_left {P Q : KernelForm}
    (hr : P.regular =ᵐ[volume.restrict (Ioc 0 1)] Q.regular) (hp : P.plusCoeff = Q.plusCoeff)
    (hd : P.deltaCoeff = Q.deltaCoeff) (φ : ℝ → ℝ) : P.pair φ = Q.pair φ := by
  have hint : (∫ z in (0 : ℝ)..1, P.regular z * φ z) = ∫ z in (0 : ℝ)..1, Q.regular z * φ z := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    rw [uIoc_of_le zero_le_one]
    exact hr.mono fun z hz => by simp [hz]
  rw [pair_def, pair_def, hint, hp, hd]

/-- **The pairing sees only the almost-everywhere class of the test function** on `(0, 1]`,
together with its value `φ 1`, which the delta part evaluates and the plus part subtracts. -/
theorem pair_congr_ae_right (P : KernelForm) {φ ψ : ℝ → ℝ}
    (h : φ =ᵐ[volume.restrict (Ioc 0 1)] ψ) (h1 : φ 1 = ψ 1) : P.pair φ = P.pair ψ := by
  have hint : (∫ z in (0 : ℝ)..1, P.regular z * φ z) = ∫ z in (0 : ℝ)..1, P.regular z * ψ z := by
    refine intervalIntegral.integral_congr_ae_restrict ?_
    rw [uIoc_of_le zero_le_one]
    exact h.mono fun z hz => by simp [hz]
  rw [pair_def, pair_def, hint, plusOneMinus_congr_ae h h1, h1]

/-- The Mellin moments see only the almost-everywhere class of the regular part on `(0, 1]`. -/
theorem moment_congr_ae {P Q : KernelForm}
    (hr : P.regular =ᵐ[volume.restrict (Ioc 0 1)] Q.regular) (hp : P.plusCoeff = Q.plusCoeff)
    (hd : P.deltaCoeff = Q.deltaCoeff) (N : ℝ) : P.moment N = Q.moment N :=
  pair_congr_ae_left hr hp hd _

/-- For a kernel without plus and delta parts the Mellin moment is the Mellin transform
`Convolution.mellinDis` of its regular part, in the same index convention: both are
`∫₀¹ z ^ (N - 1) r z dz`. -/
theorem mellinDis_regular_eq_moment {P : KernelForm} (hp : P.plusCoeff = 0)
    (hd : P.deltaCoeff = 0) (N : ℝ) :
    Convolution.mellinDis P.regular N = P.moment N := by
  simp only [moment_def, pair_def, hp, hd, zero_mul, add_zero]
  rw [Convolution.mellinDis, intervalIntegral.integral_of_le zero_le_one,
    ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  simp only [Complex.ofReal_mul, Complex.ofReal_cpow hx.1.le, Complex.ofReal_sub,
    Complex.ofReal_one]
  exact mul_comm _ _

/-- **Natural moments of a kernel.** The pairing with `z ^ n` is
`∫₀¹ r z * z ^ n dz - p H_n + d`: the plus part contributes the harmonic number `H_n` and the
delta part its coefficient. -/
theorem pair_pow (P : KernelForm) (n : ℕ) :
    (P.pair fun z => z ^ n) =
      (∫ z in (0 : ℝ)..1, P.regular z * z ^ n) - P.plusCoeff * harmonic n + P.deltaCoeff := by
  simp only [pair_def, plusOneMinus_pow, one_pow, mul_one]
  ring

/-- Scaling a kernel scales its regular part and both coefficients. -/
instance : SMul ℝ KernelForm where
  smul c P := ⟨fun z => c * P.regular z, c * P.plusCoeff, c * P.deltaCoeff⟩

@[simp]
theorem smul_regular (c : ℝ) (P : KernelForm) : (c • P).regular = fun z => c * P.regular z :=
  (rfl)

@[simp]
theorem smul_plusCoeff (c : ℝ) (P : KernelForm) : (c • P).plusCoeff = c * P.plusCoeff :=
  (rfl)

@[simp]
theorem smul_deltaCoeff (c : ℝ) (P : KernelForm) : (c • P).deltaCoeff = c * P.deltaCoeff :=
  (rfl)

/-- Scaling kernels is an action of the multiplicative monoid `ℝ`. -/
instance : MulAction ℝ KernelForm where
  one_smul P := by ext <;> simp
  mul_smul a b P := by ext <;> simp [mul_assoc]

/-- The pairing is homogeneous in the kernel. No integrability hypothesis is needed, since the
interval integral commutes with scalar multiplication unconditionally. -/
@[simp]
theorem pair_smul (c : ℝ) (P : KernelForm) (φ : ℝ → ℝ) : (c • P).pair φ = c * P.pair φ := by
  simp only [pair_def, smul_regular, smul_plusCoeff, smul_deltaCoeff, mul_assoc,
    intervalIntegral.integral_const_mul]
  ring

/-- The Mellin moments are homogeneous in the kernel. -/
@[simp]
theorem moment_smul (c : ℝ) (P : KernelForm) (N : ℝ) : (c • P).moment N = c * P.moment N :=
  pair_smul c P _

end KernelForm

end Evolution
end Factorization
end QFT
end EpsilonEridani
