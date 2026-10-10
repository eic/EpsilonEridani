/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Distribution.PlusFunctional

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
at `N = 1` and the momentum fraction the moment at `N = 2`. At natural indices the moments of the
plus part are harmonic numbers (`EpsilonEridani.plusOneMinus_pow`).

The regular part is a function on `ℝ`. Only its almost-everywhere class on `(0, 1)` enters the
pairing, as for the densities on which kernels act, whose support in `[0, 1]` is likewise a
hypothesis and not part of their type.

## Main definitions

* `EpsilonEridani.QFT.Factorization.Evolution.KernelForm`: a kernel in normal form.
* `KernelForm.pair P φ`: the action `⟨P, φ⟩` of the kernel on a test function.
* `KernelForm.moment P N`: the Mellin moment `⟨P, z ^ (N - 1)⟩` at a real index `N`.

## Main results

* `KernelForm.pair_pow`: the pairing with `z ^ n` is
  `∫₀¹ r z * z ^ n dz - p H_n + d`, with `H_n` the `n`-th harmonic number.
* `KernelForm.moment_natCast_add_one`, `KernelForm.moment_one`, `KernelForm.moment_two`: the
  moments at natural indices are pairings with natural powers.
* `KernelForm.pair_smul`, `KernelForm.moment_smul`: the pairing is homogeneous in the kernel.

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

open MeasureTheory

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
`⟨P, φ⟩ = ∫₀¹ r z * φ z dz + p ⟨[1 / (1 - z)]₊, φ⟩ + d φ 1`. -/
noncomputable def pair (P : KernelForm) (φ : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..1, P.regular z * φ z) + P.plusCoeff * plusOneMinus φ + P.deltaCoeff * φ 1

/-- Unfolding lemma for `KernelForm.pair`, whose body is not exposed. -/
theorem pair_def (P : KernelForm) (φ : ℝ → ℝ) :
    P.pair φ =
      (∫ z in (0 : ℝ)..1, P.regular z * φ z) + P.plusCoeff * plusOneMinus φ +
        P.deltaCoeff * φ 1 :=
  (rfl)

/-- The Mellin moment `M[P](N) = ⟨P, z ^ (N - 1)⟩` of a kernel, at a real index `N`. Quark
number is the moment at `N = 1` and the momentum fraction the moment at `N = 2`. The regular
part contributes `∫₀¹ z ^ (N - 1) r z dz`, which converges only for `N` in a half-line
determined by the behaviour of `r` at `z = 0`. -/
noncomputable def moment (P : KernelForm) (N : ℝ) : ℝ :=
  P.pair fun z => z ^ (N - 1)

/-- Unfolding lemma for `KernelForm.moment`, whose body is not exposed. -/
theorem moment_def (P : KernelForm) (N : ℝ) : P.moment N = P.pair fun z => z ^ (N - 1) :=
  (rfl)

/-- At the natural index `n + 1` the Mellin moment is the pairing with the monomial `z ^ n`. -/
theorem moment_natCast_add_one (P : KernelForm) (n : ℕ) :
    P.moment (n + 1) = P.pair fun z => z ^ n := by
  simp only [moment_def, add_sub_cancel_right, Real.rpow_natCast]

/-- The quark-number moment `M[P](1)` is the pairing with the constant function `1`. -/
theorem moment_one (P : KernelForm) : P.moment 1 = P.pair fun _ => 1 := by
  simp only [moment_def, sub_self, Real.rpow_zero]

/-- The momentum moment `M[P](2)` is the pairing with the identity. -/
theorem moment_two (P : KernelForm) : P.moment 2 = P.pair fun z => z := by
  norm_num [moment_def]

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
