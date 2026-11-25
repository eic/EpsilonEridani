/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient

/-!
# Simple poles from a Laurent presentation

A function `f` with a presentation `f(w) = (w - z)⁻¹ • g(w)` on a punctured neighbourhood of `z`
has, when `g` is analytic at `z` with `g(z) ≠ 0`, a simple pole at `z` whose residue is `g(z)`.
Mathlib characterises the order and the trailing coefficient through presentations
`(w - z) ^ n • g(w)` with an integer exponent (`meromorphicOrderAt_eq_int_iff`,
`AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE`). This file specialises them to
the inverse form in which simple poles are usually written, over any nontrivially normed field
and with values in any normed space, and adds the residue as a limit. For `ℂ`-valued functions on
`ℂ`, the quotient form `g / h` at a simple zero of `h` and its residue `TauCeti.Contour.residue`
are developed in TauCeti (`TauCeti.Contour.meromorphicOrderAt_div_eq_neg_one`,
`TauCeti.Contour.residue_div_of_zero_deriv_ne_zero`).

## Main statements

* `ContinuousAt.tendsto_sub_smul_of_eventually_eq_inv_smul`: `(w - z) • f(w) → g(z)` as `w → z`,
  for `g` merely continuous at `z`.
* `eventuallyEq_zpow_neg_one_smul_of_eventually_eq_inv_smul`: the inverse presentation as the
  integer-exponent presentation `f(w) = (w - z) ^ (-1) • g(w)`.
* `MeromorphicAt.meromorphicAt_of_eventually_eq_inv_smul`: `f` is meromorphic at `z` when `g` is.
* `AnalyticAt.meromorphicOrderAt_eq_neg_one_of_ne_zero_of_eventually_eq_inv_smul`: `f` has order
  `-1` at `z` when `g` is analytic at `z` with `g(z) ≠ 0`.
* `AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eventually_eq_inv_smul`: the trailing
  coefficient of `f` at `z` is `g(z)` when `g` is analytic at `z` with `g(z) ≠ 0`.
-/

@[expose] public section

open Filter Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {f g : 𝕜 → E} {z : 𝕜}

/-- **The residue at a simple pole as a limit.** If `f(w) = (w - z)⁻¹ • g(w)` near `z` with `g`
continuous at `z`, then `(w - z) • f(w) → g(z)` as `w → z`. -/
theorem ContinuousAt.tendsto_sub_smul_of_eventually_eq_inv_smul (hg : ContinuousAt g z)
    (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ • g w) :
    Tendsto (fun w => (w - z) • f w) (𝓝[≠] z) (𝓝 (g z)) := by
  refine hg.continuousWithinAt.tendsto.congr' ?_
  filter_upwards [h, self_mem_nhdsWithin] with w hw hne
  rw [hw, smul_inv_smul₀ (sub_ne_zero.2 hne)]

/-- The inverse presentation `f(w) = (w - z)⁻¹ • g(w)` is the integer-exponent presentation
`f(w) = (w - z) ^ (-1) • g(w)` that Mathlib's order and trailing-coefficient API consumes. -/
theorem eventuallyEq_zpow_neg_one_smul_of_eventually_eq_inv_smul
    (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ • g w) :
    f =ᶠ[𝓝[≠] z] fun w => (w - z) ^ (-1 : ℤ) • g w :=
  h.mono fun w hw => by simp only [hw, zpow_neg_one]

/-- If `f(w) = (w - z)⁻¹ • g(w)` near `z` with `g` meromorphic at `z`, then `f` is meromorphic
at `z`. -/
theorem MeromorphicAt.meromorphicAt_of_eventually_eq_inv_smul (hg : MeromorphicAt g z)
    (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ • g w) : MeromorphicAt f z := by
  rw [MeromorphicAt.meromorphicAt_congr
    (eventuallyEq_zpow_neg_one_smul_of_eventually_eq_inv_smul h)]
  fun_prop

/-- **A simple pole.** If `f(w) = (w - z)⁻¹ • g(w)` near `z` with `g` analytic at `z` and
`g(z) ≠ 0`, then `f` has order `-1` at `z`. -/
theorem AnalyticAt.meromorphicOrderAt_eq_neg_one_of_ne_zero_of_eventually_eq_inv_smul
    (hg : AnalyticAt 𝕜 g z) (hgz : g z ≠ 0) (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ • g w) :
    meromorphicOrderAt f z = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast,
    meromorphicOrderAt_eq_int_iff (hg.meromorphicAt.meromorphicAt_of_eventually_eq_inv_smul h)]
  exact ⟨g, hg, hgz, eventuallyEq_zpow_neg_one_smul_of_eventually_eq_inv_smul h⟩

/-- **The residue at a simple pole as a trailing coefficient.** If `f(w) = (w - z)⁻¹ • g(w)` near
`z` with `g` analytic at `z` and `g(z) ≠ 0`, then the trailing coefficient of `f` at `z` is
`g(z)`. -/
theorem AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eventually_eq_inv_smul
    (hg : AnalyticAt 𝕜 g z) (hgz : g z ≠ 0) (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ • g w) :
    meromorphicTrailingCoeffAt f z = g z :=
  hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hgz
    (eventuallyEq_zpow_neg_one_smul_of_eventually_eq_inv_smul h)
