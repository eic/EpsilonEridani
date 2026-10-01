/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# Plus functionals on the unit interval

For a function `K` on `[0, 1]` that may be singular at `1`, the *plus functional*
`[K]₊` is the functional on test functions

  `⟨[K]₊, φ⟩ = ∫₀¹ K z * (φ z - φ 1) dz`.

Subtracting `φ 1` is what makes the integral converge when `K` has a non-integrable
singularity at `z = 1`, such as `K z = 1 / (1 - z)`. The standard example is the plus
distribution `[1 / (1 - z)]₊`, which appears in the diagonal splitting kernels and in the
coefficient functions of perturbative QCD. The functional is defined directly on functions of
the momentum fraction rather than on Schwartz space, in which `[1 / (1 - z)]₊` is not an
object.

## Main definitions

* `EpsilonEridani.plusFunctional K φ`: the pairing `∫₀¹ K z * (φ z - φ 1) dz`.
* `EpsilonEridani.plusOneMinus φ`: the plus distribution `[1 / (1 - z)]₊` paired with `φ`.

## Main results

* `EpsilonEridani.intervalIntegrable_mul_sub`: the integral defining `⟨[K]₊, φ⟩`
  converges when `K z * (1 - z)` is integrable on `(0, 1]`, `φ` is a.e.-strongly-measurable
  there, and `φ z - φ 1 = O(1 - z)` uniformly for almost every `z ∈ (0, 1]`.
* `EpsilonEridani.plusFunctional_const`: a plus functional annihilates constants.
* `EpsilonEridani.plusFunctional_mul_right`: the multiplication identity
  `⟨[K]₊, g φ⟩ = g 1 ⟨[K]₊, φ⟩ + ∫₀¹ K z (g z - g 1) φ z dz`, which for `K z = 1 / (1 - z)`
  (`EpsilonEridani.plusOneMinus_mul`) is the distributional identity
  `g z [1 / (1 - z)]₊ = g 1 [1 / (1 - z)]₊ + (g z - g 1) / (1 - z)`.
* `EpsilonEridani.plusOneMinus_pow`: the moments of the plus distribution are harmonic numbers,
  `⟨[1 / (1 - z)]₊, z ^ n⟩ = -H_n`.

## The hypothesis on the test function

The convergence hypothesis on `K` is integrability of `K z * (1 - z)`, which covers both
`1 / (1 - z)` and the kernels `log ^ k (1 - z) / (1 - z)` of higher orders, for which
`K z * (1 - z)` is integrable but unbounded. Continuity of `φ` on `[0, 1]` alone does not
suffice for convergence even for `K z = 1 / (1 - z)`: the function `φ z = 1 / log (e / (1 - z))`,
extended by `φ 1 = 0`, is continuous on `[0, 1]`, but `(φ z - φ 1) / (1 - z)` is not integrable
near `1`. The test functions are therefore required to be a.e.-strongly-measurable and to
satisfy the one-sided Lipschitz bound `|φ z - φ 1| ≤ L * (1 - z)` almost everywhere, which
holds for every function continuous on `[0, 1]` and differentiable on `(0, 1)` with bounded
derivative, in particular for the polynomials `z ^ n` used for moments.

## References

* F. J. Yndurain, *The Theory of Quark and Gluon Interactions*, 4th ed., Springer (2006),
  ch. 4.
* G. Altarelli and G. Parisi, *Asymptotic freedom in parton language*, Nucl. Phys. B 126 (1977)
  298.
-/

public section

namespace EpsilonEridani

open MeasureTheory Set intervalIntegral
open scoped Interval

/-- The plus functional `[K]₊` attached to a function `K` which may be singular at `1`, paired
with a test function `φ`: `⟨[K]₊, φ⟩ = ∫₀¹ K z * (φ z - φ 1) dz`.

The integral converges under the hypotheses of `intervalIntegrable_mul_sub`; outside
them it takes the junk value of the Bochner integral. -/
noncomputable def plusFunctional (K φ : ℝ → ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..1, K z * (φ z - φ 1)

/-- The plus distribution `[1 / (1 - z)]₊` paired with a test function `φ`,
`∫₀¹ (φ z - φ 1) / (1 - z) dz`. -/
noncomputable def plusOneMinus (φ : ℝ → ℝ) : ℝ :=
  plusFunctional (fun z => (1 - z)⁻¹) φ

theorem plusFunctional_def (K φ : ℝ → ℝ) :
    plusFunctional K φ = ∫ z in (0 : ℝ)..1, K z * (φ z - φ 1) :=
  (rfl)

theorem plusOneMinus_def (φ : ℝ → ℝ) :
    plusOneMinus φ = plusFunctional (fun z => (1 - z)⁻¹) φ :=
  (rfl)

/-- **Convergence of the plus functional.** If `K z * (1 - z)` is integrable on `(0, 1]`,
`φ` is a.e.-strongly-measurable there, and the test function satisfies `|φ z - φ 1| ≤ L * (1 - z)`
for almost every `z` there, then the integrand `K z * (φ z - φ 1)` of `⟨[K]₊, φ⟩` is integrable
on `[0, 1]`, even though `K` itself need not be. -/
theorem intervalIntegrable_mul_sub {K φ : ℝ → ℝ} {L : ℝ}
    (hK : IntervalIntegrable (fun z => K z * (1 - z)) volume 0 1)
    (hφm : AEStronglyMeasurable φ (volume.restrict (Ioc 0 1)))
    (hφ : ∀ᵐ z ∂volume.restrict (Ioc 0 1), |φ z - φ 1| ≤ L * (1 - z)) :
    IntervalIntegrable (fun z => K z * (φ z - φ 1)) volume 0 1 := by
  have hIoc : Ι (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  -- `K` is measurable on `(0, 1]`: it agrees with `(K z * (1 - z)) * (1 - z)⁻¹` off `z = 1`.
  have hKm : AEStronglyMeasurable K (volume.restrict (Ioc 0 1)) := by
    have hinv : Measurable fun z : ℝ => (1 - z)⁻¹ := (measurable_const.sub measurable_id).inv
    refine (hK.aestronglyMeasurable.mul hinv.aestronglyMeasurable).congr ?_
    filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with z hz
    have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    simp [mul_assoc, mul_inv_cancel₀ h1z]
  refine (hK.norm.const_mul L).mono_fun' ?_ ?_
  · rw [hIoc]
    exact hKm.mul (hφm.sub aestronglyMeasurable_const)
  · rw [hIoc]
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hφ] with z hz hφz
    have h1z : 0 ≤ 1 - z := sub_nonneg.2 hz.2
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1z]
    nlinarith [mul_le_mul_of_nonneg_left hφz (abs_nonneg (K z))]

/-- The integrand of the plus distribution `[1 / (1 - z)]₊` is integrable on `[0, 1]` for every
a.e.-strongly-measurable test function with `|φ z - φ 1| ≤ L * (1 - z)` for almost every
`z ∈ (0, 1]`. -/
theorem intervalIntegrable_inv_one_sub_mul_sub {φ : ℝ → ℝ} {L : ℝ}
    (hφm : AEStronglyMeasurable φ (volume.restrict (Ioc 0 1)))
    (hφ : ∀ᵐ z ∂volume.restrict (Ioc 0 1), |φ z - φ 1| ≤ L * (1 - z)) :
    IntervalIntegrable (fun z => (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1 := by
  refine intervalIntegrable_mul_sub ?_ hφm hφ
  refine (intervalIntegrable_const (c := (1 : ℝ))).congr_ae ?_
  filter_upwards [ae_restrict_of_ae (Measure.ae_ne volume (1 : ℝ))] with z hz
  rw [inv_mul_cancel₀ (sub_ne_zero.2 (Ne.symm hz))]

/-- A plus functional annihilates constant test functions. -/
@[simp]
theorem plusFunctional_const (K : ℝ → ℝ) (c : ℝ) : plusFunctional K (fun _ => c) = 0 := by
  simp [plusFunctional]

/-- The plus distribution `[1 / (1 - z)]₊` annihilates constant test functions. -/
@[simp]
theorem plusOneMinus_const (c : ℝ) : plusOneMinus (fun _ => c) = 0 :=
  plusFunctional_const _ c

@[simp]
theorem plusFunctional_smul_left (c : ℝ) (K φ : ℝ → ℝ) :
    plusFunctional (c • K) φ = c * plusFunctional K φ := by
  simp only [plusFunctional, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact intervalIntegral.integral_const_mul c _

@[simp]
theorem plusFunctional_smul_right (K : ℝ → ℝ) (c : ℝ) (φ : ℝ → ℝ) :
    plusFunctional K (c • φ) = c * plusFunctional K φ := by
  simp only [plusFunctional, Pi.smul_apply, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  congr 1 with z
  ring

@[simp]
theorem plusOneMinus_smul (c : ℝ) (φ : ℝ → ℝ) : plusOneMinus (c • φ) = c * plusOneMinus φ :=
  plusFunctional_smul_right _ c φ

theorem plusFunctional_add_left {K K' φ : ℝ → ℝ}
    (hK : IntervalIntegrable (fun z => K z * (φ z - φ 1)) volume 0 1)
    (hK' : IntervalIntegrable (fun z => K' z * (φ z - φ 1)) volume 0 1) :
    plusFunctional (K + K') φ = plusFunctional K φ + plusFunctional K' φ := by
  simp only [plusFunctional, Pi.add_apply, add_mul]
  exact intervalIntegral.integral_add hK hK'

theorem plusFunctional_add_right {K φ ψ : ℝ → ℝ}
    (hφ : IntervalIntegrable (fun z => K z * (φ z - φ 1)) volume 0 1)
    (hψ : IntervalIntegrable (fun z => K z * (ψ z - ψ 1)) volume 0 1) :
    plusFunctional K (φ + ψ) = plusFunctional K φ + plusFunctional K ψ := by
  simp only [plusFunctional, Pi.add_apply]
  rw [← intervalIntegral.integral_add hφ hψ]
  congr 1
  ext z
  ring

theorem plusOneMinus_add {φ ψ : ℝ → ℝ}
    (hφ : IntervalIntegrable (fun z => (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1)
    (hψ : IntervalIntegrable (fun z => (1 - z)⁻¹ * (ψ z - ψ 1)) volume 0 1) :
    plusOneMinus (φ + ψ) = plusOneMinus φ + plusOneMinus ψ :=
  plusFunctional_add_right hφ hψ

/-- For a kernel `K` integrable on `[0, 1]` with `K φ` also integrable, the plus functional
splits as the ordinary pairing with `K` minus `(∫₀¹ K) δ(1 - z)`:
`⟨[K]₊, φ⟩ = ∫₀¹ K φ - φ 1 ∫₀¹ K`. -/
theorem plusFunctional_eq_integral_sub_mul_integral {K φ : ℝ → ℝ}
    (hK : IntervalIntegrable K volume 0 1)
    (hKφ : IntervalIntegrable (fun z => K z * φ z) volume 0 1) :
    plusFunctional K φ = (∫ z in (0 : ℝ)..1, K z * φ z) - φ 1 * ∫ z in (0 : ℝ)..1, K z := by
  simp only [plusFunctional, mul_sub, intervalIntegral.integral_sub hKφ (hK.mul_const _),
    intervalIntegral.integral_mul_const]
  ring

/-- **The multiplication identity.** Multiplying the test function by `g` moves the plus
prescription onto `g 1` and leaves an ordinary integral:
`⟨[K]₊, g φ⟩ = g 1 ⟨[K]₊, φ⟩ + ∫₀¹ K z (g z - g 1) φ z dz`. For `K z = 1 / (1 - z)` this is the
identity `g z [1 / (1 - z)]₊ = g 1 [1 / (1 - z)]₊ + (g z - g 1) / (1 - z)` of distributions,
whose last term is an ordinary function when `g z - g 1 = O(1 - z)`. -/
theorem plusFunctional_mul_right {K g φ : ℝ → ℝ}
    (hφ : IntervalIntegrable (fun z => K z * (φ z - φ 1)) volume 0 1)
    (hg : IntervalIntegrable (fun z => K z * (g z - g 1) * φ z) volume 0 1) :
    plusFunctional K (g * φ) =
      g 1 * plusFunctional K φ + ∫ z in (0 : ℝ)..1, K z * (g z - g 1) * φ z := by
  simp only [plusFunctional, Pi.mul_apply, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (hφ.const_mul (g 1)) hg]
  congr 1 with z
  ring

/-- The multiplication identity for the plus distribution `[1 / (1 - z)]₊`:
`g z [1 / (1 - z)]₊ = g 1 [1 / (1 - z)]₊ + (g z - g 1) / (1 - z)`, paired with `φ`. -/
theorem plusOneMinus_mul {g φ : ℝ → ℝ}
    (hφ : IntervalIntegrable (fun z => (1 - z)⁻¹ * (φ z - φ 1)) volume 0 1)
    (hg : IntervalIntegrable (fun z => (1 - z)⁻¹ * (g z - g 1) * φ z) volume 0 1) :
    plusOneMinus (g * φ) =
      g 1 * plusOneMinus φ + ∫ z in (0 : ℝ)..1, (1 - z)⁻¹ * (g z - g 1) * φ z :=
  plusFunctional_mul_right hφ hg

/-- **The moments of `[1 / (1 - z)]₊` are harmonic numbers**:
`⟨[1 / (1 - z)]₊, z ^ n⟩ = ∫₀¹ (z ^ n - 1) / (1 - z) dz = -H_n`. In the Mellin indexing
`M[f](N) = ∫₀¹ z ^ (N - 1) f z dz` this reads `M[[1 / (1 - z)]₊](N) = -S₁(N - 1)`. -/
@[simp]
theorem plusOneMinus_pow (n : ℕ) : plusOneMinus (fun z => z ^ n) = -(harmonic n : ℝ) := by
  simp only [plusOneMinus_def, plusFunctional_def]
  have hgeom : ∫ z in (0 : ℝ)..1, (1 - z)⁻¹ * (z ^ n - 1) =
      ∫ z in (0 : ℝ)..1, -∑ i ∈ Finset.range n, z ^ i := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with z hz _
    have h1z : (1 : ℝ) - z ≠ 0 := sub_ne_zero.2 (Ne.symm hz)
    rw [← geom_sum_mul]
    field_simp
    ring
  simp [hgeom, intervalIntegral.integral_finsetSum fun i _ =>
    (continuous_pow i).intervalIntegrable 0 1, integral_pow, harmonic]

end EpsilonEridani
