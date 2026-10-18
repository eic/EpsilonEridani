/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Modified Bessel functions of the second kind

The modified Bessel function of the second kind of real order `ν` is, for `x > 0`,

  `K_ν(x) = ∫₀^∞ exp (-x cosh t) cosh (ν t) dt`

(DLMF 10.32.9). This file defines the family `besselK ν x` by this integral representation and
proves the properties of `K₀` and `K₁` that the equivalent-photon spectrum of a fast charge and the
light-cone wave functions of a virtual photon are built from: positivity, strict decrease, the
recurrence in the order and the derivative relations `K₀' = -K₁` and `K₁' = -K₀ - K₁/x`, the
exponential decay at large argument, the simple pole of `K₁` and the logarithmic behaviour
`K₀(x) ~ -log x` at the origin.

For `x ≤ 0` the integrand is bounded below by `1`, so the integral is not convergent and the
Bochner integral returns `0`; `besselK_of_nonpos` records this value, so that statements on the
whole real line need no domain hypothesis where `0` is harmless.

## Main definitions

* `EpsilonEridani.besselK ν x`: the modified Bessel function `K_ν(x)`.

## Main statements

* `EpsilonEridani.integrableOn_besselK_integrand`: the integral converges for `x > 0`.
* `EpsilonEridani.besselK_pos`: `K_ν(x) > 0` for `x > 0`.
* `EpsilonEridani.besselK_le_besselK`: `K_ν ≤ K_μ` when `|ν| ≤ |μ|`.
* `EpsilonEridani.besselK_add_one_sub_besselK_sub_one`: `K_{ν+1} - K_{ν-1} = (2ν/x) K_ν`.
* `EpsilonEridani.hasDerivAt_besselK`: `K_ν' = -(K_{ν-1} + K_{ν+1}) / 2`, and its special
  cases `EpsilonEridani.hasDerivAt_besselK_zero`: `K₀' = -K₁` and
  `EpsilonEridani.hasDerivAt_besselK_one`: `K₁' = -K₀ - K₁/x`.
* `EpsilonEridani.strictAntiOn_besselK`: `K_ν` is strictly decreasing on `(0, ∞)`.
* `EpsilonEridani.besselK_le_exp_mul_besselK`: `K_ν(x) ≤ exp (-(x - x₀)) K_ν(x₀)` for
  `0 < x₀ ≤ x`.
* `EpsilonEridani.exp_neg_div_lt_besselK_one`,
  `EpsilonEridani.besselK_one_le_exp_neg_mul`: `exp (-x) / x < K₁(x) ≤ exp (-x) (1 + 1 / x)`,
  and hence `EpsilonEridani.tendsto_mul_besselK_one_nhdsGT_zero`: `x K₁(x) → 1` as `x → 0⁺`.
* `EpsilonEridani.neg_log_sub_one_le_besselK`,
  `EpsilonEridani.besselK_zero_le_log_two_div_add_exp_neg_one`:
  `-log x - 1 ≤ K_ν(x)` and `K₀(x) ≤ log (2/x) + e⁻¹` near the origin, whence
  `EpsilonEridani.tendsto_besselK_nhdsGT_zero`: `K_ν(x) → ∞` as `x → 0⁺`, and
  `EpsilonEridani.isEquivalent_besselK_zero_neg_log`: `K₀(x) ~ -log x` as `x → 0⁺`.

## References

* NIST Digital Library of Mathematical Functions, §10.25, §10.29 and §10.32.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd edition, Cambridge University
  Press (1944), §6.22.
-/

public section

noncomputable section

open Asymptotics Real MeasureTheory Set Filter Topology

namespace EpsilonEridani

/-- The modified Bessel function of the second kind `K_ν(x)` of real order `ν`, by its integral
representation `∫₀^∞ exp (-x cosh t) cosh (ν t) dt`. The integral converges exactly for `x > 0`;
for `x ≤ 0` its value is `0` (`besselK_of_nonpos`). -/
def besselK (ν x : ℝ) : ℝ :=
  ∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)) * cosh (ν * t)

/-- The defining integral representation of `K_ν(x)`. -/
theorem besselK_def (ν x : ℝ) :
    besselK ν x = ∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)) * cosh (ν * t) := (rfl)

/-- `K_ν` is even in the order. -/
@[simp]
theorem besselK_neg (ν x : ℝ) : besselK (-ν) x = besselK ν x := by
  simp only [besselK_def, neg_mul, cosh_neg]

/-! ### Convergence of the integral -/

/-- The integrand of `K_ν(x)` is dominated on `[0, ∞)` by a multiple of `exp (-t)`. -/
private theorem integrand_le {x : ℝ} (hx : 0 < x) (ν : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    exp (-(x * cosh t)) * cosh (ν * t) ≤ exp ((|ν| + 1) ^ 2 / x) * exp (-t) := by
  set a := |ν| + 1
  have hcosh : x * (t ^ 2 / 4) ≤ x * cosh t := by
    refine mul_le_mul_of_nonneg_left ?_ hx.le
    rw [cosh_eq]
    linarith [quadratic_le_exp_of_nonneg ht, exp_pos (-t)]
  have hsq : a * t ≤ x * (t ^ 2 / 4) + a ^ 2 / x := by
    have key : x * (a * t) ≤ x * (x * (t ^ 2 / 4) + a ^ 2 / x) := by
      rw [mul_add, mul_div_cancel₀ _ hx.ne']
      nlinarith [sq_nonneg (x * t / 2 - a)]
    exact le_of_mul_le_mul_left key hx
  calc exp (-(x * cosh t)) * cosh (ν * t)
      ≤ exp (-(x * cosh t)) * exp (|ν| * t) := by
        gcongr
        have h₁ : exp (ν * t) ≤ exp (|ν| * t) :=
          exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self ν) ht)
        have h₂ : exp (-(ν * t)) ≤ exp (|ν| * t) :=
          exp_le_exp.2 (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs ν) ht)
        rw [cosh_eq]
        linarith
    _ = exp (-(x * cosh t) + |ν| * t) := (exp_add _ _).symm
    _ ≤ exp (a ^ 2 / x + -t) := by
        refine exp_le_exp.2 ?_
        have : |ν| * t + t = a * t := by ring
        linarith
    _ = exp (a ^ 2 / x) * exp (-t) := exp_add _ _

private theorem continuous_integrand (x ν : ℝ) :
    Continuous fun t ↦ exp (-(x * cosh t)) * cosh (ν * t) := by
  fun_prop

/-- The integral defining `K_ν(x)` converges for `x > 0`. -/
theorem integrableOn_besselK_integrand (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t ↦ exp (-(x * cosh t)) * cosh (ν * t)) (Ioi 0) := by
  refine ((integrableOn_exp_neg_Ioi 0).const_mul (exp ((|ν| + 1) ^ 2 / x))).mono'
    (continuous_integrand x ν).aestronglyMeasurable ?_
  refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht ↦ ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact integrand_le hx ν (le_of_lt ht)

/-- For `x ≤ 0` the integral defining `K_ν(x)` diverges, and `besselK ν x` is `0`. -/
theorem besselK_of_nonpos (ν : ℝ) {x : ℝ} (hx : x ≤ 0) : besselK ν x = 0 := by
  refine integral_undef fun hint ↦ ?_
  have hone : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) (Ioi 0) := by
    refine hint.mono' aestronglyMeasurable_const (ae_of_all _ fun t ↦ ?_)
    rw [norm_one]
    have h₁ : 1 ≤ exp (-(x * cosh t)) :=
      one_le_exp (neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg hx (cosh_pos t).le))
    nlinarith [one_le_cosh (ν * t)]
  rw [integrableOn_const_iff] at hone
  simp [Real.volume_Ioi] at hone

/-! ### Positivity and comparison -/

/-- `K_ν(x)` is positive for `x > 0`. -/
theorem besselK_pos (ν : ℝ) {x : ℝ} (hx : 0 < x) : 0 < besselK ν x := by
  rw [besselK_def, setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun t ↦ by positivity) (integrableOn_besselK_integrand ν hx),
    Function.support_eq_univ fun t ↦ by positivity, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- `K_ν(x)` is nonnegative, including at the junk values `x ≤ 0`. -/
theorem besselK_nonneg (ν x : ℝ) : 0 ≤ besselK ν x := by
  rcases le_or_gt x 0 with hx | hx
  · exact (besselK_of_nonpos ν hx).ge
  · exact (besselK_pos ν hx).le

/-- `K_ν(x)` increases with the absolute value of the order. -/
theorem besselK_le_besselK {ν μ : ℝ} (h : |ν| ≤ |μ|) (x : ℝ) : besselK ν x ≤ besselK μ x := by
  rcases le_or_gt x 0 with hx | hx
  · rw [besselK_of_nonpos ν hx, besselK_of_nonpos μ hx]
  refine setIntegral_mono_on (integrableOn_besselK_integrand ν hx)
    (integrableOn_besselK_integrand μ hx) measurableSet_Ioi fun t ht ↦ ?_
  gcongr
  rw [cosh_le_cosh, abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg t)

/-! ### The recurrence in the order -/

/-- The recurrence in the order, `K_{ν+1}(x) - K_{ν-1}(x) = (2ν/x) K_ν(x)` (DLMF 10.29.1). -/
theorem besselK_add_one_sub_besselK_sub_one (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    besselK (ν + 1) x - besselK (ν - 1) x = 2 * ν / x * besselK ν x := by
  -- Integrate `sinh (ν t) exp (-x cosh t)` over `(0, ∞)`: it vanishes at both ends, so its
  -- derivative integrates to zero, and the two halves of that derivative are the two sides.
  have hintν := integrableOn_besselK_integrand ν hx
  have hintAdd := integrableOn_besselK_integrand (ν + 1) hx
  have hintSub := integrableOn_besselK_integrand (ν - 1) hx
  -- `2 sinh (ν t) sinh t` is the difference of the integrands of orders `ν + 1` and `ν - 1`.
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun s ↦ sinh (ν * s) * exp (-(x * cosh s)))
        (ν * (exp (-(x * cosh t)) * cosh (ν * t)) -
          x / 2 * (exp (-(x * cosh t)) * cosh ((ν + 1) * t) -
            exp (-(x * cosh t)) * cosh ((ν - 1) * t))) t := by
    intro t _
    have h₁ : HasDerivAt (fun s : ℝ ↦ sinh (ν * s)) (cosh (ν * t) * ν) t := by
      simpa using ((hasDerivAt_id t).const_mul ν).sinh
    have h₂ : HasDerivAt (fun s : ℝ ↦ exp (-(x * cosh s)))
        (exp (-(x * cosh t)) * -(x * sinh t)) t :=
      ((hasDerivAt_cosh t).const_mul x).fun_neg.exp
    refine (h₁.mul h₂).congr_deriv ?_
    rw [add_mul, sub_mul, one_mul, cosh_add, cosh_sub]
    ring
  have hintScaled : IntegrableOn (fun t ↦ ν * (exp (-(x * cosh t)) * cosh (ν * t))) (Ioi 0) :=
    hintν.const_mul ν
  have hintDiff : IntegrableOn (fun t ↦ exp (-(x * cosh t)) * cosh ((ν + 1) * t) -
      exp (-(x * cosh t)) * cosh ((ν - 1) * t)) (Ioi 0) := hintAdd.sub hintSub
  have hintTail : IntegrableOn (fun t ↦ x / 2 * (exp (-(x * cosh t)) * cosh ((ν + 1) * t) -
      exp (-(x * cosh t)) * cosh ((ν - 1) * t))) (Ioi 0) := hintDiff.const_mul (x / 2)
  have hF'int : IntegrableOn (fun t ↦ ν * (exp (-(x * cosh t)) * cosh (ν * t)) -
      x / 2 * (exp (-(x * cosh t)) * cosh ((ν + 1) * t) -
        exp (-(x * cosh t)) * cosh ((ν - 1) * t))) (Ioi 0) := hintScaled.sub hintTail
  -- The primitive decays super-exponentially, since `cosh t` grows faster than `|sinh (ν t)|`.
  have hlim : Tendsto (fun t : ℝ ↦ sinh (ν * t) * exp (-(x * cosh t))) atTop (𝓝 0) := by
    have hbot : Tendsto (fun t : ℝ ↦ |ν| * t - x * t ^ 2 / 4) atTop atBot := by
      refine tendsto_atBot_mono' _ ?_ tendsto_neg_atTop_atBot
      filter_upwards [eventually_ge_atTop (4 * (|ν| + 1) / x), eventually_ge_atTop (0 : ℝ)]
        with t ht ht0
      rw [div_le_iff₀ hx] at ht
      nlinarith
    refine squeeze_zero_norm' ?_ (tendsto_exp_atBot.comp hbot)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h₁ : exp (ν * t) ≤ exp (|ν| * t) :=
      exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_abs_self ν) ht)
    have h₂ : exp (-(ν * t)) ≤ exp (|ν| * t) :=
      exp_le_exp.2 (by rw [← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_le_abs ν) ht)
    have habs : |sinh (ν * t)| ≤ exp (|ν| * t) := by
      rw [abs_le, sinh_eq]
      exact ⟨by linarith [exp_pos (ν * t)], by linarith [exp_pos (-(ν * t))]⟩
    have hcosh : x * (t ^ 2 / 4) ≤ x * cosh t := by
      refine mul_le_mul_of_nonneg_left ?_ hx.le
      rw [cosh_eq]
      linarith [quadratic_le_exp_of_nonneg ht, exp_pos (-t)]
    calc ‖sinh (ν * t) * exp (-(x * cosh t))‖
        = |sinh (ν * t)| * exp (-(x * cosh t)) := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (exp_pos _)]
      _ ≤ exp (|ν| * t) * exp (-(x * (t ^ 2 / 4))) := by gcongr
      _ = exp (|ν| * t - x * t ^ 2 / 4) := by rw [← exp_add]; ring_nf
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hF'int hlim
  simp only [mul_zero, sinh_zero, zero_mul, sub_zero] at hFTC
  rw [integral_sub hintScaled hintTail, integral_const_mul, integral_const_mul,
    integral_sub hintAdd hintSub] at hFTC
  have key : x * (besselK (ν + 1) x - besselK (ν - 1) x) = 2 * ν * besselK ν x := by
    rw [besselK_def ν, besselK_def (ν + 1), besselK_def (ν - 1)]
    linear_combination (-2 : ℝ) * hFTC
  rw [div_mul_eq_mul_div, eq_div_iff hx.ne']
  linarith [key]

/-! ### The derivative -/

/-- The derivative recurrence `K_ν'(x) = -(K_{ν-1}(x) + K_{ν+1}(x)) / 2` (DLMF 10.29.1). -/
theorem hasDerivAt_besselK (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselK ν) (-(besselK (ν - 1) x + besselK (ν + 1) x) / 2) x := by
  -- `cosh t cosh (ν t)` is the half-sum of the integrands of orders `ν - 1` and `ν + 1`.
  have hprod (y t : ℝ) : cosh t * (exp (-(y * cosh t)) * cosh (ν * t)) =
      (exp (-(y * cosh t)) * cosh ((ν - 1) * t) + exp (-(y * cosh t)) * cosh ((ν + 1) * t)) /
        2 := by
    rw [sub_mul, add_mul, one_mul, cosh_sub, cosh_add]
    ring
  have hint (y : ℝ) (hy : 0 < y) : IntegrableOn (fun t ↦ cosh t *
      (exp (-(y * cosh t)) * cosh (ν * t))) (Ioi 0) := by
    simp_rw [hprod]
    exact ((integrableOn_besselK_integrand (ν - 1) hy).add
      (integrableOn_besselK_integrand (ν + 1) hy)).div_const 2
  -- Differentiate under the integral sign on `(x / 2, ∞)`, dominated by the integrand at `x / 2`.
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := fun y t ↦ exp (-(y * cosh t)) * cosh (ν * t))
    (F' := fun y t ↦ -(cosh t * (exp (-(y * cosh t)) * cosh (ν * t))))
    (bound := fun t ↦ cosh t * (exp (-(x / 2 * cosh t)) * cosh (ν * t)))
    (Ioi_mem_nhds (half_lt_self hx))
    (Eventually.of_forall fun y ↦ (continuous_integrand y ν).aestronglyMeasurable)
    (integrableOn_besselK_integrand ν hx) (hint x hx).neg.aestronglyMeasurable
    (ae_of_all _ fun t y hy ↦ ?_) (hint (x / 2) (half_pos hx))
    (ae_of_all _ fun t y _ ↦ ?_)
  · have hK : besselK ν = fun y ↦ ∫ t in Ioi (0 : ℝ), exp (-(y * cosh t)) * cosh (ν * t) :=
      funext (besselK_def ν)
    rw [hK, besselK_def, besselK_def]
    convert key.2 using 1
    rw [integral_neg, ← integral_add (integrableOn_besselK_integrand (ν - 1) hx)
      (integrableOn_besselK_integrand (ν + 1) hx), neg_div, ← integral_div]
    simp_rw [hprod]
  · rw [norm_neg, Real.norm_of_nonneg (by positivity)]
    gcongr
    exact le_of_lt hy
  · exact (((hasDerivAt_id y).mul_const (cosh t)).fun_neg.exp.mul_const
      (cosh (ν * t))).congr_deriv (by simp only [id, one_mul]; ring)

/-- The derivative relation `K₀' = -K₁`. -/
theorem hasDerivAt_besselK_zero {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselK 0) (-besselK 1 x) x := by
  convert hasDerivAt_besselK 0 hx using 1
  rw [zero_sub, zero_add, besselK_neg]
  ring

/-- The derivative relation `K₁'(x) = -K₀(x) - K₁(x)/x`, the case `ν = 1` of DLMF 10.29.2. -/
theorem hasDerivAt_besselK_one {x : ℝ} (hx : 0 < x) :
    HasDerivAt (besselK 1) (-besselK 0 x - besselK 1 x / x) x := by
  have h := besselK_add_one_sub_besselK_sub_one 1 hx
  rw [show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num] at h
  refine (hasDerivAt_besselK 1 hx).congr_deriv ?_
  rw [show (1 : ℝ) + 1 = 2 by norm_num, show (1 : ℝ) - 1 = 0 by norm_num]
  field_simp at h ⊢
  linarith

/-- `K_ν` is continuous on `(0, ∞)`. -/
theorem continuousOn_besselK (ν : ℝ) : ContinuousOn (besselK ν) (Ioi 0) :=
  fun _ hx ↦ (hasDerivAt_besselK ν hx).continuousAt.continuousWithinAt

/-- `K_ν` is strictly decreasing on `(0, ∞)`. -/
theorem strictAntiOn_besselK (ν : ℝ) : StrictAntiOn (besselK ν) (Ioi 0) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioi 0) (continuousOn_besselK ν) fun x hx ↦ ?_
  rw [interior_Ioi] at hx
  rw [(hasDerivAt_besselK ν hx).deriv]
  have := besselK_pos (ν - 1) hx
  have := besselK_pos (ν + 1) hx
  linarith

/-! ### Behaviour at infinity -/

/-- Exponential decay of `K_ν`: beyond any `x₀ > 0`, `K_ν(x)` falls at least as fast as
`exp (-x)`. -/
theorem besselK_le_exp_mul_besselK (ν : ℝ) {x₀ x : ℝ} (hx₀ : 0 < x₀) (h : x₀ ≤ x) :
    besselK ν x ≤ exp (-(x - x₀)) * besselK ν x₀ := by
  rw [besselK_def, besselK_def, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_besselK_integrand ν (hx₀.trans_le h))
    ((integrableOn_besselK_integrand ν hx₀).const_mul _) measurableSet_Ioi fun t _ ↦ ?_
  rw [← mul_assoc, ← exp_add]
  gcongr
  nlinarith [one_le_cosh t]

/-! ### Behaviour at the origin -/

/-- The remainder `∫₀^∞ exp (-x cosh t) exp (-t) dt` of `K₁(x)` beyond `exp (-x) / x` converges
for `x ≥ 0`. -/
private theorem integrableOn_besselK_one_remainder {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t ↦ exp (-(x * cosh t)) * exp (-t)) (Ioi 0) := by
  refine (integrableOn_exp_neg_Ioi 0).mono' (by fun_prop) (ae_of_all _ fun t ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  refine mul_le_of_le_one_left (exp_pos _).le (exp_le_one_iff.2 ?_)
  nlinarith [cosh_pos t]

/-- `K₁(x)` is `exp (-x) / x` plus the remainder `∫₀^∞ exp (-x cosh t) exp (-t) dt`. -/
private theorem besselK_one_eq {x : ℝ} (hx : 0 < x) :
    besselK 1 x = exp (-x) / x + ∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)) * exp (-t) := by
  have hrem := integrableOn_besselK_one_remainder hx.le
  -- `exp (-x cosh t) sinh t` has the antiderivative `-exp (-x cosh t) / x`.
  have hsinh : ∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)) * sinh t = exp (-x) / x := by
    have h := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (l := 0)
      (g := fun t ↦ -exp (-(x * cosh t)) / x)
      (g' := fun t ↦ exp (-(x * cosh t)) * sinh t) (fun t _ ↦ ?_)
      (fun t ht ↦ mul_nonneg (exp_pos _).le (sinh_nonneg_iff.2 (le_of_lt ht))) ?_
    · rw [h, cosh_zero, mul_one]
      ring
    · exact (((hasDerivAt_cosh t).const_mul x).fun_neg.exp.fun_neg.div_const x).congr_deriv
        (by field_simp)
    · have hcosh : Tendsto (fun t ↦ x * cosh t) atTop atTop :=
        tendsto_atTop_mono (fun t ↦ by rw [cosh_eq]; nlinarith [exp_pos (-t)])
          ((tendsto_exp_atTop.atTop_div_const two_pos).const_mul_atTop hx)
      simpa using ((tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hcosh)).neg.div_const x)
  have hsplit (t : ℝ) : exp (-(x * cosh t)) * cosh (1 * t) =
      exp (-(x * cosh t)) * sinh t + exp (-(x * cosh t)) * exp (-t) := by
    rw [one_mul]
    linear_combination exp (-(x * cosh t)) * cosh_sub_sinh t
  have hfirst : IntegrableOn (fun t ↦ exp (-(x * cosh t)) * sinh t) (Ioi 0) :=
    ((integrableOn_besselK_integrand 1 hx).sub hrem).congr_fun
      (fun t _ ↦ by simp only [Pi.sub_apply, hsplit]; ring) measurableSet_Ioi
  simp_rw [besselK_def, hsplit]
  rw [integral_add hfirst hrem, hsinh]

/-- The leading singular term of `K₁` is a strict lower bound: `exp (-x) / x < K₁(x)`. -/
theorem exp_neg_div_lt_besselK_one {x : ℝ} (hx : 0 < x) : exp (-x) / x < besselK 1 x := by
  rw [besselK_one_eq hx, lt_add_iff_pos_right, setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun t ↦ by positivity) (integrableOn_besselK_one_remainder hx.le),
    Function.support_eq_univ fun t ↦ by positivity, univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

/-- An upper bound matching `exp_neg_div_lt_besselK_one` up to the term `exp (-x)`:
`K₁(x) ≤ exp (-x) (1 + 1 / x)`. -/
theorem besselK_one_le_exp_neg_mul {x : ℝ} (hx : 0 < x) :
    besselK 1 x ≤ exp (-x) * (1 + 1 / x) := by
  rw [besselK_one_eq hx]
  have : ∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)) * exp (-t) ≤ exp (-x) := by
    calc ∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)) * exp (-t)
        ≤ ∫ t in Ioi (0 : ℝ), exp (-x) * exp (-t) := by
          refine setIntegral_mono_on (integrableOn_besselK_one_remainder hx.le)
            ((integrableOn_exp_neg_Ioi 0).const_mul _) measurableSet_Ioi fun t _ ↦ ?_
          gcongr
          nlinarith [one_le_cosh t]
      _ = exp (-x) := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [mul_add, mul_one_div]
  linarith

/-- `K₁` has a simple pole of unit residue at the origin: `x K₁(x) → 1` as `x → 0⁺`. -/
theorem tendsto_mul_besselK_one_nhdsGT_zero :
    Tendsto (fun x ↦ x * besselK 1 x) (𝓝[>] 0) (𝓝 1) := by
  have hlow : Tendsto (fun x ↦ exp (-x)) (𝓝[>] 0) (𝓝 1) :=
    ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x)).tendsto' 0 1 (by simp)).mono_left
      nhdsWithin_le_nhds
  have hupp : Tendsto (fun x ↦ exp (-x) * (x + 1)) (𝓝[>] 0) (𝓝 1) :=
    ((by fun_prop : Continuous fun x : ℝ ↦ exp (-x) * (x + 1)).tendsto' 0 1 (by simp)).mono_left
      nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    have := exp_neg_div_lt_besselK_one hx
    rw [div_lt_iff₀ hx] at this
    linarith
  · filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
    have := mul_le_mul_of_nonneg_left (besselK_one_le_exp_neg_mul hx) hx.le
    calc x * besselK 1 x ≤ x * (exp (-x) * (1 + 1 / x)) := this
      _ = exp (-x) * (x + 1) := by field_simp

/-- A logarithmic lower bound with the sharp coefficient: `-log x - 1 ≤ K_ν(x)` for `0 < x ≤ 1`,
in every order. -/
theorem neg_log_sub_one_le_besselK (ν : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    -log x - 1 ≤ besselK ν x := by
  -- On `(0, -log x]` the integrand is at least `1 - x exp t`, whose integral is `-log x - 1 + x`.
  have hT0 : 0 ≤ -log x := neg_nonneg.2 (log_nonpos hx.le hx1)
  have hlinint : IntervalIntegrable (fun t : ℝ ↦ x * exp t) volume 0 (-log x) :=
    (Real.continuous_exp.intervalIntegrable 0 (-log x)).const_mul x
  have hcomp : ∫ t in Ioc (0 : ℝ) (-log x), (1 - x * exp t)
      = -log x - x * (exp (-log x) - 1) := by
    rw [← intervalIntegral.integral_of_le hT0,
      intervalIntegral.integral_sub intervalIntegrable_const hlinint,
      intervalIntegral.integral_const_mul, integral_exp, intervalIntegral.integral_const]
    simp
  calc -log x - 1 ≤ -log x - x * (exp (-log x) - 1) := by
        rw [show exp (-log x) = x⁻¹ by rw [exp_neg, exp_log hx],
          show x * (x⁻¹ - 1) = 1 - x by field_simp]
        linarith
    _ = ∫ t in Ioc (0 : ℝ) (-log x), (1 - x * exp t) := hcomp.symm
    _ ≤ ∫ t in Ioc (0 : ℝ) (-log x), exp (-(x * cosh t)) * cosh (ν * t) := by
        refine setIntegral_mono_on (Continuous.integrableOn_Ioc (by fun_prop))
          ((integrableOn_besselK_integrand ν hx).mono_set Ioc_subset_Ioi_self)
          measurableSet_Ioc fun t ht ↦ ?_
        have hcexp : cosh t ≤ exp t := by
          rw [cosh_eq]
          linarith [exp_le_exp.2 (show -t ≤ t by linarith [ht.1])]
        have hxc : x * cosh t ≤ x * exp t := by gcongr
        calc 1 - x * exp t ≤ exp (-(x * cosh t)) := by
              linarith [add_one_le_exp (-(x * cosh t))]
          _ = exp (-(x * cosh t)) * 1 := (mul_one _).symm
          _ ≤ exp (-(x * cosh t)) * cosh (ν * t) := by
              gcongr
              exact one_le_cosh _
    _ ≤ besselK ν x :=
        setIntegral_mono_set (integrableOn_besselK_integrand ν hx)
          (ae_of_all _ fun t ↦ by positivity) Ioc_subset_Ioi_self.eventuallyLE

/-- A matching logarithmic upper bound for the order zero: `K₀(x) ≤ log (2/x) + e⁻¹` for
`0 < x ≤ 2`. -/
theorem besselK_zero_le_log_two_div_add_exp_neg_one {x : ℝ} (hx : 0 < x) (hx2 : x ≤ 2) :
    besselK 0 x ≤ log (2 / x) + exp (-1) := by
  -- Split at `t = log (2/x)`: below it the integrand is at most `1`, and beyond it
  -- `x cosh t ≥ 1 + (t - log (2/x))`, so the tail is at most `e⁻¹`.
  have hT0 : 0 ≤ log (2 / x) := log_nonneg ((one_le_div hx).2 hx2)
  have hexpT : exp (log (2 / x)) = 2 / x := exp_log (by positivity)
  have hint : IntegrableOn (fun t : ℝ ↦ exp (-(x * cosh t))) (Ioi 0) := by
    simpa using integrableOn_besselK_integrand 0 hx
  have hK0 : besselK 0 x = ∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)) := by
    rw [besselK_def]; simp
  have hdisj : Disjoint (Ioc (0 : ℝ) (log (2 / x))) (Ioi (log (2 / x))) := by
    rw [Set.disjoint_left]
    exact fun a ha hb ↦ absurd ha.2 (not_le.2 hb)
  have hsplit : (∫ t in Ioi (0 : ℝ), exp (-(x * cosh t)))
      = (∫ t in Ioc (0 : ℝ) (log (2 / x)), exp (-(x * cosh t)))
        + ∫ t in Ioi (log (2 / x)), exp (-(x * cosh t)) := by
    rw [← Ioc_union_Ioi_eq_Ioi hT0, setIntegral_union hdisj measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hT0))]
  have hhead : (∫ t in Ioc (0 : ℝ) (log (2 / x)), exp (-(x * cosh t))) ≤ log (2 / x) := by
    calc (∫ t in Ioc (0 : ℝ) (log (2 / x)), exp (-(x * cosh t)))
        ≤ ∫ _ in Ioc (0 : ℝ) (log (2 / x)), (1 : ℝ) := by
          refine setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self)
            (integrableOn_const (by simp)) measurableSet_Ioc fun t _ ↦ ?_
          exact exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
      _ = log (2 / x) := by
          rw [setIntegral_const, Real.volume_real_Ioc, sub_zero, max_eq_left hT0, smul_eq_mul,
            mul_one]
  have htail : (∫ t in Ioi (log (2 / x)), exp (-(x * cosh t))) ≤ exp (-1) := by
    calc (∫ t in Ioi (log (2 / x)), exp (-(x * cosh t)))
        ≤ ∫ t in Ioi (log (2 / x)), exp (-1) * exp (log (2 / x)) * exp (-t) := by
          refine setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hT0))
            ((integrableOn_exp_neg_Ioi _).const_mul _) measurableSet_Ioi fun t _ ↦ ?_
          rw [← exp_add, ← exp_add]
          refine exp_le_exp.2 ?_
          have hsub : exp (t - log (2 / x)) = x / 2 * exp t := by
            rw [exp_sub, hexpT]; field_simp
          have hcosh : x / 2 * exp t ≤ x * cosh t := by
            rw [cosh_eq]; nlinarith [exp_pos (-t), hx]
          have hexp := add_one_le_exp (t - log (2 / x))
          rw [hsub] at hexp
          linarith
      _ = exp (-1) := by
          rw [integral_const_mul, integral_exp_neg_Ioi, mul_assoc, ← exp_add, add_neg_cancel,
            exp_zero, mul_one]
  rw [hK0, hsplit]
  linarith

/-- Every `K_ν` diverges at the origin. -/
theorem tendsto_besselK_nhdsGT_zero (ν : ℝ) : Tendsto (besselK ν) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun x : ℝ ↦ -log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  refine tendsto_atTop_mono' _ ?_ (hlog.atTop_div_const two_pos)
  filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1),
    hlog.eventually_ge_atTop 2] with x (hx : 0 < x) hx1 hM
  linarith [neg_log_sub_one_le_besselK ν hx hx1.2]

/-- `K₀` is logarithmic at the origin: `K₀(x) ~ -log x` as `x → 0⁺`. -/
theorem isEquivalent_besselK_zero_neg_log :
    besselK 0 ~[𝓝[>] (0 : ℝ)] fun x ↦ -log x := by
  have hlog : Tendsto (fun x : ℝ ↦ -log x) (𝓝[>] 0) atTop :=
    tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero
  have hpos : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < -log x := hlog.eventually_gt_atTop 0
  rw [isEquivalent_iff_tendsto_one (hpos.mono fun x h ↦ ne_of_gt h)]
  have hinv : Tendsto (fun x : ℝ ↦ (-log x)⁻¹) (𝓝[>] 0) (𝓝 0) := hlog.inv_tendsto_atTop
  have hlow : Tendsto (fun x : ℝ ↦ 1 - (-log x)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hupp : Tendsto (fun x : ℝ ↦ 1 + (log 2 + exp (-1)) * (-log x)⁻¹) (𝓝[>] 0) (𝓝 1) := by
    simpa using tendsto_const_nhds.add (hinv.const_mul (log 2 + exp (-1)))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1), hpos]
      with x (hx : 0 < x) hx1 hM
    have hlne : log x ≠ 0 := neg_ne_zero.mp (ne_of_gt hM)
    rw [Pi.div_apply, le_div_iff₀ hM, show (1 - (-log x)⁻¹) * -log x = -log x - 1 by
      field_simp; ring]
    exact neg_log_sub_one_le_besselK 0 hx hx1.2
  · filter_upwards [self_mem_nhdsWithin, Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 2), hpos]
      with x (hx : 0 < x) hx2 hM
    have hlne : log x ≠ 0 := neg_ne_zero.mp (ne_of_gt hM)
    rw [Pi.div_apply, div_le_iff₀ hM,
      show (1 + (log 2 + exp (-1)) * (-log x)⁻¹) * -log x = -log x + log 2 + exp (-1) by
        field_simp; ring]
    have hb := besselK_zero_le_log_two_div_add_exp_neg_one hx hx2.2
    rw [log_div two_ne_zero hx.ne'] at hb
    linarith

end EpsilonEridani
