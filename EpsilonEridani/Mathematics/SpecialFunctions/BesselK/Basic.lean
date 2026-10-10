/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

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
derivative relation `K₀' = -K₁`, the exponential decay at large argument, the simple pole of `K₁`
and the at-least-logarithmic divergence of every `K_ν` at the origin.

For `x ≤ 0` the integrand is bounded below by `1`, so the integral is not convergent and the
Bochner integral returns `0`; `besselK_of_nonpos` records this value, so that statements on the
whole real line need no domain hypothesis where `0` is harmless.

## Main definitions

* `EpsilonEridani.besselK ν x`: the modified Bessel function `K_ν(x)`.

## Main statements

* `EpsilonEridani.integrableOn_besselK_integrand`: the integral converges for `x > 0`.
* `EpsilonEridani.besselK_pos`: `K_ν(x) > 0` for `x > 0`.
* `EpsilonEridani.besselK_le_besselK`: `K_ν ≤ K_μ` when `|ν| ≤ |μ|`.
* `EpsilonEridani.hasDerivAt_besselK`: `K_ν' = -(K_{ν-1} + K_{ν+1}) / 2`, and its special
  case `EpsilonEridani.hasDerivAt_besselK_zero`: `K₀' = -K₁`.
* `EpsilonEridani.strictAntiOn_besselK`: `K_ν` is strictly decreasing on `(0, ∞)`.
* `EpsilonEridani.besselK_le_exp_mul_besselK`: `K_ν(x) ≤ exp (-(x - x₀)) K_ν(x₀)` for
  `0 < x₀ ≤ x`.
* `EpsilonEridani.exp_neg_div_lt_besselK_one`,
  `EpsilonEridani.besselK_one_le_exp_neg_mul`: `exp (-x) / x < K₁(x) ≤ exp (-x) (1 + 1 / x)`,
  and hence `EpsilonEridani.tendsto_mul_besselK_one_nhdsGT_zero`: `x K₁(x) → 1` as `x → 0⁺`.
* `EpsilonEridani.neg_log_mul_exp_neg_one_le_besselK`: `-log x / e ≤ K_ν(x)` for `x > 0`,
  and hence `EpsilonEridani.tendsto_besselK_nhdsGT_zero`: `K_ν(x) → ∞` as `x → 0⁺`.

## References

* NIST Digital Library of Mathematical Functions, §10.25, §10.29 and §10.32.
* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd edition, Cambridge University
  Press (1944), §6.22.
-/

@[expose] public section

noncomputable section

open Real MeasureTheory Set Filter Topology

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

/-- A logarithmic lower bound, `-log x / e ≤ K_ν(x)` for every order and every `x > 0`. -/
theorem neg_log_mul_exp_neg_one_le_besselK (ν : ℝ) {x : ℝ} (hx : 0 < x) :
    -log x * exp (-1) ≤ besselK ν x := by
  rcases le_or_gt 1 x with h1 | h1
  · have : -log x * exp (-1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (log_nonneg h1)) (exp_pos _).le
    exact this.trans (besselK_nonneg ν x)
  -- On `(0, -log x]` one has `x cosh t ≤ x exp t ≤ 1`, so the integrand is at least `exp (-1)`.
  set T := -log x
  have hT : 0 < T := neg_pos.2 (log_neg hx h1)
  have hint := integrableOn_besselK_integrand ν hx
  calc -log x * exp (-1) = ∫ _ in Ioc 0 T, exp (-1) := by
        rw [setIntegral_const, Real.volume_real_Ioc, sub_zero, max_eq_left hT.le, smul_eq_mul]
    _ ≤ ∫ t in Ioc 0 T, exp (-(x * cosh t)) * cosh (ν * t) := by
        refine setIntegral_mono_on (integrableOn_const (by simp))
          (hint.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc fun t ht ↦ ?_
        have hct : x * cosh t ≤ 1 := by
          have hcexp : cosh t ≤ exp t := by
            rw [cosh_eq]
            linarith [exp_le_exp.2 (show -t ≤ t by linarith [ht.1])]
          have hexp : exp t ≤ exp T := exp_le_exp.2 ht.2
          rw [show exp T = x⁻¹ by rw [exp_neg, exp_log hx]] at hexp
          calc x * cosh t ≤ x * x⁻¹ := by gcongr; exact hcexp.trans hexp
            _ = 1 := mul_inv_cancel₀ hx.ne'
        calc exp (-1) = exp (-1) * 1 := (mul_one _).symm
          _ ≤ exp (-(x * cosh t)) * cosh (ν * t) := by
            gcongr
            exact one_le_cosh _
    _ ≤ besselK ν x :=
        setIntegral_mono_set hint (ae_of_all _ fun t ↦ by positivity)
          (Ioc_subset_Ioi_self.eventuallyLE)

/-- Every `K_ν` diverges at the origin. -/
theorem tendsto_besselK_nhdsGT_zero (ν : ℝ) : Tendsto (besselK ν) (𝓝[>] 0) atTop := by
  have hlog : Tendsto (fun x ↦ -log x * exp (-1)) (𝓝[>] 0) atTop :=
    (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsGT_zero).atTop_mul_const (exp_pos _)
  refine tendsto_atTop_mono' _ ?_ hlog
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x)
  exact neg_log_mul_exp_neg_one_le_besselK ν hx

end EpsilonEridani
