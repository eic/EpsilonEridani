/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Functions and integrals on a real half-line

Facts about functions on a half-line `(b, ∞)` of the real line, as used to build radial wave
functions piece by piece and to evaluate their moments.

* `memLp_piecewise_Ioi_const`: the function equal to `v` on `(R, ∞)` and to a constant `a`
  elsewhere is in `Lᵖ` on `(b, ∞)`, for `b ≤ R`, when `v` is in `Lᵖ` on `(R, ∞)`.
* `setIntegral_piecewise_Ioi_const`: its integral over `(b, ∞)` is `(R - b) • a + ∫_R^∞ v`;
  `setIntegral_piecewise_Ioi_const_sq`: the integral of its square is
  `(R - b) * a ^ 2 + ∫_R^∞ v ^ 2`.
* `setIntegral_Ioi_pow_mul_exp_neg_pos`: `∫_a^∞ r ^ n * exp (-c * r) dr` is positive for
  `0 ≤ a` and `0 < c`.
-/

public section

namespace EpsilonEridani

open MeasureTheory Set

/-- The function equal to `v` on `(R, ∞)` and to the constant `a` elsewhere is in `Lᵖ` on the
half-line `(b, ∞)`, for `b ≤ R`, when `v` is in `Lᵖ` on `(R, ∞)`. -/
theorem memLp_piecewise_Ioi_const {E : Type*} [NormedAddCommGroup E] {p : ENNReal} {b R : ℝ}
    (hbR : b ≤ R) (a : E) {v : ℝ → E} (hv : MemLp v p (volume.restrict (Ioi R))) :
    MemLp ((Ioi R).piecewise v fun _ => a) p (volume.restrict (Ioi b)) := by
  refine MemLp.piecewise measurableSet_Ioi.nullMeasurableSet ?_ ?_
  · rwa [Measure.restrict_restrict measurableSet_Ioi, inter_eq_left.2 (Ioi_subset_Ioi hbR)]
  · rw [Measure.restrict_restrict measurableSet_Ioi.compl, compl_Ioi, Iic_inter_Ioi]
    exact memLp_const a

/-- The integral over the half-line `(b, ∞)` of the function equal to `f` on `(R, ∞)` and to
the constant `a` elsewhere, for `b ≤ R`, is `(R - b) • a + ∫_R^∞ f`. -/
theorem setIntegral_piecewise_Ioi_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {b R : ℝ} (hbR : b ≤ R) (a : E) {f : ℝ → E}
    (hf : IntegrableOn f (Ioi R)) :
    ∫ r in Ioi b, (Ioi R).piecewise f (fun _ => a) r = (R - b) • a + ∫ r in Ioi R, f r := by
  have hIoc : EqOn ((Ioi R).piecewise f fun _ => a) (fun _ => a) (Ioc b R) :=
    fun r hr => piecewise_eq_of_notMem _ _ _ (notMem_Ioi.2 hr.2)
  have hIoi : EqOn ((Ioi R).piecewise f fun _ => a) f (Ioi R) :=
    fun r hr => piecewise_eq_of_mem _ _ _ hr
  rw [← Ioc_union_Ioi_eq_Ioi hbR, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    ((integrableOn_const measure_Ioc_lt_top.ne).congr_fun hIoc.symm measurableSet_Ioc)
    (hf.congr_fun hIoi.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioc hIoc, setIntegral_congr_fun measurableSet_Ioi hIoi,
    setIntegral_const, Real.volume_real_Ioc_of_le hbR]

/-- The integral over the half-line `(b, ∞)` of the square of the function equal to `v` on
`(R, ∞)` and to the constant `a` elsewhere, for `b ≤ R`, is `(R - b) * a ^ 2 + ∫_R^∞ v ^ 2`. -/
theorem setIntegral_piecewise_Ioi_const_sq {b R : ℝ} (hbR : b ≤ R) (a : ℝ) {v : ℝ → ℝ}
    (hv : IntegrableOn (fun r => v r ^ 2) (Ioi R)) :
    ∫ r in Ioi b, (Ioi R).piecewise v (fun _ => a) r ^ 2 =
      (R - b) * a ^ 2 + ∫ r in Ioi R, v r ^ 2 := by
  rw [← smul_eq_mul, ← setIntegral_piecewise_Ioi_const hbR (a ^ 2) hv]
  exact integral_congr_ae (ae_of_all _ fun _ =>
    apply_piecewise (Ioi R) v (fun _ => a) fun _ x => x ^ 2)

/-- The integral `∫_a^∞ r ^ n * exp (-c * r) dr` is positive for `0 ≤ a` and `0 < c`. -/
theorem setIntegral_Ioi_pow_mul_exp_neg_pos (n : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hc : 0 < c) :
    0 < ∫ r in Ioi a, r ^ n * Real.exp (-c * r) := by
  have hint : IntegrableOn (fun r : ℝ => r ^ n * Real.exp (-c * r)) (Ioi a) :=
    ((integrableOn_rpow_mul_exp_neg_mul_rpow (s := n) (p := 1)
      (neg_one_lt_zero.trans_le n.cast_nonneg) one_pos hc).mono_set (Ioi_subset_Ioi ha)).congr_fun
      (fun r _ => by simp [Real.rpow_one, Real.rpow_natCast]) measurableSet_Ioi
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ hint).2 ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r (hr : a < r)
    have := ha.trans_lt hr
    positivity
  · refine lt_of_lt_of_le (by simp [Real.volume_Ioi]) (measure_mono (s := Ioi a)
      fun r (hr : r ∈ Ioi a) => ⟨(mul_pos (pow_pos (ha.trans_lt hr) n)
        (Real.exp_pos _)).ne', hr⟩)

end EpsilonEridani
