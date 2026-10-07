/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Convolution.Mellin
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The strip of convergence of the Mellin transform on the unit interval

A collinear density is a real function `f` of the momentum fraction, supported in `[0, 1]` and
locally integrable on the momentum-fraction interval. Its Mellin transform
`mellinDis f N = ∫_{(0,1]} x ^ (N - 1) * f x dx` converges at `N` exactly when `f` lies in the
weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`. This file determines the set of such `N`.

On `(0, 1]` the weight `x ^ (σ - 1)` decreases as `σ` grows, so convergence at `σ₀` implies
convergence at every `σ ≥ σ₀`. The domain of convergence is therefore a right half-plane, whose
abscissa is fixed by the behaviour of `f` as `x → 0`: if `f x = O(x ^ (-b))` there, the transform
converges and is holomorphic for `b < Re N`. A density behaving like `x ^ (-1 - λ)` at small `x`
thus has its moments from `Re N > 1 + λ` on. The bound is sharp: `x ^ (-b)` itself has a
convergent transform exactly for `b < Re N`.

The holomorphy is obtained from Mathlib's `mellin`, the transform on the half-line, through the
identity `mellinDis f = mellin (Set.indicator (Set.Ioc 0 1) f)`, which for a density supported in
`[0, 1]` reads `mellinDis f = mellin f`.

## Main results

* `mellinDisConvergent_iff_integrableOn_rpow_mul`: convergence at `N` is membership of `f` in the
  weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`.
* `MellinDisConvergent.of_re_le_re`, `isUpperSet_setOf_mellinDisConvergent`: convergence propagates
  to larger real parts, so the real points of convergence form an upper set, in particular an
  interval.
* `mellinDis_eq_mellin_indicator`, `mellinDis_eq_mellin`: the bridge to Mathlib's `mellin`.
* `mellinDisConvergent_of_isBigO_rpow`, `differentiableOn_mellinDis`: if `f` is locally
  integrable on `(0, 1]` and `f x = O(x ^ (-b))` as `x → 0⁺`, the transform converges and is
  holomorphic on the half-plane `b < Re N`.
* `mellinDisConvergent_rpow_neg_iff`: for `f x = x ^ (-b)` the half-plane `b < Re N` is exactly
  the domain of convergence.

## References

* F. J. Yndurain, *The Theory of Quark and Gluon Interactions*, 4th ed., Springer (2006),
  ch. 4.
-/

public section

noncomputable section

open MeasureTheory Set Filter Asymptotics Topology

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Convolution

variable {f : ℝ → ℝ}

/-!
## The weighted spaces
-/

/-- Convergence of the Mellin transform on the unit interval forces `f` to be
a.e.-strongly-measurable on `(0, 1]`: there `f x` is recovered from the integrand by multiplying
with the continuous function `x ^ (1 - N)`. -/
theorem MellinDisConvergent.aestronglyMeasurable {N : ℂ} (h : MellinDisConvergent f N) :
    AEStronglyMeasurable f (volume.restrict (Ioc 0 1)) := by
  have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (1 - N)) (Ioc 0 1) := fun x hx =>
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx.1.ne')).continuousWithinAt
  refine (Complex.continuous_re.comp_aestronglyMeasurable
    ((hc.aestronglyMeasurable measurableSet_Ioc).mul (Integrable.aestronglyMeasurable h))).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.1.ne'
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← Complex.cpow_add _ _ hx0, sub_add_sub_cancel', sub_self, Complex.cpow_zero,
    one_mul, Complex.ofReal_re]

/-- The Mellin transform on the unit interval converges at `N` exactly when `f` lies in the
weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`. In particular convergence depends on `N` only
through its real part. -/
theorem mellinDisConvergent_iff_integrableOn_rpow_mul {N : ℂ} :
    MellinDisConvergent f N ↔ IntegrableOn (fun x => x ^ (N.re - 1) * f x) (Ioc 0 1) := by
  -- On `(0, 1]` the complex and the real integrand have the same norm.
  have hnorm : ∀ x ∈ Ioc (0 : ℝ) 1,
      ‖(x : ℂ) ^ (N - 1) * (f x : ℂ)‖ = ‖x ^ (N.re - 1) * f x‖ := fun x hx => by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx.1, Complex.norm_real, norm_mul,
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le, Complex.sub_re, Complex.one_re]
  have hw : ∀ σ : ℝ, ContinuousOn (fun x : ℝ => x ^ σ) (Ioc 0 1) := fun _ x hx =>
    (Real.continuousAt_rpow_const _ _ (Or.inl hx.1.ne')).continuousWithinAt
  constructor
  · intro h
    refine Integrable.mono' h.norm (((hw _).aestronglyMeasurable measurableSet_Ioc).mul
      h.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (hnorm x hx).symm.le
  · intro h
    -- `f` is measurable on `(0, 1]`, being `x ^ (1 - Re N)` times the real integrand.
    have hf : AEStronglyMeasurable f (volume.restrict (Ioc 0 1)) := by
      refine (((hw (1 - N.re)).aestronglyMeasurable measurableSet_Ioc).mul
        h.aestronglyMeasurable).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      rw [Pi.mul_apply, ← mul_assoc, ← Real.rpow_add hx.1, sub_add_sub_cancel', sub_self,
        Real.rpow_zero, one_mul]
    have hc : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (N - 1)) (Ioc 0 1) := fun x hx =>
      (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hx.1.ne')).continuousWithinAt
    refine Integrable.mono' h.norm ((hc.aestronglyMeasurable measurableSet_Ioc).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hf)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (hnorm x hx).le

/-- Convergence of the Mellin transform depends only on the real part of the index. -/
theorem mellinDisConvergent_iff_re {N : ℂ} :
    MellinDisConvergent f N ↔ MellinDisConvergent f N.re := by
  rw [mellinDisConvergent_iff_integrableOn_rpow_mul, mellinDisConvergent_iff_integrableOn_rpow_mul,
    Complex.ofReal_re]

/-!
## The domain of convergence is a right half-plane
-/

/-- Convergence of the Mellin transform on the unit interval propagates to larger real parts:
on `(0, 1]` the weight `x ^ (Re M - 1)` is bounded by `x ^ (Re N - 1)` when `Re N ≤ Re M`. -/
theorem MellinDisConvergent.of_re_le_re {N M : ℂ} (h : MellinDisConvergent f N)
    (hNM : N.re ≤ M.re) : MellinDisConvergent f M := by
  have hf := h.aestronglyMeasurable
  have hw : ContinuousOn (fun x : ℝ => x ^ (M.re - 1)) (Ioc 0 1) := fun x hx =>
    (Real.continuousAt_rpow_const _ _ (Or.inl hx.1.ne')).continuousWithinAt
  rw [mellinDisConvergent_iff_integrableOn_rpow_mul] at h ⊢
  refine Integrable.mono' h.norm ((hw.aestronglyMeasurable measurableSet_Ioc).mul hf) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)) (norm_nonneg _)

/-- The real indices at which the Mellin transform on the unit interval converges form an upper
set. In particular they form an interval (`IsUpperSet.ordConnected`): a density integrable
against `x ^ (σ₀ - 1)` and against `x ^ (σ₁ - 1)` is integrable against `x ^ (σ - 1)` for every
`σ` between `σ₀` and `σ₁`. -/
theorem isUpperSet_setOf_mellinDisConvergent (f : ℝ → ℝ) :
    IsUpperSet {σ : ℝ | MellinDisConvergent f σ} := fun σ τ hστ hσ =>
  MellinDisConvergent.of_re_le_re hσ (by simpa using hστ)

/-!
## The bridge to Mathlib's Mellin transform
-/

/-- The Mellin transform on the unit interval is Mathlib's Mellin transform on the half-line of
the restriction of `f` to `(0, 1]`, extended by zero. -/
theorem mellinDis_eq_mellin_indicator (f : ℝ → ℝ) (N : ℂ) :
    mellinDis f N = mellin (fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ)) N := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self, mellinDis]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [indicator_of_mem hx, smul_eq_mul]
  · intro x hx
    rw [indicator_of_notMem hx.2, Complex.ofReal_zero, smul_zero]

/-- For a function vanishing on `(1, ∞)`, in particular for a density supported in `[0, 1]`, the
Mellin transform on the unit interval is Mathlib's Mellin transform on the half-line. -/
theorem mellinDis_eq_mellin (hf : Function.support f ⊆ Iic 1) (N : ℂ) :
    mellinDis f N = mellin (fun x => (f x : ℂ)) N := by
  rw [mellinDis_eq_mellin_indicator, mellin, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [indicator_of_mem (mem_Ioc.mpr ⟨hx, hx1⟩)]
  · rw [indicator_of_notMem fun h => hx1.not_ge h.2,
      Function.notMem_support.mp fun h => hx1.not_ge (hf h)]

/-!
## The abscissa of convergence and the small-`x` behaviour
-/

/-- The extension by zero of `f` from `(0, 1]` to the half-line meets the hypotheses of Mathlib's
convergence and holomorphy theorems for `mellin` at every `N` with `b < Re N`. -/
private lemma mellinConvergent_and_differentiableAt_indicator
    (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ} (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ}
    (hN : b < N.re) :
    MellinConvergent (fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ)) N ∧
      DifferentiableAt ℂ (mellin fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ)) N := by
  -- Local integrability on the half-line: a compact `k ⊆ (0, ∞)` meets `(0, 1]` inside the
  -- compact interval `[inf k, 1] ⊆ (0, 1]`, on which `f` is integrable.
  have hloc : LocallyIntegrableOn (fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ)) (Ioi 0) := by
    rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
    intro k hk hkc
    rcases k.eq_empty_or_nonempty with rfl | hne
    · exact integrableOn_empty
    have hpos : 0 < sInf k := hk (hkc.sInf_mem hne)
    have hIcc : IntegrableOn f (Icc (sInf k) 1) :=
      hf.integrableOn_compact_subset (fun x hx => ⟨hpos.trans_le hx.1, hx.2⟩) isCompact_Icc
    exact Integrable.ofReal ((integrableOn_indicator_iff measurableSet_Ioc).mpr
      (hIcc.mono_set fun x hx => ⟨csInf_le hkc.bddBelow hx.2, hx.1.2⟩))
  -- The extension vanishes on `(1, ∞)`, so it satisfies any growth bound at infinity.
  have htop : (fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ)) =O[atTop]
      fun x => x ^ (-(N.re + 1)) := by
    refine EventuallyEq.trans_isBigO ?_ (isBigO_zero _ _)
    filter_upwards [eventually_gt_atTop 1] with x hx
    rw [indicator_of_notMem fun h => hx.not_ge h.2, Complex.ofReal_zero]
  -- Near `0⁺` the extension agrees with `f`.
  have hzero : (fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ)) =O[𝓝[>] 0]
      fun x => x ^ (-b) := by
    refine isBigO_norm_left.mp (EventuallyEq.trans_isBigO ?_ hb.norm_left)
    filter_upwards [Ioo_mem_nhdsGT one_pos] with x hx
    rw [indicator_of_mem (Ioo_subset_Ioc_self hx), Complex.norm_real]
  exact ⟨mellinConvergent_of_isBigO_rpow hloc htop (lt_add_one _) hzero hN,
    mellin_differentiableAt_of_isBigO_rpow hloc htop (lt_add_one _) hzero hN⟩

/-- **The abscissa of convergence.** If `f` is locally integrable on `(0, 1]` and
`f x = O(x ^ (-b))` as `x → 0⁺`, the Mellin transform on the unit interval converges on the
half-plane `b < Re N`. For a density behaving like `x ^ (-1 - λ)` at small `x` this is the
half-plane `1 + λ < Re N`. -/
theorem mellinDisConvergent_of_isBigO_rpow (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ} (hN : b < N.re) :
    MellinDisConvergent f N := by
  have h := (mellinConvergent_and_differentiableAt_indicator hf hb hN).1
  refine (h.mono_set Ioc_subset_Ioi_self).congr_fun (fun x hx => ?_) measurableSet_Ioc
  simp only [indicator_of_mem hx, smul_eq_mul]

/-- **Holomorphy in the strip.** If `f` is locally integrable on `(0, 1]` and
`f x = O(x ^ (-b))` as `x → 0⁺`, the Mellin transform on the unit interval is complex
differentiable at every `N` with `b < Re N`. -/
theorem differentiableAt_mellinDis (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ} (hN : b < N.re) :
    DifferentiableAt ℂ (mellinDis f) N := by
  have h : mellinDis f = mellin fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ) :=
    funext (mellinDis_eq_mellin_indicator f)
  rw [h]
  exact (mellinConvergent_and_differentiableAt_indicator hf hb hN).2

/-- If `f` is locally integrable on `(0, 1]` and `f x = O(x ^ (-b))` as `x → 0⁺`, the Mellin
transform on the unit interval is holomorphic on the half-plane `b < Re N`. -/
theorem differentiableOn_mellinDis (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) :
    DifferentiableOn ℂ (mellinDis f) {N | b < N.re} := fun _ hN =>
  (differentiableAt_mellinDis hf hb hN).differentiableWithinAt

/-- **The abscissa is sharp.** The power `x ^ (-b)` has a convergent Mellin transform on the unit
interval exactly on the half-plane `b < Re N`, so the half-plane of
`mellinDisConvergent_of_isBigO_rpow` cannot be enlarged under its hypotheses. -/
theorem mellinDisConvergent_rpow_neg_iff {b : ℝ} {N : ℂ} :
    MellinDisConvergent (fun x => x ^ (-b)) N ↔ b < N.re := by
  rw [mellinDisConvergent_iff_integrableOn_rpow_mul, integrableOn_Ioc_iff_integrableOn_Ioo,
    integrableOn_congr_fun (g := fun x => x ^ (N.re - 1 - b)) (fun x hx => by
      dsimp only; rw [← Real.rpow_add hx.1, ← sub_eq_add_neg]) measurableSet_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff one_pos]
  constructor <;> intro h <;> linarith

end Convolution
end Factorization
end QFT
end EpsilonEridani
