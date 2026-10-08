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
* `mellinDisConvergent_rpow_neg_iff`: for `f x = x ^ (-b)` the half-plane `b < Re N` is exactly
  the domain of convergence.

## References

* F. J. Ynduráin, *The Theory of Quark and Gluon Interactions*, 4th ed., Springer (2006), ch. 4.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Asymptotics Topology

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Convolution

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

/-- Holomorphy in the strip: `mellinDis f` is complex differentiable at every `N`
with `b < Re N`. -/
theorem differentiableAt_mellinDis (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ} (hN : b < N.re) :
    DifferentiableAt ℂ (mellinDis f) N := by
  have h : mellinDis f = mellin fun x => (((Ioc 0 1).indicator f x : ℝ) : ℂ) :=
    funext (mellinDis_eq_mellin_indicator f)
  rw [h]
  exact (mellinConvergent_and_differentiableAt_indicator hf hb hN).2

/-- Holomorphy on the half-plane: `mellinDis f` is differentiable on `{N | b < N.re}`. -/
theorem differentiableOn_mellinDis (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) :
    DifferentiableOn ℂ (mellinDis f) {N | b < N.re} := fun _ hN =>
  (differentiableAt_mellinDis hf hb hN).differentiableWithinAt

/-- The abscissa is sharp: the half-plane `b < Re N` cannot be enlarged under its hypotheses. -/
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
