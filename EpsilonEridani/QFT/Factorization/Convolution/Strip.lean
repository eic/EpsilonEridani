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
weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`. This file studies the set of such `N`.

On `(0, 1]` the weight `x ^ (σ - 1)` decreases as `σ` grows, so convergence at `σ₀` implies
convergence at every `σ ≥ σ₀`: the domain of convergence is a right half-plane. Its position is
controlled by the behaviour of `f` as `x → 0`: if `f x = O(x ^ (-b))` there, the transform
converges and is holomorphic for `b < Re N`. A density behaving like `x ^ (-1 - λ)` at small `x`
thus has its moments from `Re N > 1 + λ` on. For the bound itself this half-plane is maximal:
`x ^ (-b)` has a convergent transform exactly for `b < Re N`.

Convergence and holomorphy are obtained from Mathlib's `mellin`, the transform on the half-line,
through the extension of `f` by zero, `Set.indicator (Set.Ioc 0 1) fun x => (f x : ℂ)`: the two
transforms agree, and converge at the same indices. For a density supported in `[0, 1]` this reads
`mellinDis f = mellin f`.

## Main results

* `mellinDisConvergent_iff_integrableOn_rpow_mul`: convergence at `N` is membership of `f` in the
  weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`; `mellinDisConvergent_iff_re`: it depends only
  on `Re N`.
* `MellinDisConvergent.of_re_le_re`, `isUpperSet_setOf_mellinDisConvergent`: convergence propagates
  to larger real parts, so the real points of convergence form an upper set, in particular an
  interval.
* `mellinDis_eq_mellin_indicator`, `mellinDisConvergent_iff_mellinConvergent_indicator`: the bridge
  to Mathlib's `mellin`, for values and for convergence; `mellinDis_eq_mellin` for a density
  supported in `[0, 1]`.
* `locallyIntegrableOn_Ioi_indicator_Ioc`, `indicator_Ioc_eventuallyEq_zero_atTop`,
  `indicator_Ioc_eventuallyEq_nhdsGT`: the extension by zero meets the hypotheses of Mathlib's
  convergence and holomorphy theorems for `mellin`.
* `mellinDisConvergent_of_isBigO_rpow`, `differentiableAt_mellinDis`, `differentiableOn_mellinDis`:
  if `f x = O(x ^ (-b))` as `x → 0⁺`, the transform converges and is holomorphic on `b < Re N`.
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

variable {f : ℝ → ℝ}

/-!
## The weighted spaces
-/

/-- Dividing out a power weight: if `x ^ c * f x` is integrable on a measurable `s ⊆ (0, ∞)`, then
`f` is a.e.-strongly-measurable on `s`. -/
theorem aestronglyMeasurable_of_integrableOn_cpow_mul {s : Set ℝ} (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) {c : ℂ} (h : IntegrableOn (fun x : ℝ => (x : ℂ) ^ c * (f x : ℂ)) s) :
    AEStronglyMeasurable f (volume.restrict s) := by
  have hw : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-c)) s :=
    Complex.continuous_ofReal.continuousOn.cpow_const fun x hx =>
      Complex.ofReal_mem_slitPlane.mpr (hs0 hx)
  refine (Complex.continuous_re.comp_aestronglyMeasurable
    ((hw.aestronglyMeasurable hs).mul h.aestronglyMeasurable)).congr ?_
  filter_upwards [ae_restrict_mem hs] with x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hs0 hx).ne'
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← Complex.cpow_add _ _ hx0, neg_add_cancel, Complex.cpow_zero, one_mul,
    Complex.ofReal_re]

/-- Dividing out a real power weight: if `x ^ σ * f x` is integrable on a measurable
`s ⊆ (0, ∞)`, then `f` is a.e.-strongly-measurable on `s`. -/
theorem aestronglyMeasurable_of_integrableOn_rpow_mul {s : Set ℝ} (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) {σ : ℝ} (h : IntegrableOn (fun x => x ^ σ * f x) s) :
    AEStronglyMeasurable f (volume.restrict s) := by
  refine aestronglyMeasurable_of_integrableOn_cpow_mul hs hs0 (c := σ)
    (h.ofReal.congr_fun (fun x hx => ?_) hs)
  rw [← Complex.ofReal_cpow (hs0 hx).le]
  exact Complex.ofReal_mul _ _

/-- Convergence of the Mellin transform on the unit interval forces `f` to be
a.e.-strongly-measurable on `(0, 1]`. -/
theorem MellinDisConvergent.aestronglyMeasurable {N : ℂ} (h : MellinDisConvergent f N) :
    AEStronglyMeasurable f (volume.restrict (Ioc 0 1)) :=
  aestronglyMeasurable_of_integrableOn_cpow_mul measurableSet_Ioc Ioc_subset_Ioi_self
    (mellinDisConvergent_def.mp h)

/-- The Mellin transform on the unit interval converges at `N` exactly when `f` lies in the
weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`. In particular convergence depends on `N` only
through its real part. -/
theorem mellinDisConvergent_iff_integrableOn_rpow_mul {N : ℂ} :
    MellinDisConvergent f N ↔ IntegrableOn (fun x => x ^ (N.re - 1) * f x) (Ioc 0 1) := by
  -- Either side makes `f` measurable on `(0, 1]`; given that, the statement is Mathlib's
  -- `mellin_convergent_iff_norm` for the extension of `f` by zero.
  suffices key : AEStronglyMeasurable f (volume.restrict (Ioc 0 1)) →
      (MellinDisConvergent f N ↔ IntegrableOn (fun x => x ^ (N.re - 1) * f x) (Ioc 0 1)) from
    ⟨fun h => (key h.aestronglyMeasurable).mp h, fun h => (key <|
      aestronglyMeasurable_of_integrableOn_rpow_mul measurableSet_Ioc Ioc_subset_Ioi_self h).mpr h⟩
  intro hf
  have hg : AEStronglyMeasurable ((Ioc 0 1).indicator fun x => (f x : ℂ))
      (volume.restrict (Ioi 0)) := by
    rw [aestronglyMeasurable_indicator_iff measurableSet_Ioc,
      Measure.restrict_restrict_of_subset Ioc_subset_Ioi_self]
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable hf
  have hw : ContinuousOn (fun x : ℝ => x ^ (N.re - 1)) (Ioc 0 1) :=
    continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne'
  rw [mellinDisConvergent_def]
  refine (integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioc).trans
    ((mellin_convergent_iff_norm (s := N) Ioc_subset_Ioi_self measurableSet_Ioc hg).trans
      ((integrableOn_congr_fun (g := fun x => ‖x ^ (N.re - 1) * f x‖) (fun x hx => ?_)
        measurableSet_Ioc).trans (integrable_norm_iff
          ((hw.aestronglyMeasurable measurableSet_Ioc).mul hf))))
  · rw [indicator_of_mem hx, smul_eq_mul]
  · dsimp only
    rw [indicator_of_mem hx, Complex.norm_real, norm_mul,
      Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le]

/-- Convergence of the Mellin transform depends only on the real part of the index. -/
theorem mellinDisConvergent_iff_re {N : ℂ} :
    MellinDisConvergent f N ↔ MellinDisConvergent f N.re := by
  rw [mellinDisConvergent_iff_integrableOn_rpow_mul, mellinDisConvergent_iff_integrableOn_rpow_mul,
    Complex.ofReal_re]

/-!
## The domain of convergence is a right half-plane
-/

/-- Convergence propagates to larger real parts. -/
theorem MellinDisConvergent.of_re_le_re {N M : ℂ} (h : MellinDisConvergent f N)
    (hNM : N.re ≤ M.re) : MellinDisConvergent f M := by
  have hf := h.aestronglyMeasurable
  have hw : ContinuousOn (fun x : ℝ => x ^ (M.re - 1)) (Ioc 0 1) :=
    continuousOn_id.rpow_const fun x hx => Or.inl hx.1.ne'
  rw [mellinDisConvergent_iff_integrableOn_rpow_mul] at h ⊢
  refine Integrable.mono' h.norm ((hw.aestronglyMeasurable measurableSet_Ioc).mul hf) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hx.1 hx.2 (by linarith)) (norm_nonneg _)

/-- The real indices at which the Mellin transform on the unit interval converges form an upper
set. -/
theorem isUpperSet_setOf_mellinDisConvergent (f : ℝ → ℝ) :
    IsUpperSet {σ : ℝ | MellinDisConvergent f σ} := fun σ τ hστ hσ =>
  MellinDisConvergent.of_re_le_re hσ (by simpa using hστ)

/-!
## The bridge to Mathlib's Mellin transform
-/

/-- The Mellin transform on the unit interval is Mathlib's Mellin transform on the half-line of
the restriction of `f` to `(0, 1]`, extended by zero. -/
theorem mellinDis_eq_mellin_indicator (f : ℝ → ℝ) (N : ℂ) :
    mellinDis f N = mellin ((Ioc 0 1).indicator fun x => (f x : ℂ)) N := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self, mellinDis]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [indicator_of_mem hx, smul_eq_mul]
  · intro x hx
    rw [indicator_of_notMem hx.2, smul_zero]

/-- The Mellin transform on the unit interval converges at `N` exactly when Mathlib's Mellin
transform of the extension of `f` by zero converges at `N`. -/
theorem mellinDisConvergent_iff_mellinConvergent_indicator {N : ℂ} :
    MellinDisConvergent f N ↔ MellinConvergent ((Ioc 0 1).indicator fun x => (f x : ℂ)) N := by
  rw [mellinDisConvergent_def, integrableOn_congr_fun (fun x hx => ?_) measurableSet_Ioc]
  · refine ⟨fun h => h.of_forall_sdiff_eq_zero measurableSet_Ioi fun x hx => ?_,
      fun h => h.mono_set Ioc_subset_Ioi_self⟩
    rw [indicator_of_notMem hx.2, smul_zero]
  · rw [indicator_of_mem hx, smul_eq_mul]

/-- For a function vanishing on `(1, ∞)`, in particular for a density supported in `[0, 1]`, the
Mellin transform on the unit interval is Mathlib's Mellin transform on the half-line. -/
theorem mellinDis_eq_mellin (hf : Function.support f ⊆ Iic 1) (N : ℂ) :
    mellinDis f N = mellin (fun x => (f x : ℂ)) N := by
  rw [mellinDis_eq_mellin_indicator, mellin, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [indicator_of_mem (mem_Ioc.mpr ⟨hx, hx1⟩)]
  · rw [indicator_of_notMem fun h => hx1.not_ge h.2,
      Function.notMem_support.mp fun h => hx1.not_ge (hf h), Complex.ofReal_zero]

/-!
## The extension by zero
-/

/-- The extension by zero of a function locally integrable on `(0, 1]` is locally integrable on
the half-line. -/
theorem locallyIntegrableOn_Ioi_indicator_Ioc (hf : LocallyIntegrableOn f (Ioc 0 1)) :
    LocallyIntegrableOn ((Ioc 0 1).indicator fun x => (f x : ℂ)) (Ioi 0) := by
  -- A compact `k ⊆ (0, ∞)` meets `(0, 1]` inside the compact interval `[inf k, 1] ⊆ (0, 1]`, on
  -- which `f` is integrable.
  rw [locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro k hk hkc
  rcases k.eq_empty_or_nonempty with rfl | hne
  · exact integrableOn_empty
  have hpos : 0 < sInf k := hk (hkc.sInf_mem hne)
  have hIcc : IntegrableOn f (Icc (sInf k) 1) :=
    hf.integrableOn_compact_subset (fun x hx => ⟨hpos.trans_le hx.1, hx.2⟩) isCompact_Icc
  rw [IntegrableOn, integrable_indicator_iff measurableSet_Ioc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Ioc]
  exact (hIcc.mono_set fun x hx => ⟨csInf_le hkc.bddBelow hx.2, hx.1.2⟩).ofReal

/-- The extension by zero of a function from `(a, b]` vanishes near `+∞`. -/
theorem indicator_Ioc_eventuallyEq_zero_atTop {E : Type*} [Zero E] (a b : ℝ) (g : ℝ → E) :
    (Ioc a b).indicator g =ᶠ[atTop] 0 := by
  filter_upwards [eventually_gt_atTop b] with x hx
  exact indicator_of_notMem (fun h => hx.not_ge h.2) g

/-- The extension by zero of a function from `(a, b]` agrees with it to the right of `a`. -/
theorem indicator_Ioc_eventuallyEq_nhdsGT {E : Type*} [Zero E] {a b : ℝ} (hab : a < b)
    (g : ℝ → E) : (Ioc a b).indicator g =ᶠ[𝓝[>] a] g := by
  filter_upwards [Ioo_mem_nhdsGT hab] with x hx
  exact indicator_of_mem (Ioo_subset_Ioc_self hx) g

/-!
## Convergence and holomorphy from the small-`x` behaviour
-/

/-- **Convergence from the small-`x` bound.** If `f` is locally integrable on `(0, 1]` and
`f x = O(x ^ (-b))` as `x → 0⁺`, the Mellin transform on the unit interval converges on the
half-plane `b < Re N`. For a density behaving like `x ^ (-1 - λ)` at small `x` this is the
half-plane `1 + λ < Re N`. -/
theorem mellinDisConvergent_of_isBigO_rpow (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ} (hN : b < N.re) :
    MellinDisConvergent f N :=
  mellinDisConvergent_iff_mellinConvergent_indicator.mpr <|
    mellinConvergent_of_isBigO_rpow (a := N.re + 1) (locallyIntegrableOn_Ioi_indicator_Ioc hf)
      ((indicator_Ioc_eventuallyEq_zero_atTop 0 1 _).trans_isBigO (isBigO_zero _ _))
      (lt_add_one _)
      ((indicator_Ioc_eventuallyEq_nhdsGT one_pos _).trans_isBigO
        (Complex.isBigO_ofReal_left.mpr hb)) hN

/-- **Holomorphy from the small-`x` bound.** Under the hypotheses of
`mellinDisConvergent_of_isBigO_rpow`, `mellinDis f` is complex differentiable at every `N` with
`b < Re N`. -/
theorem differentiableAt_mellinDis (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ} (hN : b < N.re) :
    DifferentiableAt ℂ (mellinDis f) N := by
  rw [show mellinDis f = _ from funext (mellinDis_eq_mellin_indicator f)]
  exact mellin_differentiableAt_of_isBigO_rpow (a := N.re + 1)
    (locallyIntegrableOn_Ioi_indicator_Ioc hf)
    ((indicator_Ioc_eventuallyEq_zero_atTop 0 1 _).trans_isBigO (isBigO_zero _ _))
    (lt_add_one _)
    ((indicator_Ioc_eventuallyEq_nhdsGT one_pos _).trans_isBigO
      (Complex.isBigO_ofReal_left.mpr hb)) hN

/-- Holomorphy on the half-plane: `mellinDis f` is differentiable on `{N | b < N.re}`. -/
theorem differentiableOn_mellinDis (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) :
    DifferentiableOn ℂ (mellinDis f) {N | b < N.re} := fun _ hN =>
  (differentiableAt_mellinDis hf hb hN).differentiableWithinAt

/-- The function `x ^ (-b)` has a convergent Mellin transform on `(0, 1]` exactly when
`b < Re N`. So for the bound `f x = O(x ^ (-b))` the half-plane of
`mellinDisConvergent_of_isBigO_rpow` cannot be enlarged. -/
@[simp]
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
