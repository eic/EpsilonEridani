/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Factorization.Convolution.Mellin
public import EpsilonEridani.Mathematics.HalfLine
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# The half-plane of convergence of the Mellin transform on the unit interval

A collinear density is a real function `f` of the momentum fraction, supported in `[0, 1]` and
locally integrable on the momentum-fraction interval. Its Mellin transform
`mellinDis f N = ∫_{(0,1]} x ^ (N - 1) * f x dx` converges at `N` exactly when `f` lies in the
weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`. This file studies the set of such `N`.

On `(0, 1]` the weight `x ^ (σ - 1)` decreases as `σ` grows, so convergence at `σ₀` implies
convergence at every `σ ≥ σ₀`: the domain of convergence is a right half-plane, the form the usual
strip of convergence takes on the unit interval. Its position is controlled by the behaviour of `f`
as `x → 0`: if `f x = O(x ^ (-b))` there, the transform converges and is holomorphic for
`b < Re N`. A density behaving like `x ^ (-1 - λ)` at small `x` thus has its moments from
`Re N > 1 + λ` on. For the bound itself this half-plane is maximal: `x ^ (-b)` has a convergent
transform exactly for `b < Re N`.

Convergence and holomorphy are obtained from Mathlib's `mellin`, the transform on the half-line,
through the extension of `f` by zero, `Set.indicator (Set.Ioc 0 1) fun x => (f x : ℂ)`: the two
transforms agree, and converge at the same indices. For a density supported in `[0, 1]` this reads
`mellinDis f = mellin f`. The transforms of powers come from the `MellinIoc` section of
`Mathlib/Analysis/MellinTransform.lean`, which treats functions on `(0, 1]`.

## Main results

* `mellinDisConvergent_iff_integrableOn_rpow_mul`: convergence at `N` is membership of `f` in the
  weighted space `L¹((0, 1], x ^ (Re N - 1) dx)`; `mellinDisConvergent_iff_re`: it depends only
  on `Re N`.
* `MellinDisConvergent.of_re_le_re`, `isUpperSet_setOf_mellinDisConvergent`,
  `ordConnected_setOf_mellinDisConvergent`: convergence propagates to larger real parts, so the
  real points of convergence form an upper set, in particular an interval.
* `mellinDis_eq_mellin_indicator`, `mellinDisConvergent_iff_mellinConvergent_indicator`: the bridge
  to Mathlib's `mellin`, for values and for convergence; `mellinDis_eq_mellin_of_support_subset`
  for a density supported in `[0, 1]`.
* `mellinDisConvergent_of_isBigO_rpow`, `mellinDis_differentiableAt_of_isBigO_rpow`,
  `mellinDis_differentiableOn_of_isBigO_rpow`: if `f` is locally integrable on `(0, 1]` and
  `f x = O(x ^ (-b))` as `x → 0⁺`, the transform converges and is holomorphic on `b < Re N`.
* `mellinDis_rpow`, `mellinDisConvergent_rpow_iff`: `x ^ a` has the transform `1 / (N + a)`, and
  converges exactly on `0 < Re N + a`; with `a = -b` this shows the half-plane above is maximal.

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
  -- On `(0, 1]` the integrand of `mellinDis` is that of `mellin` for the extension by zero.
  have h₁ : MellinDisConvergent f N ↔ IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (N - 1) • (Ioc 0 1).indicator (fun x => (f x : ℂ)) x) (Ioc 0 1) :=
    mellinDisConvergent_def.trans <| integrableOn_congr_fun
      (fun x hx => by rw [indicator_of_mem hx, smul_eq_mul]) measurableSet_Ioc
  have h₂ : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (N - 1) • (Ioc 0 1).indicator (fun x => (f x : ℂ)) x) (Ioc 0 1) ↔
      IntegrableOn (fun x : ℝ => x ^ (N.re - 1) * ‖(Ioc 0 1).indicator (fun x => (f x : ℂ)) x‖)
        (Ioc 0 1) :=
    mellin_convergent_iff_norm Ioc_subset_Ioi_self measurableSet_Ioc hg
  have h₃ : IntegrableOn
      (fun x : ℝ => x ^ (N.re - 1) * ‖(Ioc 0 1).indicator (fun x => (f x : ℂ)) x‖) (Ioc 0 1) ↔
      IntegrableOn (fun x => ‖x ^ (N.re - 1) * f x‖) (Ioc 0 1) :=
    integrableOn_congr_fun (fun x hx => by
      rw [indicator_of_mem hx, Complex.norm_real, norm_mul,
        Real.norm_of_nonneg (Real.rpow_pos_of_pos hx.1 _).le]) measurableSet_Ioc
  have h₄ : IntegrableOn (fun x => ‖x ^ (N.re - 1) * f x‖) (Ioc 0 1) ↔
      IntegrableOn (fun x => x ^ (N.re - 1) * f x) (Ioc 0 1) :=
    integrable_norm_iff <|
      ((continuousOn_id.rpow_const fun _ hx => Or.inl hx.1.ne').aestronglyMeasurable
        measurableSet_Ioc).mul hf
  exact h₁.trans (h₂.trans (h₃.trans h₄))

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
  rw [mellinDisConvergent_iff_integrableOn_rpow_mul] at h ⊢
  refine Integrable.mono' h.norm
    (((continuousOn_id.rpow_const fun _ hx => Or.inl hx.1.ne').aestronglyMeasurable
      measurableSet_Ioc).mul hf) ?_
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

/-- The real indices at which the Mellin transform on the unit interval converges form an
interval. -/
theorem ordConnected_setOf_mellinDisConvergent (f : ℝ → ℝ) :
    {σ : ℝ | MellinDisConvergent f σ}.OrdConnected :=
  (isUpperSet_setOf_mellinDisConvergent f).ordConnected

/-!
## The bridge to Mathlib's Mellin transform
-/

/-- The Mellin transform on the unit interval is Mathlib's Mellin transform on the half-line of
the restriction of `f` to `(0, 1]`, extended by zero. -/
theorem mellinDis_eq_mellin_indicator (f : ℝ → ℝ) (N : ℂ) :
    mellinDis f N = mellin ((Ioc 0 1).indicator fun x => (f x : ℂ)) N := by
  rw [mellin, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self, mellinDis_def]
  · refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    rw [indicator_of_mem hx, smul_eq_mul]
  · intro x hx
    rw [indicator_of_notMem hx.2, smul_zero]

/-- The Mellin transform on the unit interval converges at `N` exactly when Mathlib's Mellin
transform of the extension of `f` by zero converges at `N`. -/
theorem mellinDisConvergent_iff_mellinConvergent_indicator {N : ℂ} :
    MellinDisConvergent f N ↔ MellinConvergent ((Ioc 0 1).indicator fun x => (f x : ℂ)) N := by
  rw [mellinDisConvergent_def, integrableOn_congr_fun
    (g := fun x : ℝ => (x : ℂ) ^ (N - 1) • (Ioc 0 1).indicator (fun x => (f x : ℂ)) x)
    (fun x hx => by dsimp only; rw [indicator_of_mem hx, smul_eq_mul]) measurableSet_Ioc]
  refine ⟨fun h => h.of_forall_sdiff_eq_zero measurableSet_Ioi fun x hx => ?_,
    fun h => h.mono_set Ioc_subset_Ioi_self⟩
  rw [indicator_of_notMem hx.2, smul_zero]

/-- For a function vanishing on `(1, ∞)`, in particular for a density supported in `[0, 1]`, the
Mellin transform on the unit interval is Mathlib's Mellin transform on the half-line. -/
theorem mellinDis_eq_mellin_of_support_subset (hf : Function.support f ⊆ Iic 1) (N : ℂ) :
    mellinDis f N = mellin (fun x => (f x : ℂ)) N := by
  rw [mellinDis_eq_mellin_indicator, mellin, mellin]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  rcases le_or_gt x 1 with hx1 | hx1
  · rw [indicator_of_mem (mem_Ioc.mpr ⟨hx, hx1⟩)]
  · rw [indicator_of_notMem fun h => hx1.not_ge h.2,
      Function.notMem_support.mp fun h => hx1.not_ge (hf h), Complex.ofReal_zero]

/-!
## Convergence and holomorphy from the small-`x` behaviour
-/

/-- The extension by zero of `f` meets the hypotheses of Mathlib's
`mellinConvergent_of_isBigO_rpow` and `mellin_differentiableAt_of_isBigO_rpow`, for any exponent
`a` at `+∞`. -/
private theorem indicator_isBigO_rpow_hyps (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) (a : ℝ) :
    LocallyIntegrableOn ((Ioc 0 1).indicator fun x => (f x : ℂ)) (Ioi 0) ∧
      (Ioc 0 1).indicator (fun x => (f x : ℂ)) =O[atTop] (· ^ (-a)) ∧
      (Ioc 0 1).indicator (fun x => (f x : ℂ)) =O[𝓝[>] 0] (· ^ (-b)) :=
  ⟨locallyIntegrableOn_Ioi_indicator_Ioc (Complex.ofRealCLM.locallyIntegrableOn_comp hf),
    (indicator_Ioc_eventuallyEq_zero_atTop 0 1 _).trans_isBigO (isBigO_zero _ _),
    (indicator_Ioc_eventuallyEq_nhdsGT one_pos _).trans_isBigO
      (Complex.isBigO_ofReal_left.mpr hb)⟩

/-- **Convergence from the small-`x` bound.** If `f` is locally integrable on `(0, 1]` and
`f x = O(x ^ (-b))` as `x → 0⁺`, the Mellin transform on the unit interval converges on the
half-plane `b < Re N`. For a density behaving like `x ^ (-1 - λ)` at small `x` this is the
half-plane `1 + λ < Re N`. -/
theorem mellinDisConvergent_of_isBigO_rpow (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ} (hN : b < N.re) :
    MellinDisConvergent f N :=
  have ⟨hloc, htop, hbot⟩ := indicator_isBigO_rpow_hyps hf hb (N.re + 1)
  mellinDisConvergent_iff_mellinConvergent_indicator.mpr <|
    mellinConvergent_of_isBigO_rpow hloc htop (lt_add_one _) hbot hN

/-- **Holomorphy from the small-`x` bound.** Under the hypotheses of
`mellinDisConvergent_of_isBigO_rpow`, `mellinDis f` is complex differentiable at every `N` with
`b < Re N`. -/
theorem mellinDis_differentiableAt_of_isBigO_rpow (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) {N : ℂ} (hN : b < N.re) :
    DifferentiableAt ℂ (mellinDis f) N := by
  have ⟨hloc, htop, hbot⟩ := indicator_isBigO_rpow_hyps hf hb (N.re + 1)
  rw [funext (mellinDis_eq_mellin_indicator f)]
  exact mellin_differentiableAt_of_isBigO_rpow hloc htop (lt_add_one _) hbot hN

/-- Holomorphy on the half-plane: `mellinDis f` is differentiable on `{N | b < N.re}`. -/
theorem mellinDis_differentiableOn_of_isBigO_rpow (hf : LocallyIntegrableOn f (Ioc 0 1)) {b : ℝ}
    (hb : f =O[𝓝[>] 0] fun x => x ^ (-b)) :
    DifferentiableOn ℂ (mellinDis f) {N | b < N.re} := fun _ hN =>
  (mellinDis_differentiableAt_of_isBigO_rpow hf hb hN).differentiableWithinAt

/-!
## Powers
-/

/-- The extension by zero of the real power `x ^ a` from `(0, 1]` is the complex one of Mathlib's
`hasMellin_cpow_Ioc`. -/
private theorem indicator_rpow_eq_indicator_cpow (a : ℝ) :
    ((Ioc 0 1).indicator fun x : ℝ => ((x ^ a : ℝ) : ℂ)) =
      (Ioc 0 1).indicator fun x : ℝ => (x : ℂ) ^ (a : ℂ) :=
  indicator_congr fun _ hx => Complex.ofReal_cpow hx.1.le a

/-- The Mellin transform of `x ^ a` on the unit interval is `1 / (N + a)` for `0 < Re N + a`;
this is Mathlib's `hasMellin_cpow_Ioc`. -/
theorem mellinDis_rpow {a : ℝ} {N : ℂ} (hN : 0 < N.re + a) :
    mellinDis (fun x => x ^ a) N = 1 / (N + a) := by
  rw [mellinDis_eq_mellin_indicator, indicator_rpow_eq_indicator_cpow]
  exact (hasMellin_cpow_Ioc a (by simpa using hN)).2

/-- The function `x ^ a` has a convergent Mellin transform on `(0, 1]` exactly when
`0 < Re N + a`. With `a = -b`, this shows that for the bound `f x = O(x ^ (-b))` the half-plane of
`mellinDisConvergent_of_isBigO_rpow` cannot be enlarged. -/
@[simp]
theorem mellinDisConvergent_rpow_iff {a : ℝ} {N : ℂ} :
    MellinDisConvergent (fun x => x ^ a) N ↔ 0 < N.re + a := by
  refine ⟨fun h => ?_, fun hN => ?_⟩
  · -- Necessity: `x ^ (Re N - 1 + a)` is integrable near `0` only for `-1 < Re N - 1 + a`.
    rw [mellinDisConvergent_iff_integrableOn_rpow_mul, integrableOn_Ioc_iff_integrableOn_Ioo,
      integrableOn_congr_fun (g := fun x => x ^ (N.re - 1 + a)) (fun x hx => by
        dsimp only; rw [← Real.rpow_add hx.1]) measurableSet_Ioo,
      intervalIntegral.integrableOn_Ioo_rpow_iff one_pos] at h
    linarith
  · -- Sufficiency: Mathlib's `hasMellin_cpow_Ioc`.
    rw [mellinDisConvergent_iff_mellinConvergent_indicator, indicator_rpow_eq_indicator_cpow]
    exact (hasMellin_cpow_Ioc a (by simpa using hN)).1

end Convolution
end Factorization
end QFT
end EpsilonEridani
