/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.TailIntegral
public import EpsilonEridani.QFT.Factorization.Convolution.Mellin

/-!

# The Mellin convolution on the momentum-fraction interval

This module defines the Mellin convolution of two densities on the momentum-fraction interval,
```
(f ⊗ g) (x) = ∫_x^1 (dy / y) f y * g (x / y),   0 < x ≤ 1,
```
extended by zero outside `(0,1]`, as a binary operation `mellinConv` on functions `ℝ → ℝ`. It
proves support, commutativity, bilinearity and positivity of that operation, the absence of a
unit, and the transfer of the Mellin convolution theorem. Only additivity needs an
integrability hypothesis.

`mellinConv f g` is the collinear convolution `convolveAt (collinearKernel g) f` of
`EpsilonEridani.QFT.Factorization.Convolution.Collinear`, truncated to `(0,1]` by
`Set.indicator` (`mellinConv_apply_eq_convolveAt_of_mem`). The truncation is what makes it a
binary operation on densities supported in the unit interval: the untruncated
`convolveAt (collinearKernel g) f x` need not vanish for `x ≤ 0`. Only the values of `f` and `g`
on `(0,1]` enter `mellinConv f g`, so no support hypothesis is needed in any statement below.

The value at `x = 0` is set to zero rather than to the integral: at `x = 0` the integrand is
`f y * g 0 / y`, which is not symmetric in `f` and `g`, and commutativity would fail there.

## Main results

- `mellinConv_apply_of_mem`: the defining integral on `(0,1]`.
- `support_mellinConv_subset`: the convolution is supported in `(0,1]`.
- `mellinConv_comm`: commutativity, with no hypothesis on `f` or `g`.
- `mellinConv_smul_left`, `mellinConv_neg_left`, `mellinConv_add_left_apply`,
  `mellinConv_sub_left_apply` and their right-hand versions: bilinearity, additivity requiring
  integrability at the point.
- `mellinConv_apply_nonneg`: the convolution of non-negative densities is non-negative.
- `not_mellinConv_indicator_one_ae_eq` and `not_exists_forall_mellinConv_ae_eq`: no function is
  a unit for `mellinConv`, even almost everywhere on `(0,1]` and even against the single density
  `1` on `(0,1]`. The unit of the convolution is the distribution `δ(1 - x)`, which is not a
  function.
- `mellinDis_mellinConv`: the Mellin transform of `mellinConv f g` is the product of the
  transforms, transferred from `mellinDis_convolveAt`.

## Implementation notes

Mathlib's `MeasureTheory.mlconvolution` is a convolution on a multiplicative group for
`ℝ≥0∞`-valued functions; it does not cover real-valued densities on the bounded interval, whose
convolution is not a group convolution because `(0,1]` is only a monoid.

## References

- F. J. Yndurain, *The Theory of Quark and Gluon Interactions*, 4th ed., Springer (2006), ch. 4.

-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Convolution

/-- The Mellin convolution on the momentum-fraction interval,
`mellinConv f g x = ∫_x^1 (dy / y) f y * g (x / y)` for `x ∈ (0,1]` and `0` otherwise. It is the
collinear convolution `convolveAt (collinearKernel g) f` truncated to `(0,1]`; use
`mellinConv_apply_of_mem` for the integral and `mellinConv_apply_eq_zero_of_notMem` outside
`(0,1]`. -/
def mellinConv (f g : ℝ → ℝ) : ℝ → ℝ :=
  (Ioc (0 : ℝ) 1).indicator (convolveAt (collinearKernel g) f)

/-- Outside `(0,1]` the Mellin convolution vanishes. -/
theorem mellinConv_apply_eq_zero_of_notMem (f g : ℝ → ℝ) {x : ℝ} (hx : x ∉ Ioc (0 : ℝ) 1) :
    mellinConv f g x = 0 :=
  indicator_of_notMem hx _

/-- On `(0,1]` the Mellin convolution is the collinear convolution of `f` against the kernel of
`g`. -/
theorem mellinConv_apply_eq_convolveAt_of_mem (f g : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    mellinConv f g x = convolveAt (collinearKernel g) f x :=
  indicator_of_mem hx _

/-- The Mellin convolution is supported in `(0,1]`. -/
theorem support_mellinConv_subset (f g : ℝ → ℝ) :
    Function.support (mellinConv f g) ⊆ Ioc (0 : ℝ) 1 :=
  support_indicator_subset

/-- The defining integral of the Mellin convolution on `(0,1]`:
`mellinConv f g x = ∫_{[x,1]} f y * g (x / y) / y dy`. -/
theorem mellinConv_apply_of_mem (f g : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    mellinConv f g x = ∫ y in Icc x 1, f y * g (x / y) / y := by
  have hsub : Icc x 1 = Icc 0 1 ∩ Icc x 1 :=
    (inter_eq_right.mpr (Icc_subset_Icc_left hx.1.le)).symm
  rw [mellinConv_apply_eq_convolveAt_of_mem f g hx, convolveAt, hsub,
    ← setIntegral_indicator measurableSet_Icc]
  refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
  by_cases hxz : x ≤ z
  · rw [indicator_of_mem (mem_Icc.mpr ⟨hxz, hz.2⟩), integrand,
      collinearKernel_of_mem g (hx.1.trans_le hxz) hxz]
    ring
  · simp only [indicator_of_notMem fun h : z ∈ Icc x 1 => hxz h.1, integrand,
      collinearKernel_of_lt g (not_le.mp hxz), zero_mul]

/-- **Commutativity** of the Mellin convolution. No integrability hypothesis is needed. -/
theorem mellinConv_comm (f g : ℝ → ℝ) : mellinConv f g = mellinConv g f := by
  ext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [mellinConv_apply_of_mem f g hx, mellinConv_apply_of_mem g f hx,
      ← setIntegral_Icc_comp_div_div (fun u => g u * f (x / u)) hx.1]
    refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
    rw [div_div_cancel₀ hx.1.ne', mul_comm]
  · simp only [mellinConv_apply_eq_zero_of_notMem _ _ hx]

/-- The Mellin convolution with the zero density on the left vanishes. -/
@[simp]
theorem mellinConv_zero_left (g : ℝ → ℝ) : mellinConv 0 g = 0 := by
  ext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp [mellinConv_apply_of_mem 0 g hx]
  · simp [mellinConv_apply_eq_zero_of_notMem 0 g hx]

/-- The Mellin convolution with the zero density on the right vanishes. -/
@[simp]
theorem mellinConv_zero_right (f : ℝ → ℝ) : mellinConv f 0 = 0 := by
  rw [mellinConv_comm, mellinConv_zero_left]

/-- The Mellin convolution is homogeneous in its left argument. No integrability hypothesis is
needed. -/
@[simp]
theorem mellinConv_smul_left (c : ℝ) (f g : ℝ → ℝ) :
    mellinConv (c • f) g = c • mellinConv f g := by
  ext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [Pi.smul_apply, mellinConv_apply_of_mem _ _ hx, smul_eq_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    ring
  · simp [mellinConv_apply_eq_zero_of_notMem _ _ hx]

/-- The Mellin convolution is homogeneous in its right argument. -/
@[simp]
theorem mellinConv_smul_right (c : ℝ) (f g : ℝ → ℝ) :
    mellinConv f (c • g) = c • mellinConv f g := by
  rw [mellinConv_comm, mellinConv_smul_left, mellinConv_comm]

/-- The Mellin convolution commutes with negation of its left argument. -/
@[simp]
theorem mellinConv_neg_left (f g : ℝ → ℝ) : mellinConv (-f) g = -mellinConv f g := by
  simpa using mellinConv_smul_left (-1) f g

/-- The Mellin convolution commutes with negation of its right argument. -/
@[simp]
theorem mellinConv_neg_right (f g : ℝ → ℝ) : mellinConv f (-g) = -mellinConv f g := by
  rw [mellinConv_comm, mellinConv_neg_left, mellinConv_comm]

/-- The Mellin convolution is additive in its left argument at a point `x`, provided both
convolution integrands are integrable when `x ∈ (0,1]`. -/
theorem mellinConv_add_left_apply {f₁ f₂ g : ℝ → ℝ} {x : ℝ}
    (h₁ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f₁ y * g (x / y) / y) (Icc x 1))
    (h₂ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f₂ y * g (x / y) / y) (Icc x 1)) :
    mellinConv (f₁ + f₂) g x = mellinConv f₁ g x + mellinConv f₂ g x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [mellinConv_apply_of_mem _ _ hx, ← integral_add (h₁ hx) (h₂ hx)]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [Pi.add_apply]
    ring
  · simp only [mellinConv_apply_eq_zero_of_notMem _ _ hx, add_zero]

/-- The Mellin convolution is additive in its right argument at a point `x`, provided both
convolution integrands are integrable when `x ∈ (0,1]`. -/
theorem mellinConv_add_right_apply {f g₁ g₂ : ℝ → ℝ} {x : ℝ}
    (h₁ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f y * g₁ (x / y) / y) (Icc x 1))
    (h₂ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f y * g₂ (x / y) / y) (Icc x 1)) :
    mellinConv f (g₁ + g₂) x = mellinConv f g₁ x + mellinConv f g₂ x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [mellinConv_apply_of_mem _ _ hx, ← integral_add (h₁ hx) (h₂ hx)]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [Pi.add_apply]
    ring
  · simp only [mellinConv_apply_eq_zero_of_notMem _ _ hx, add_zero]

/-- The Mellin convolution is subtractive in its left argument at a point `x`, provided both
convolution integrands are integrable when `x ∈ (0,1]`. -/
theorem mellinConv_sub_left_apply {f₁ f₂ g : ℝ → ℝ} {x : ℝ}
    (h₁ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f₁ y * g (x / y) / y) (Icc x 1))
    (h₂ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f₂ y * g (x / y) / y) (Icc x 1)) :
    mellinConv (f₁ - f₂) g x = mellinConv f₁ g x - mellinConv f₂ g x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [mellinConv_apply_of_mem _ _ hx, ← integral_sub (h₁ hx) (h₂ hx)]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [Pi.sub_apply]
    ring
  · simp only [mellinConv_apply_eq_zero_of_notMem _ _ hx, sub_zero]

/-- The Mellin convolution is subtractive in its right argument at a point `x`, provided both
convolution integrands are integrable when `x ∈ (0,1]`. -/
theorem mellinConv_sub_right_apply {f g₁ g₂ : ℝ → ℝ} {x : ℝ}
    (h₁ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f y * g₁ (x / y) / y) (Icc x 1))
    (h₂ : x ∈ Ioc (0 : ℝ) 1 → IntegrableOn (fun y => f y * g₂ (x / y) / y) (Icc x 1)) :
    mellinConv f (g₁ - g₂) x = mellinConv f g₁ x - mellinConv f g₂ x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp only [mellinConv_apply_of_mem _ _ hx, ← integral_sub (h₁ hx) (h₂ hx)]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [Pi.sub_apply]
    ring
  · simp only [mellinConv_apply_eq_zero_of_notMem _ _ hx, sub_zero]

/-- **Positivity.** The Mellin convolution of two densities that are non-negative on `(0,1]` is
non-negative. This is what carries a positivity constraint through a factorization formula. -/
theorem mellinConv_apply_nonneg {f g : ℝ → ℝ} (hf : ∀ y ∈ Ioc (0 : ℝ) 1, 0 ≤ f y)
    (hg : ∀ y ∈ Ioc (0 : ℝ) 1, 0 ≤ g y) (x : ℝ) : 0 ≤ mellinConv f g x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [mellinConv_apply_of_mem f g hx]
    refine setIntegral_nonneg measurableSet_Icc fun y hy => ?_
    have hy0 : 0 < y := hx.1.trans_le hy.1
    exact div_nonneg (mul_nonneg (hf y ⟨hy0, hy.2⟩)
      (hg _ (div_mem_Ioc_of_pos_of_le hx.1 hy.1))) hy0.le
  · rw [mellinConv_apply_eq_zero_of_notMem f g hx]

/-- Against the constant density `1` on `(0,1]`, the Mellin convolution is the tail integral
`∫_x^1 e y / y dy`. -/
theorem mellinConv_indicator_one_apply_of_mem (e : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    mellinConv e ((Ioc (0 : ℝ) 1).indicator 1) x = ∫ y in Icc x 1, e y / y := by
  rw [mellinConv_apply_of_mem _ _ hx]
  refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
  simp only [indicator_of_mem (div_mem_Ioc_of_pos_of_le hx.1 hy.1), Pi.one_apply, mul_one]

/-- **No function is a unit for the Mellin convolution**, not even almost everywhere on `(0,1]`
and not even against the single density `1` on `(0,1]`: for every `e : ℝ → ℝ`,
`e ⊗ 1_{(0,1]}` differs from `1_{(0,1]}` on a set of positive measure in `(0,1]`. The unit of the
convolution is the distribution `δ(1 - x)`, which is not a function. -/
theorem not_mellinConv_indicator_one_ae_eq (e : ℝ → ℝ) :
    ¬ mellinConv e ((Ioc (0 : ℝ) 1).indicator 1)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (Ioc (0 : ℝ) 1).indicator 1 := by
  intro hae
  rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hae
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp
    ((tendsto_setIntegral_Icc_nhdsLT (fun y => e y / y) 1).eventually_ne zero_ne_one)
  have hab : max l 0 < 1 := max_lt hl one_pos
  refine (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hab)).ne'
    (measure_mono_null (fun x hx => ?_) (ae_iff.mp hae))
  have hx01 : x ∈ Ioc (0 : ℝ) 1 := ⟨(le_max_right _ _).trans_lt hx.1, hx.2.le⟩
  simp only [mem_ofPred_eq, not_imp]
  refine ⟨hx01, fun hx' => hsub ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩ ?_⟩
  rw [← mellinConv_indicator_one_apply_of_mem e hx01, hx', indicator_of_mem hx01, Pi.one_apply]

/-- The integrable densities supported in `[0,1]` have no unit for the Mellin convolution, even
up to equality almost everywhere on `(0,1]`. -/
theorem not_exists_forall_mellinConv_ae_eq :
    ¬ ∃ e : ℝ → ℝ, ∀ f : ℝ → ℝ, Integrable f → Function.support f ⊆ Icc 0 1 →
      mellinConv e f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f := fun ⟨e, he⟩ =>
  not_mellinConv_indicator_one_ae_eq e <| he _
    ((integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc)
    ((support_indicator_subset).trans Ioc_subset_Icc_self)

/-- The Mellin transform of a Mellin convolution: `M[f ⊗ g] (N) = M[f] (N) * M[g] (N)` under the
hypotheses of the convolution theorem. -/
theorem mellinDis_mellinConv (f g : ℝ → ℝ) (N : ℂ) (h : MellinConvolutionAssumptions f g N) :
    mellinDis (mellinConv f g) N = mellinDis f N * mellinDis g N := by
  have hcongr : mellinDis (mellinConv g f) N = mellinDis (convolveAt (collinearKernel f) g) N :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx => by
      rw [mellinConv_apply_eq_convolveAt_of_mem g f hx]
  rw [mellinConv_comm, hcongr, mellinDis_convolveAt f g N h]

end Convolution
end Factorization
end QFT
end EpsilonEridani
