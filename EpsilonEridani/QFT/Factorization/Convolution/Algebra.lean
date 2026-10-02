/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

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
`EpsilonEridani.QFT.Factorization.Convolution.Collinear`, truncated to `(0,1]`
(`mellinConv_eq_convolveAt`). The truncation is what makes it a binary operation on densities
supported in the unit interval: the untruncated `convolveAt (collinearKernel g) f x` need not
vanish for `x ≤ 0`. Only the values of `f` and `g` on `(0,1]` enter `mellinConv f g`, so no
support hypothesis is needed in any statement below.

The value at `x = 0` is set to zero rather than to the integral: at `x = 0` the integrand is
`f y * g 0 / y`, which is not symmetric in `f` and `g`, and commutativity would fail there.

## Main results

- `mellinConv_of_mem`: the defining integral on `(0,1]`.
- `support_mellinConv_subset`: the convolution is supported in `(0,1]`.
- `mellinConv_comm`: commutativity, by the substitution `y ↦ x / y`. No hypothesis is needed:
  the substitution is a bijection of `[x,1]`, so it relates the two Bochner integrals whether or
  not they converge.
- `mellinConv_smul_left`, `mellinConv_add_left` and their right-hand versions: bilinearity,
  additivity requiring integrability at the point.
- `mellinConv_nonneg`: the convolution of non-negative densities is non-negative.
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

public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Convolution

/-- The Mellin convolution on the momentum-fraction interval,
`mellinConv f g x = ∫_x^1 (dy / y) f y * g (x / y)` for `x ∈ (0,1]` and `0` otherwise. It is the
collinear convolution `convolveAt (collinearKernel g) f` truncated to `(0,1]`; use
`mellinConv_of_mem` for the integral and `mellinConv_of_notMem` outside `(0,1]`. -/
def mellinConv (f g : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ Ioc (0 : ℝ) 1 then convolveAt (collinearKernel g) f x else 0

/-- Outside `(0,1]` the Mellin convolution vanishes. -/
theorem mellinConv_of_notMem (f g : ℝ → ℝ) {x : ℝ} (hx : x ∉ Ioc (0 : ℝ) 1) :
    mellinConv f g x = 0 := by
  simp only [mellinConv, hx, ↓reduceIte]

/-- On `(0,1]` the Mellin convolution is the collinear convolution of `f` against the kernel of
`g`. -/
theorem mellinConv_eq_convolveAt (f g : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    mellinConv f g x = convolveAt (collinearKernel g) f x := by
  simp only [mellinConv, hx, ↓reduceIte]

/-- The Mellin convolution is supported in `(0,1]`. -/
theorem support_mellinConv_subset (f g : ℝ → ℝ) :
    Function.support (mellinConv f g) ⊆ Ioc (0 : ℝ) 1 :=
  Function.support_subset_iff'.mpr fun _ hx => mellinConv_of_notMem f g hx

/-- For `x ∈ (0,1]` and `y ∈ [x,1]`, the rescaled fraction `x / y` again lies in `(0,1]`. -/
private lemma div_mem_Ioc {x y : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hy : y ∈ Icc x 1) :
    x / y ∈ Ioc (0 : ℝ) 1 :=
  have hy0 : 0 < y := hx.1.trans_le hy.1
  ⟨div_pos hx.1 hy0, (div_le_one hy0).mpr hy.1⟩

/-- The defining integral of the Mellin convolution on `(0,1]`:
`mellinConv f g x = ∫_{[x,1]} f y * g (x / y) / y dy`. -/
theorem mellinConv_of_mem (f g : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    mellinConv f g x = ∫ y in Icc x 1, f y * g (x / y) / y := by
  have hsub : Icc x 1 = Icc 0 1 ∩ Icc x 1 :=
    (inter_eq_right.mpr (Icc_subset_Icc_left hx.1.le)).symm
  rw [mellinConv_eq_convolveAt f g hx, convolveAt, hsub,
    ← setIntegral_indicator measurableSet_Icc]
  refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
  by_cases hxz : x ≤ z
  · rw [indicator_of_mem (mem_Icc.mpr ⟨hxz, hz.2⟩), integrand,
      collinearKernel_of_mem g (hx.1.trans_le hxz) hxz]
    ring
  · rw [indicator_of_notMem fun h => hxz h.1, integrand,
      collinearKernel_of_lt g (not_le.mp hxz), zero_mul]

/-- The substitution `y ↦ x / y` maps `[x,1]` onto itself for `0 < x ≤ 1`, and exchanges the two
factors of the Mellin convolution integrand. -/
private lemma integral_Icc_comm (f g : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∫ y in Icc x 1, f y * g (x / y) / y = ∫ y in Icc x 1, g y * f (x / y) / y := by
  have hx0 := hx.1
  have himage : (fun u => x / u) '' Icc x 1 = Icc x 1 := by
    refine Subset.antisymm ?_ fun v hv => ?_
    · rintro _ ⟨u, hu, rfl⟩
      have := div_mem_Ioc hx hu
      exact ⟨(le_div_iff₀ (hx0.trans_le hu.1)).mpr (by nlinarith [hu.2]), this.2⟩
    · have hv0 : 0 < v := hx0.trans_le hv.1
      refine ⟨x / v, ⟨(le_div_iff₀ hv0).mpr (by nlinarith [hv.2]), (div_mem_Ioc hx hv).2⟩, ?_⟩
      exact div_div_cancel₀ hx0.ne'
  have hderiv : ∀ u ∈ Icc x 1,
      HasDerivWithinAt (fun u => x / u) (-x / u ^ 2) (Icc x 1) u := fun u hu => by
    have hu0 : u ≠ 0 := (hx0.trans_le hu.1).ne'
    convert ((hasDerivAt_inv hu0).const_mul x).hasDerivWithinAt using 1
    · funext y
      exact div_eq_mul_inv x y
    · ring
  have hinj : InjOn (fun u => x / u) (Icc x 1) := fun u _ v _ huv => by
    simpa [div_div_cancel₀ hx0.ne'] using congrArg (x / ·) huv
  rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj, himage]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  have hu0 : 0 < u := hx0.trans_le hu.1
  rw [smul_eq_mul, div_div_cancel₀ hx0.ne', neg_div, abs_neg, abs_of_pos (by positivity)]
  field_simp

/-- **Commutativity** of the Mellin convolution, by the substitution `y ↦ x / y`. No
integrability hypothesis is needed. -/
theorem mellinConv_comm (f g : ℝ → ℝ) : mellinConv f g = mellinConv g f := by
  ext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [mellinConv_of_mem f g hx, mellinConv_of_mem g f hx, integral_Icc_comm f g hx]
  · rw [mellinConv_of_notMem f g hx, mellinConv_of_notMem g f hx]

/-- The Mellin convolution with the zero density on the left vanishes. -/
@[simp]
theorem mellinConv_zero_left (g : ℝ → ℝ) : mellinConv 0 g = 0 := by
  ext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · simp [mellinConv_of_mem 0 g hx]
  · rw [mellinConv_of_notMem 0 g hx, Pi.zero_apply]

/-- The Mellin convolution with the zero density on the right vanishes. -/
@[simp]
theorem mellinConv_zero_right (f : ℝ → ℝ) : mellinConv f 0 = 0 := by
  rw [mellinConv_comm, mellinConv_zero_left]

/-- The Mellin convolution is homogeneous in its left argument. No integrability hypothesis is
needed. -/
theorem mellinConv_smul_left (c : ℝ) (f g : ℝ → ℝ) :
    mellinConv (c • f) g = c • mellinConv f g := by
  ext x
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [Pi.smul_apply, mellinConv_of_mem _ _ hx, mellinConv_of_mem _ _ hx, smul_eq_mul,
      ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [Pi.smul_apply, mellinConv_of_notMem _ _ hx, mellinConv_of_notMem _ _ hx, smul_zero]

/-- The Mellin convolution is homogeneous in its right argument. -/
theorem mellinConv_smul_right (c : ℝ) (f g : ℝ → ℝ) :
    mellinConv f (c • g) = c • mellinConv f g := by
  rw [mellinConv_comm, mellinConv_smul_left, mellinConv_comm]

/-- The Mellin convolution is additive in its left argument at a point `x` where both
convolution integrands are integrable. -/
theorem mellinConv_add_left {f₁ f₂ g : ℝ → ℝ} {x : ℝ}
    (h₁ : IntegrableOn (fun y => f₁ y * g (x / y) / y) (Icc x 1))
    (h₂ : IntegrableOn (fun y => f₂ y * g (x / y) / y) (Icc x 1)) :
    mellinConv (f₁ + f₂) g x = mellinConv f₁ g x + mellinConv f₂ g x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [mellinConv_of_mem _ _ hx, mellinConv_of_mem _ _ hx, mellinConv_of_mem _ _ hx,
      ← integral_add h₁ h₂]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [Pi.add_apply]
    ring
  · rw [mellinConv_of_notMem _ _ hx, mellinConv_of_notMem _ _ hx, mellinConv_of_notMem _ _ hx,
      add_zero]

/-- The Mellin convolution is additive in its right argument at a point `x` where both
convolution integrands are integrable. -/
theorem mellinConv_add_right {f g₁ g₂ : ℝ → ℝ} {x : ℝ}
    (h₁ : IntegrableOn (fun y => f y * g₁ (x / y) / y) (Icc x 1))
    (h₂ : IntegrableOn (fun y => f y * g₂ (x / y) / y) (Icc x 1)) :
    mellinConv f (g₁ + g₂) x = mellinConv f g₁ x + mellinConv f g₂ x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [mellinConv_of_mem _ _ hx, mellinConv_of_mem _ _ hx, mellinConv_of_mem _ _ hx,
      ← integral_add h₁ h₂]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [Pi.add_apply]
    ring
  · rw [mellinConv_of_notMem _ _ hx, mellinConv_of_notMem _ _ hx, mellinConv_of_notMem _ _ hx,
      add_zero]

/-- **Positivity.** The Mellin convolution of two densities that are non-negative on `(0,1]` is
non-negative. This is what carries a positivity constraint through a factorization formula. -/
theorem mellinConv_nonneg {f g : ℝ → ℝ} (hf : ∀ y ∈ Ioc (0 : ℝ) 1, 0 ≤ f y)
    (hg : ∀ y ∈ Ioc (0 : ℝ) 1, 0 ≤ g y) (x : ℝ) : 0 ≤ mellinConv f g x := by
  by_cases hx : x ∈ Ioc (0 : ℝ) 1
  · rw [mellinConv_of_mem f g hx]
    refine setIntegral_nonneg measurableSet_Icc fun y hy => ?_
    have hy0 : 0 < y := hx.1.trans_le hy.1
    exact div_nonneg (mul_nonneg (hf y ⟨hy0, hy.2⟩) (hg _ (div_mem_Ioc hx hy))) hy0.le
  · rw [mellinConv_of_notMem f g hx]

/-- Against the constant density `1` on `(0,1]`, the Mellin convolution is the tail integral
`∫_x^1 e y / y dy`. -/
theorem mellinConv_indicator_one_of_mem (e : ℝ → ℝ) {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    mellinConv e ((Ioc (0 : ℝ) 1).indicator 1) x = ∫ y in Icc x 1, e y / y := by
  rw [mellinConv_of_mem _ _ hx]
  refine setIntegral_congr_fun measurableSet_Icc fun y hy => ?_
  rw [indicator_of_mem (div_mem_Ioc hx hy), Pi.one_apply, mul_one]

/-- The tail integral `∫_x^1 h` differs from `1` on a non-empty open subinterval of `(0,1]`:
near `1` if `h` is integrable on `[1/2, 1]`, by continuity of the tail integral, and on
`(0, 1/2)` otherwise, where the tail integral diverges. -/
private lemma exists_Ioo_integral_Icc_ne_one (h : ℝ → ℝ) :
    ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ Ioc (0 : ℝ) 1 ∧ ∀ x ∈ Ioo a b, ∫ y in Icc x 1, h y ≠ 1 := by
  by_cases hint : IntegrableOn h (Icc (1 / 2) 1)
  · have hcont := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
      (a := 1 / 2) (b := 1) (by rwa [uIcc_of_le (by norm_num)])
    obtain ⟨δ, hδ, hball⟩ := Metric.continuousWithinAt_iff.mp
      (hcont 1 (by rw [uIcc_of_le (by norm_num)]; norm_num)) 1 one_pos
    refine ⟨max (1 / 2) (1 - δ), 1, max_lt (by norm_num) (by linarith),
      fun x hx => ⟨by linarith [le_max_left (1 / 2 : ℝ) (1 - δ), hx.1], hx.2.le⟩,
      fun x hx => ?_⟩
    have hx₁ : 1 / 2 < x := (le_max_left _ _).trans_lt hx.1
    have hxδ : 1 - δ < x := (le_max_right _ _).trans_lt hx.1
    have hlt := hball (x := x) (by rw [uIcc_of_le (by norm_num)]; exact ⟨hx₁.le, hx.2.le⟩)
      (by rw [Real.dist_eq, abs_sub_lt_iff]; constructor <;> linarith [hx.2])
    rw [intervalIntegral.integral_same, Real.dist_eq, sub_zero,
      intervalIntegral.integral_of_le hx.2.le, ← integral_Icc_eq_integral_Ioc] at hlt
    exact fun h1 => by rw [h1, abs_one] at hlt; exact lt_irrefl _ hlt
  · refine ⟨0, 1 / 2, by norm_num, fun x hx => ⟨hx.1, by linarith [hx.2]⟩, fun x hx => ?_⟩
    rw [integral_undef fun hx' => hint (IntegrableOn.mono_set hx' (Icc_subset_Icc_left hx.2.le))]
    exact zero_ne_one

/-- **No function is a unit for the Mellin convolution**, not even almost everywhere on `(0,1]`
and not even against the single density `1` on `(0,1]`: for every `e : ℝ → ℝ`,
`e ⊗ 1_{(0,1]}` differs from `1_{(0,1]}` on a set of positive measure in `(0,1]`. The unit of the
convolution is the distribution `δ(1 - x)`, which is not a function. -/
theorem not_mellinConv_indicator_one_ae_eq (e : ℝ → ℝ) :
    ¬ mellinConv e ((Ioc (0 : ℝ) 1).indicator 1)
      =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] (Ioc (0 : ℝ) 1).indicator 1 := by
  intro hae
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hae
  obtain ⟨a, b, hab, hsub, hne⟩ := exists_Ioo_integral_Icc_ne_one fun y => e y / y
  refine (isOpen_Ioo.measure_pos volume (nonempty_Ioo.mpr hab)).ne'
    (measure_mono_null (fun x hx => ?_) (ae_iff.mp hae))
  have hx01 := hsub hx
  simp only [mem_ofPred_eq, not_imp]
  refine ⟨hx01, fun hx' => hne x hx ?_⟩
  rw [← mellinConv_indicator_one_of_mem e hx01, hx', indicator_of_mem hx01, Pi.one_apply]

/-- The integrable densities supported in `[0,1]` have no unit for the Mellin convolution, even
up to equality almost everywhere on `(0,1]`. -/
theorem not_exists_forall_mellinConv_ae_eq :
    ¬ ∃ e : ℝ → ℝ, ∀ f : ℝ → ℝ, Integrable f → Function.support f ⊆ Icc 0 1 →
      mellinConv e f =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)] f := fun ⟨e, he⟩ =>
  not_mellinConv_indicator_one_ae_eq e <| he _
    ((integrableOn_const measure_Ioc_lt_top.ne).integrable_indicator measurableSet_Ioc)
    ((support_indicator_subset).trans Ioc_subset_Icc_self)

/-- The Mellin transform of a Mellin convolution: on `(0,1]` the convolution agrees with the
collinear convolution, so `mellinDis_convolveAt` gives `M[f ⊗ g] (N) = M[f] (N) * M[g] (N)`
under the hypotheses of the convolution theorem. -/
theorem mellinDis_mellinConv (f g : ℝ → ℝ) (N : ℂ) (h : MellinConvolutionAssumptions g f N) :
    mellinDis (mellinConv f g) N = mellinDis f N * mellinDis g N := by
  have hcongr : mellinDis (mellinConv f g) N = mellinDis (convolveAt (collinearKernel g) f) N :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx => by
      rw [mellinConv_eq_convolveAt f g hx]
  rw [hcongr, mellinDis_convolveAt g f N h, mul_comm]

end Convolution
end Factorization
end QFT
end EpsilonEridani
