/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
/-!

# Integration over the momentum transfer `t`

A diffractive structure function differential in the momentum transfer, `F₂^{D(4)}(β, Q², ξ, t)`,
is turned into the `t`-integrated `F₂^{D(3)}(β, Q², ξ)` by integrating over a range of `t`. The
range is part of the measurement, so here it is explicit data: `tIntegrate tLo tHi f` is the
integral of a `t`-profile `f` over `[tLo, tHi]`. At fixed `β`, `Q²` and `ξ` the profile is a real
function of `t`, and that is all this file needs.

The file proves two things about this integration.

* It loses information. Two normalised exponentials with different slopes both integrate to one,
  so their difference integrates to zero, yet it vanishes at no more than two points of the range
  (`ae_normalizedExpProfile_ne`). So a `t`-integrated quantity does not determine the
  `t`-differential one (`tIntegrate_not_injective`).
* A slope measurement restores what integration lost. Suppose the profile is a single exponential
  `A e^{-B |t|}`. If `B` is known, `A` and hence the profile follow from the integral
  (`eq_div_tIntegrate_expProfile`, `eqOn_of_tIntegrate_eq`). If `B` is not known, it is the
  logarithm of the ratio of the integrals over two windows of equal width, divided by their offset
  (`slope_eq_log_div`). Two such windows therefore fix both `A` and `B`
  (`eq_and_eq_of_tIntegrate_eq`).

In line with the sign convention `t ≤ 0`, the exponential is written in `|t|`, which is `-t` on the
physical region (`expProfile_of_nonpos`). The closed form of its integral and the slope recovery
assume that the range, or the windows, lie in `t ≤ 0`.

## Main definitions

* `tIntegrate tLo tHi f`: the integral of `f` over `[tLo, tHi]`.
* `expProfile B`: the single-exponential profile `t ↦ e^{-B |t|}` with slope `B`.
* `normalizedExpProfile tLo tHi B`: `expProfile B` divided by its integral over `[tLo, tHi]`.

## References

* H1 Collaboration, *Measurement and QCD analysis of the diffractive deep-inelastic scattering
  cross section at HERA*, Eur. Phys. J. C **48** (2006) 715, §2–3, for `F₂^{D(4)}`, `F₂^{D(3)}`
  and the `t`-range of the integration.
* G. Wolf, *Review of high energy diffraction in real and virtual photon proton scattering at
  HERA*, Rept. Prog. Phys. **73** (2010) 116202, §3, for the exponential `t`-dependence and its
  slope.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive

open MeasureTheory Set

/-! ## The `t`-integration over an explicit range -/

/-- The integral of a `t`-profile `f` over the range `[tLo, tHi]`. Applied to `F₂^{D(4)}` at fixed
`β`, `Q²` and `ξ`, it gives `F₂^{D(3)}` over that range. -/
def tIntegrate (tLo tHi : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ t in Icc tLo tHi, f t

variable {tLo tHi : ℝ} {f g : ℝ → ℝ}

theorem tIntegrate_def (tLo tHi : ℝ) (f : ℝ → ℝ) :
    tIntegrate tLo tHi f = ∫ t in Icc tLo tHi, f t := (rfl)

/-- On a non-empty range, `tIntegrate` is the interval integral. -/
theorem tIntegrate_eq_intervalIntegral (h : tLo ≤ tHi) (f : ℝ → ℝ) :
    tIntegrate tLo tHi f = ∫ t in tLo..tHi, f t := by
  rw [tIntegrate_def, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h]

/-- `tIntegrate` only sees the profile on the range. -/
theorem tIntegrate_congr (h : EqOn f g (Icc tLo tHi)) :
    tIntegrate tLo tHi f = tIntegrate tLo tHi g :=
  setIntegral_congr_fun measurableSet_Icc h

theorem tIntegrate_add (hf : IntegrableOn f (Icc tLo tHi)) (hg : IntegrableOn g (Icc tLo tHi)) :
    tIntegrate tLo tHi (f + g) = tIntegrate tLo tHi f + tIntegrate tLo tHi g :=
  integral_add hf hg

theorem tIntegrate_sub (hf : IntegrableOn f (Icc tLo tHi)) (hg : IntegrableOn g (Icc tLo tHi)) :
    tIntegrate tLo tHi (f - g) = tIntegrate tLo tHi f - tIntegrate tLo tHi g :=
  integral_sub hf hg

@[simp]
theorem tIntegrate_const_mul (c : ℝ) (f : ℝ → ℝ) :
    tIntegrate tLo tHi (fun t => c * f t) = c * tIntegrate tLo tHi f :=
  integral_const_mul c f

@[simp]
theorem tIntegrate_div_const (f : ℝ → ℝ) (c : ℝ) :
    tIntegrate tLo tHi (fun t => f t / c) = tIntegrate tLo tHi f / c :=
  integral_div c f

theorem tIntegrate_nonneg (h : ∀ t ∈ Icc tLo tHi, 0 ≤ f t) : 0 ≤ tIntegrate tLo tHi f :=
  setIntegral_nonneg measurableSet_Icc h

/-- Monotonicity in the profile. -/
theorem tIntegrate_mono (hf : IntegrableOn f (Icc tLo tHi)) (hg : IntegrableOn g (Icc tLo tHi))
    (h : ∀ t ∈ Icc tLo tHi, f t ≤ g t) : tIntegrate tLo tHi f ≤ tIntegrate tLo tHi g :=
  setIntegral_mono_on hf hg measurableSet_Icc h

/-- Monotonicity in the range, for a non-negative profile. -/
theorem tIntegrate_mono_range {tLo' tHi' : ℝ} (hf : IntegrableOn f (Icc tLo' tHi'))
    (hf₀ : ∀ t ∈ Icc tLo' tHi', 0 ≤ f t) (hLo : tLo' ≤ tLo) (hHi : tHi ≤ tHi') :
    tIntegrate tLo tHi f ≤ tIntegrate tLo' tHi' f :=
  setIntegral_mono_set hf ((ae_restrict_iff' measurableSet_Icc).mpr (.of_forall hf₀))
    (Icc_subset_Icc hLo hHi).eventuallyLE

/-- Adjacent ranges add. -/
theorem tIntegrate_add_adjacent {t₁ t₂ t₃ : ℝ} (h₁₂ : t₁ ≤ t₂) (h₂₃ : t₂ ≤ t₃)
    (hf : IntegrableOn f (Icc t₁ t₃)) :
    tIntegrate t₁ t₂ f + tIntegrate t₂ t₃ f = tIntegrate t₁ t₃ f := by
  rw [tIntegrate_eq_intervalIntegral h₁₂, tIntegrate_eq_intervalIntegral h₂₃,
    tIntegrate_eq_intervalIntegral (h₁₂.trans h₂₃)]
  exact intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegrable_iff_integrableOn_Icc_of_le h₁₂).mpr
      (hf.mono_set (Icc_subset_Icc_right h₂₃)))
    ((intervalIntegrable_iff_integrableOn_Icc_of_le h₂₃).mpr
      (hf.mono_set (Icc_subset_Icc_left h₁₂)))

/-- Shifting the profile by `s` is shifting the range by `s`. -/
theorem tIntegrate_comp_add_right (s : ℝ) (f : ℝ → ℝ) :
    tIntegrate tLo tHi (fun t => f (t + s)) = tIntegrate (tLo + s) (tHi + s) f := by
  rcases le_or_gt tLo tHi with h | h
  · rw [tIntegrate_eq_intervalIntegral h, tIntegrate_eq_intervalIntegral (by linarith),
      intervalIntegral.integral_comp_add_right]
  · rw [tIntegrate_def, tIntegrate_def, Icc_eq_empty h.not_ge,
      Icc_eq_empty (by linarith : ¬tLo + s ≤ tHi + s), Measure.restrict_empty,
      integral_zero_measure, integral_zero_measure]

/-! ## The single-exponential profile -/

/-- The single-exponential `t`-profile `e^{-B |t|}` with slope `B`. On the physical region `t ≤ 0`,
`|t|` is `-t` (`expProfile_of_nonpos`). -/
def expProfile (B t : ℝ) : ℝ :=
  Real.exp (-(B * |t|))

variable {B : ℝ}

theorem expProfile_def (B t : ℝ) : expProfile B t = Real.exp (-(B * |t|)) := (rfl)

theorem expProfile_pos (B t : ℝ) : 0 < expProfile B t :=
  Real.exp_pos _

theorem expProfile_of_nonpos {t : ℝ} (ht : t ≤ 0) : expProfile B t = Real.exp (B * t) := by
  rw [expProfile_def, abs_of_nonpos ht, mul_neg, neg_neg]

@[fun_prop]
theorem continuous_expProfile (B : ℝ) : Continuous (expProfile B) := by
  unfold expProfile
  fun_prop

theorem integrableOn_expProfile (B tLo tHi : ℝ) : IntegrableOn (expProfile B) (Icc tLo tHi) :=
  (continuous_expProfile B).integrableOn_Icc

theorem tIntegrate_expProfile_pos (B : ℝ) (h : tLo < tHi) :
    0 < tIntegrate tLo tHi (expProfile B) := by
  rw [tIntegrate_eq_intervalIntegral h.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((continuous_expProfile B).intervalIntegrable _ _) (fun t _ => expProfile_pos B t) h

/-- The closed form of the integral of the exponential profile over a range in `t ≤ 0`. -/
theorem tIntegrate_expProfile (hB : B ≠ 0) (h : tLo ≤ tHi) (hHi : tHi ≤ 0) :
    tIntegrate tLo tHi (expProfile B) = (Real.exp (B * tHi) - Real.exp (B * tLo)) / B := by
  rw [tIntegrate_eq_intervalIntegral h,
    intervalIntegral.integral_congr (g := fun t => Real.exp (B * t)) fun t ht =>
      expProfile_of_nonpos (by rw [uIcc_of_le h] at ht; exact ht.2.trans hHi),
    intervalIntegral.integral_comp_mul_left (fun t => Real.exp t) hB, integral_exp, smul_eq_mul,
    inv_mul_eq_div]

/-- Shifting a range in `t ≤ 0` by `s` multiplies the integral of the exponential profile by
`e^{B s}`. -/
theorem tIntegrate_expProfile_add {a b s : ℝ} (hb : b ≤ 0) (hbs : b + s ≤ 0) :
    tIntegrate (a + s) (b + s) (expProfile B) =
      Real.exp (B * s) * tIntegrate a b (expProfile B) := by
  rw [← tIntegrate_comp_add_right, ← tIntegrate_const_mul]
  refine tIntegrate_congr fun t ht => ?_
  rw [expProfile_of_nonpos (by linarith [ht.2]), expProfile_of_nonpos (ht.2.trans hb),
    ← Real.exp_add, mul_add, add_comm]

/-! ## Integration loses the `t`-dependence -/

/-- The exponential profile with slope `B`, normalised to integrate to one over `[tLo, tHi]`. -/
def normalizedExpProfile (tLo tHi B t : ℝ) : ℝ :=
  expProfile B t / tIntegrate tLo tHi (expProfile B)

theorem normalizedExpProfile_def (tLo tHi B t : ℝ) :
    normalizedExpProfile tLo tHi B t = expProfile B t / tIntegrate tLo tHi (expProfile B) := (rfl)

@[fun_prop]
theorem continuous_normalizedExpProfile (tLo tHi B : ℝ) :
    Continuous (normalizedExpProfile tLo tHi B) :=
  (continuous_expProfile B).div_const _

theorem tIntegrate_normalizedExpProfile (B : ℝ) (h : tLo < tHi) :
    tIntegrate tLo tHi (normalizedExpProfile tLo tHi B) = 1 := by
  rw [tIntegrate_congr (g := fun t => expProfile B t / tIntegrate tLo tHi (expProfile B))
      fun t _ => normalizedExpProfile_def tLo tHi B t, tIntegrate_div_const,
    div_self (tIntegrate_expProfile_pos B h).ne']

/-- Two normalised exponentials integrate to the same value, so their difference is in the kernel
of `tIntegrate`. -/
theorem tIntegrate_normalizedExpProfile_sub (B₁ B₂ : ℝ) (h : tLo < tHi) :
    tIntegrate tLo tHi (normalizedExpProfile tLo tHi B₁ - normalizedExpProfile tLo tHi B₂) = 0 := by
  rw [tIntegrate_sub (continuous_normalizedExpProfile _ _ _).integrableOn_Icc
      (continuous_normalizedExpProfile _ _ _).integrableOn_Icc,
    tIntegrate_normalizedExpProfile B₁ h, tIntegrate_normalizedExpProfile B₂ h, sub_self]

/-- Normalised exponentials with different slopes agree only where `|t|` takes one value. -/
private theorem abs_eq_of_normalizedExpProfile_eq {B₁ B₂ t : ℝ} (h : tLo < tHi) (hB : B₁ ≠ B₂)
    (heq : normalizedExpProfile tLo tHi B₁ t = normalizedExpProfile tLo tHi B₂ t) :
    |t| = Real.log (tIntegrate tLo tHi (expProfile B₁) / tIntegrate tLo tHi (expProfile B₂)) /
      (B₂ - B₁) := by
  have h₁ := tIntegrate_expProfile_pos B₁ h
  have h₂ := tIntegrate_expProfile_pos B₂ h
  rw [normalizedExpProfile_def, normalizedExpProfile_def, expProfile_def, expProfile_def,
    div_eq_div_iff h₁.ne' h₂.ne'] at heq
  have hexp : Real.exp ((B₂ - B₁) * |t|) =
      tIntegrate tLo tHi (expProfile B₁) / tIntegrate tLo tHi (expProfile B₂) := by
    rw [show (B₂ - B₁) * |t| = -(B₁ * |t|) - -(B₂ * |t|) by ring, Real.exp_sub,
      div_eq_div_iff (Real.exp_pos _).ne' h₂.ne']
    linarith
  rw [← hexp, Real.log_exp, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hB.symm)]

/-- Normalised exponentials with different slopes differ almost everywhere on the range: they agree
at no more than two points. -/
theorem ae_normalizedExpProfile_ne {B₁ B₂ : ℝ} (h : tLo < tHi) (hB : B₁ ≠ B₂) :
    ∀ᵐ t ∂volume.restrict (Icc tLo tHi),
      normalizedExpProfile tLo tHi B₁ t ≠ normalizedExpProfile tLo tHi B₂ t := by
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
  set x := Real.log (tIntegrate tLo tHi (expProfile B₁) / tIntegrate tLo tHi (expProfile B₂)) /
    (B₂ - B₁)
  refine measure_mono_null (t := {x, -x}) (fun t ht => ?_) ((toFinite _).measure_zero _)
  simp only [not_imp, not_not, mem_ofPred_eq] at ht
  have hx := abs_eq_of_normalizedExpProfile_eq h hB ht.2
  simp only [mem_insert_iff, mem_singleton_iff]
  rcases abs_choice t with ht' | ht'
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- `F₂^{D(3)}` does not determine `F₂^{D(4)}`: on a range of positive length, the
difference of two normalised exponentials with different slopes is a continuous profile that is
not almost everywhere zero on the range, yet integrates to zero over it. -/
theorem tIntegrate_not_injective (h : tLo < tHi) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ¬f =ᵐ[volume.restrict (Icc tLo tHi)] 0 ∧
      tIntegrate tLo tHi f = 0 := by
  refine ⟨normalizedExpProfile tLo tHi 0 - normalizedExpProfile tLo tHi 1, by fun_prop,
    fun h0 => ?_, tIntegrate_normalizedExpProfile_sub 0 1 h⟩
  have hfalse : ∀ᵐ _t ∂volume.restrict (Icc tLo tHi), False := by
    filter_upwards [h0, ae_normalizedExpProfile_ne h zero_ne_one] with t ht hne
    exact hne (sub_eq_zero.mp ht)
  simp only [ae_iff, not_false_eq_true, ofPred_true, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.ofReal_eq_zero] at hfalse
  linarith

/-! ## Recovery under the single-exponential hypothesis -/

/-- If the profile is `A e^{-B |t|}` on the range, then `A` is the integral of the profile divided
by that of `e^{-B |t|}`. -/
theorem eq_div_tIntegrate_expProfile {A : ℝ} (h : tLo < tHi)
    (hf : EqOn f (fun t => A * expProfile B t) (Icc tLo tHi)) :
    A = tIntegrate tLo tHi f / tIntegrate tLo tHi (expProfile B) := by
  rw [tIntegrate_congr hf, tIntegrate_const_mul,
    mul_div_cancel_right₀ _ (tIntegrate_expProfile_pos B h).ne']

/-- With the slope known, the `t`-integrated quantity determines the `t`-differential one: two
single-exponential profiles with the same slope and the same integral agree on the range. -/
theorem eqOn_of_tIntegrate_eq {A A' : ℝ} (h : tLo < tHi)
    (hf : EqOn f (fun t => A * expProfile B t) (Icc tLo tHi))
    (hg : EqOn g (fun t => A' * expProfile B t) (Icc tLo tHi))
    (hfg : tIntegrate tLo tHi f = tIntegrate tLo tHi g) : EqOn f g (Icc tLo tHi) := by
  have hA : A = A' := by
    rw [eq_div_tIntegrate_expProfile h hf, eq_div_tIntegrate_expProfile h hg, hfg]
  intro t ht
  rw [hf ht, hg ht, hA]

/-- The slope of a single-exponential profile is fixed by its integrals over two windows
`[a, b]` and `[a + s, b + s]` of equal width in `t ≤ 0`: it is the logarithm of their ratio
divided by the offset `s`. -/
theorem slope_eq_log_div {A a b s : ℝ} (hA : A ≠ 0) (hab : a < b) (hb : b ≤ 0) (hbs : b + s ≤ 0)
    (hs : s ≠ 0) (hf : EqOn f (fun t => A * expProfile B t) (Icc a b ∪ Icc (a + s) (b + s))) :
    B = Real.log (tIntegrate (a + s) (b + s) f / tIntegrate a b f) / s := by
  rw [tIntegrate_congr (hf.mono subset_union_right), tIntegrate_congr (hf.mono subset_union_left),
    tIntegrate_const_mul, tIntegrate_const_mul, tIntegrate_expProfile_add hb hbs,
    mul_left_comm A,
    mul_div_cancel_right₀ _ (mul_ne_zero hA (tIntegrate_expProfile_pos B hab).ne'), Real.log_exp,
    mul_div_cancel_right₀ _ hs]

/-- Integrals over two windows `[a, b]` and `[a + s, b + s]` of equal width in `t ≤ 0` determine
both the normalisation and the slope of a single-exponential profile. -/
theorem eq_and_eq_of_tIntegrate_eq {A A' B' a b s : ℝ} (hA : A ≠ 0) (hab : a < b) (hb : b ≤ 0)
    (hbs : b + s ≤ 0) (hs : s ≠ 0)
    (hf : EqOn f (fun t => A * expProfile B t) (Icc a b ∪ Icc (a + s) (b + s)))
    (hg : EqOn g (fun t => A' * expProfile B' t) (Icc a b ∪ Icc (a + s) (b + s)))
    (h₁ : tIntegrate a b f = tIntegrate a b g)
    (h₂ : tIntegrate (a + s) (b + s) f = tIntegrate (a + s) (b + s) g) :
    A = A' ∧ B = B' := by
  have hA' : A' ≠ 0 := by
    rintro rfl
    have := tIntegrate_congr (hf.mono subset_union_left)
    rw [h₁, tIntegrate_congr (hg.mono subset_union_left), tIntegrate_const_mul,
      tIntegrate_const_mul, zero_mul] at this
    exact mul_ne_zero hA (tIntegrate_expProfile_pos B hab).ne' this.symm
  have hB : B = B' := by
    rw [slope_eq_log_div hA hab hb hbs hs hf, slope_eq_log_div hA' hab hb hbs hs hg, h₁, h₂]
  subst hB
  refine ⟨?_, rfl⟩
  rw [eq_div_tIntegrate_expProfile hab (hf.mono subset_union_left),
    eq_div_tIntegrate_expProfile hab (hg.mono subset_union_left), h₁]

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
