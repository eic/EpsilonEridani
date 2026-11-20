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
  so their difference integrates to zero, yet it vanishes only where `|t|` takes one value
  (`abs_eq_of_normalizedExpProfile_eq`), hence almost nowhere on the range
  (`ae_normalizedExpProfile_ne`). So a `t`-integrated quantity does not determine the
  `t`-differential one (`exists_continuous_not_ae_eq_zero_tIntegrate_eq_zero`,
  `tIntegrate_not_injective`).
* A slope measurement restores what integration lost. Suppose the profile is a single exponential
  `A e^{-B |t|}`. If `B` is known, `A` and hence the profile follow from the integral
  (`eq_div_tIntegrate`, `eqOn_of_tIntegrate_eq_expProfile`). If `B` is not known, it is the
  logarithm of the ratio of the integrals over two windows of equal width, divided by their offset
  (`expProfile_slope_eq_log_div`). Two such windows therefore fix both `A` and `B`
  (`eq_and_eq_of_tIntegrate_eq_expProfile`).

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

/-- On an empty or one-point range, `tIntegrate` is zero. -/
@[simp]
theorem tIntegrate_eq_zero_of_le (h : tHi ≤ tLo) (f : ℝ → ℝ) : tIntegrate tLo tHi f = 0 := by
  rw [tIntegrate_def, Measure.restrict_eq_zero.mpr (by
    rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith), integral_zero_measure]

/-- On a one-point range, `tIntegrate` is zero. -/
theorem tIntegrate_self (t : ℝ) (f : ℝ → ℝ) : tIntegrate t t f = 0 :=
  tIntegrate_eq_zero_of_le le_rfl f

/-- The integral of a constant profile is the width of the range times the constant. -/
theorem tIntegrate_const (h : tLo ≤ tHi) (c : ℝ) :
    tIntegrate tLo tHi (fun _ => c) = (tHi - tLo) * c := by
  rw [tIntegrate_eq_intervalIntegral h, intervalIntegral.integral_const, smul_eq_mul]

/-- `tIntegrate` only sees the profile on the range. -/
theorem tIntegrate_congr (h : EqOn f g (Icc tLo tHi)) :
    tIntegrate tLo tHi f = tIntegrate tLo tHi g :=
  setIntegral_congr_fun measurableSet_Icc h

theorem tIntegrate_add (hf : IntegrableOn f (Icc tLo tHi)) (hg : IntegrableOn g (Icc tLo tHi)) :
    tIntegrate tLo tHi (fun t => f t + g t) = tIntegrate tLo tHi f + tIntegrate tLo tHi g :=
  integral_add hf hg

theorem tIntegrate_sub (hf : IntegrableOn f (Icc tLo tHi)) (hg : IntegrableOn g (Icc tLo tHi)) :
    tIntegrate tLo tHi (fun t => f t - g t) = tIntegrate tLo tHi f - tIntegrate tLo tHi g :=
  integral_sub hf hg

@[simp]
theorem tIntegrate_const_mul (c : ℝ) (f : ℝ → ℝ) :
    tIntegrate tLo tHi (fun t => c * f t) = c * tIntegrate tLo tHi f :=
  integral_const_mul c f

/-- If the profile is `A φ` on the range, its integral is `A` times that of `φ`. -/
theorem tIntegrate_eq_const_mul_of_eqOn {A : ℝ} {φ : ℝ → ℝ}
    (hf : EqOn f (fun t => A * φ t) (Icc tLo tHi)) :
    tIntegrate tLo tHi f = A * tIntegrate tLo tHi φ := by
  rw [tIntegrate_congr hf, tIntegrate_const_mul]

@[simp]
theorem tIntegrate_div_const (f : ℝ → ℝ) (c : ℝ) :
    tIntegrate tLo tHi (fun t => f t / c) = tIntegrate tLo tHi f / c :=
  integral_div c f

theorem tIntegrate_nonneg (h : ∀ t ∈ Icc tLo tHi, 0 ≤ f t) : 0 ≤ tIntegrate tLo tHi f :=
  setIntegral_nonneg measurableSet_Icc h

/-- A profile that is integrable on a range of positive length and positive on its interior has
positive integral. -/
theorem tIntegrate_pos (hf : IntegrableOn f (Icc tLo tHi)) (hpos : ∀ t ∈ Ioo tLo tHi, 0 < f t)
    (h : tLo < tHi) : 0 < tIntegrate tLo tHi f := by
  rw [tIntegrate_eq_intervalIntegral h.le]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((intervalIntegrable_iff_integrableOn_Icc_of_le h.le).mpr hf) hpos h

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

/-- Shifting the profile by `s` is shifting the range by `s`. -/
theorem tIntegrate_comp_add_right (s : ℝ) (f : ℝ → ℝ) :
    tIntegrate tLo tHi (fun t => f (t + s)) = tIntegrate (tLo + s) (tHi + s) f := by
  rcases le_or_gt tLo tHi with h | h
  · rw [tIntegrate_eq_intervalIntegral h, tIntegrate_eq_intervalIntegral (by linarith),
      intervalIntegral.integral_comp_add_right]
  · rw [tIntegrate_eq_zero_of_le h.le, tIntegrate_eq_zero_of_le (by linarith)]

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

@[simp]
theorem expProfile_zero : expProfile 0 = fun _ => 1 := by
  funext t
  rw [expProfile_def, zero_mul, neg_zero, Real.exp_zero]

/-- The profile is normalised to one at `t = 0`. -/
@[simp]
theorem expProfile_apply_zero (B : ℝ) : expProfile B 0 = 1 := by
  rw [expProfile_def, abs_zero, mul_zero, neg_zero, Real.exp_zero]

/-- With zero slope, the integral of the profile is the width of the range. -/
theorem tIntegrate_expProfile_zero (h : tLo ≤ tHi) :
    tIntegrate tLo tHi (expProfile 0) = tHi - tLo := by
  rw [expProfile_zero, tIntegrate_const h, mul_one]

theorem tIntegrate_expProfile_pos (B : ℝ) (h : tLo < tHi) :
    0 < tIntegrate tLo tHi (expProfile B) :=
  tIntegrate_pos (continuous_expProfile B).integrableOn_Icc (fun t _ => expProfile_pos B t) h

/-- The closed form of the integral of the exponential profile over a range in `t ≤ 0`. -/
theorem tIntegrate_expProfile (hB : B ≠ 0) (h : tLo ≤ tHi) (hHi : tHi ≤ 0) :
    tIntegrate tLo tHi (expProfile B) = (Real.exp (B * tHi) - Real.exp (B * tLo)) / B := by
  have hexp : EqOn (expProfile B) (fun t => Real.exp (B * t)) (uIcc tLo tHi) := by
    rw [uIcc_of_le h]
    exact fun t ht => expProfile_of_nonpos (ht.2.trans hHi)
  rw [tIntegrate_eq_intervalIntegral h, intervalIntegral.integral_congr hexp,
    intervalIntegral.integral_comp_mul_left (fun t => Real.exp t) hB, integral_exp, smul_eq_mul,
    inv_mul_eq_div]

/-- Shifting a range in `t ≤ 0` by `s` multiplies the integral of the exponential profile by
`e^{B s}`. -/
theorem tIntegrate_expProfile_add_eq_exp_mul {a b s : ℝ} (hb : b ≤ 0) (hbs : b + s ≤ 0) :
    tIntegrate (a + s) (b + s) (expProfile B) =
      Real.exp (B * s) * tIntegrate a b (expProfile B) := by
  rw [← tIntegrate_comp_add_right, ← tIntegrate_const_mul]
  refine tIntegrate_congr fun t ht => ?_
  rw [expProfile_of_nonpos (by linarith [ht.2]), expProfile_of_nonpos (ht.2.trans hb),
    ← Real.exp_add, mul_add, add_comm]

/-! ## Integration loses the `t`-dependence -/

/-- The exponential profile with slope `B`, divided by its integral over `[tLo, tHi]`. On a range of
positive length it integrates to one (`tIntegrate_normalizedExpProfile_eq_one`); on a degenerate
range the divisor is zero and so is the profile. -/
def normalizedExpProfile (tLo tHi B t : ℝ) : ℝ :=
  expProfile B t / tIntegrate tLo tHi (expProfile B)

theorem normalizedExpProfile_def (tLo tHi B t : ℝ) :
    normalizedExpProfile tLo tHi B t = expProfile B t / tIntegrate tLo tHi (expProfile B) := (rfl)

theorem normalizedExpProfile_eq_div (tLo tHi B : ℝ) :
    normalizedExpProfile tLo tHi B = fun t => expProfile B t / tIntegrate tLo tHi (expProfile B) :=
  (rfl)

@[fun_prop]
theorem continuous_normalizedExpProfile (tLo tHi B : ℝ) :
    Continuous (normalizedExpProfile tLo tHi B) :=
  (continuous_expProfile B).div_const _

/-- On a range of positive length, the normalised exponential integrates to one. -/
@[simp]
theorem tIntegrate_normalizedExpProfile_eq_one (B : ℝ) (h : tLo < tHi) :
    tIntegrate tLo tHi (normalizedExpProfile tLo tHi B) = 1 := by
  rw [normalizedExpProfile_eq_div, tIntegrate_div_const,
    div_self (tIntegrate_expProfile_pos B h).ne']

/-- Two normalised exponentials integrate to the same value, so their difference is in the kernel
of `tIntegrate`. -/
theorem tIntegrate_normalizedExpProfile_sub_eq_zero (B₁ B₂ : ℝ) (h : tLo < tHi) :
    tIntegrate tLo tHi (fun t => normalizedExpProfile tLo tHi B₁ t -
      normalizedExpProfile tLo tHi B₂ t) = 0 := by
  rw [tIntegrate_sub (continuous_normalizedExpProfile _ _ _).integrableOn_Icc
      (continuous_normalizedExpProfile _ _ _).integrableOn_Icc,
    tIntegrate_normalizedExpProfile_eq_one B₁ h, tIntegrate_normalizedExpProfile_eq_one B₂ h,
    sub_self]

/-- Normalised exponentials with different slopes agree only where `|t|` takes one value, so at no
more than two points. -/
theorem abs_eq_of_normalizedExpProfile_eq {B₁ B₂ t : ℝ} (h : tLo < tHi) (hB : B₁ ≠ B₂)
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

/-- Normalised exponentials with different slopes differ almost everywhere: by
`abs_eq_of_normalizedExpProfile_eq` they agree at no more than two points. -/
theorem ae_normalizedExpProfile_ne {B₁ B₂ : ℝ} (h : tLo < tHi) (hB : B₁ ≠ B₂) :
    ∀ᵐ t ∂(volume : Measure ℝ),
      normalizedExpProfile tLo tHi B₁ t ≠ normalizedExpProfile tLo tHi B₂ t := by
  set x := Real.log (tIntegrate tLo tHi (expProfile B₁) / tIntegrate tLo tHi (expProfile B₂)) /
    (B₂ - B₁)
  have hnull : volume ({x, -x} : Set ℝ) = 0 := (toFinite _).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht heq
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at ht
  have hx : |t| = x := abs_eq_of_normalizedExpProfile_eq h hB heq
  rcases abs_choice t with ht' | ht'
  · exact ht.1 (by linarith)
  · exact ht.2 (by linarith)

/-- `F₂^{D(3)}` does not determine `F₂^{D(4)}`: on a range of positive length, the
difference of two normalised exponentials with different slopes is a continuous profile that is
not almost everywhere zero on the range, yet integrates to zero over it. -/
theorem exists_continuous_not_ae_eq_zero_tIntegrate_eq_zero (h : tLo < tHi) :
    ∃ f : ℝ → ℝ, Continuous f ∧ ¬f =ᵐ[volume.restrict (Icc tLo tHi)] 0 ∧
      tIntegrate tLo tHi f = 0 := by
  refine ⟨fun t => normalizedExpProfile tLo tHi 0 t - normalizedExpProfile tLo tHi 1 t,
    by fun_prop, fun h0 => ?_, tIntegrate_normalizedExpProfile_sub_eq_zero 0 1 h⟩
  have hfalse : ∀ᵐ _t ∂volume.restrict (Icc tLo tHi), False := by
    filter_upwards [h0, ae_restrict_of_ae (ae_normalizedExpProfile_ne h zero_ne_one)]
      with t ht hne
    exact hne (sub_eq_zero.mp ht)
  have hne : volume.restrict (Icc tLo tHi) ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero, Real.volume_Icc, ENNReal.ofReal_eq_zero, not_le]
    exact sub_pos.mpr h
  -- `Filter.Eventually.exists` needs the a.e. filter of the restricted measure to be non-trivial.
  have : (ae (volume.restrict (Icc tLo tHi))).NeBot := ae_neBot.mpr hne
  exact hfalse.exists.elim fun _ hx => hx

/-- `F₂^{D(3)}` does not determine `F₂^{D(4)}`: on a range of positive length, `tIntegrate` is not
injective. -/
theorem tIntegrate_not_injective (h : tLo < tHi) : ¬Function.Injective (tIntegrate tLo tHi) := by
  intro hinj
  obtain ⟨f, -, hf, hf0⟩ := exists_continuous_not_ae_eq_zero_tIntegrate_eq_zero h
  have hz : tIntegrate tLo tHi 0 = 0 := by simp [tIntegrate_def]
  exact hf (by rw [hinj (hf0.trans hz.symm)])

/-! ## Recovery under the single-exponential hypothesis -/

/-- If the profile is `A φ` on the range and `φ` has non-zero integral, then `A` is the integral of
the profile divided by that of `φ`. -/
theorem eq_div_tIntegrate {A : ℝ} {φ : ℝ → ℝ} (hφ : tIntegrate tLo tHi φ ≠ 0)
    (hf : EqOn f (fun t => A * φ t) (Icc tLo tHi)) :
    A = tIntegrate tLo tHi f / tIntegrate tLo tHi φ := by
  rw [tIntegrate_eq_const_mul_of_eqOn hf, mul_div_cancel_right₀ _ hφ]

/-- Two multiples `A φ` and `A' φ` of a profile `φ` with non-zero integral that have the same
integral have the same coefficient. -/
theorem eq_of_tIntegrate_eq {A A' : ℝ} {φ : ℝ → ℝ} (hφ : tIntegrate tLo tHi φ ≠ 0)
    (hf : EqOn f (fun t => A * φ t) (Icc tLo tHi))
    (hg : EqOn g (fun t => A' * φ t) (Icc tLo tHi))
    (hfg : tIntegrate tLo tHi f = tIntegrate tLo tHi g) : A = A' := by
  rw [eq_div_tIntegrate hφ hf, eq_div_tIntegrate hφ hg, hfg]

/-- With the shape `φ` known and of non-zero integral, the `t`-integrated quantity determines the
`t`-differential one: two multiples of `φ` with the same integral agree on the range. -/
theorem eqOn_of_tIntegrate_eq {A A' : ℝ} {φ : ℝ → ℝ} (hφ : tIntegrate tLo tHi φ ≠ 0)
    (hf : EqOn f (fun t => A * φ t) (Icc tLo tHi))
    (hg : EqOn g (fun t => A' * φ t) (Icc tLo tHi))
    (hfg : tIntegrate tLo tHi f = tIntegrate tLo tHi g) : EqOn f g (Icc tLo tHi) := by
  intro t ht
  rw [hf ht, hg ht, eq_of_tIntegrate_eq hφ hf hg hfg]

/-- With the slope known, the `t`-integrated quantity determines the `t`-differential one: two
single-exponential profiles with the same slope and the same integral over a range of positive
length agree on the range. -/
theorem eqOn_of_tIntegrate_eq_expProfile {A A' : ℝ} (h : tLo < tHi)
    (hf : EqOn f (fun t => A * expProfile B t) (Icc tLo tHi))
    (hg : EqOn g (fun t => A' * expProfile B t) (Icc tLo tHi))
    (hfg : tIntegrate tLo tHi f = tIntegrate tLo tHi g) : EqOn f g (Icc tLo tHi) :=
  eqOn_of_tIntegrate_eq (tIntegrate_expProfile_pos B h).ne' hf hg hfg

/-- The slope of a single-exponential profile is fixed by its integrals over two windows
`[a, b]` and `[a + s, b + s]` of equal width in `t ≤ 0`: it is the logarithm of their ratio
divided by the offset `s`. -/
theorem expProfile_slope_eq_log_div {A a b s : ℝ} (hA : A ≠ 0) (hab : a < b) (hb : b ≤ 0)
    (hbs : b + s ≤ 0) (hs : s ≠ 0)
    (hf : EqOn f (fun t => A * expProfile B t) (Icc a b ∪ Icc (a + s) (b + s))) :
    B = Real.log (tIntegrate (a + s) (b + s) f / tIntegrate a b f) / s := by
  have h₁ : tIntegrate a b f = A * tIntegrate a b (expProfile B) :=
    tIntegrate_eq_const_mul_of_eqOn (hf.mono subset_union_left)
  have h₂ : tIntegrate (a + s) (b + s) f =
      Real.exp (B * s) * (A * tIntegrate a b (expProfile B)) := by
    rw [tIntegrate_eq_const_mul_of_eqOn (hf.mono subset_union_right),
      tIntegrate_expProfile_add_eq_exp_mul hb hbs, mul_left_comm]
  have hI : A * tIntegrate a b (expProfile B) ≠ 0 :=
    mul_ne_zero hA (tIntegrate_expProfile_pos B hab).ne'
  rw [h₁, h₂, mul_div_cancel_right₀ _ hI, Real.log_exp, mul_div_cancel_right₀ _ hs]

/-- Integrals over two windows `[a, b]` and `[a + s, b + s]` of equal width in `t ≤ 0` determine
both the normalisation and the slope of a single-exponential profile. -/
theorem eq_and_eq_of_tIntegrate_eq_expProfile {A A' B' a b s : ℝ} (hA : A ≠ 0) (hab : a < b)
    (hb : b ≤ 0) (hbs : b + s ≤ 0) (hs : s ≠ 0)
    (hf : EqOn f (fun t => A * expProfile B t) (Icc a b ∪ Icc (a + s) (b + s)))
    (hg : EqOn g (fun t => A' * expProfile B' t) (Icc a b ∪ Icc (a + s) (b + s)))
    (h₁ : tIntegrate a b f = tIntegrate a b g)
    (h₂ : tIntegrate (a + s) (b + s) f = tIntegrate (a + s) (b + s) g) :
    A = A' ∧ B = B' := by
  have hA' : A' ≠ 0 := by
    rintro rfl
    have := tIntegrate_eq_const_mul_of_eqOn (hf.mono subset_union_left)
    rw [h₁, tIntegrate_eq_const_mul_of_eqOn (hg.mono subset_union_left), zero_mul] at this
    exact mul_ne_zero hA (tIntegrate_expProfile_pos B hab).ne' this.symm
  have hB : B = B' := by
    rw [expProfile_slope_eq_log_div hA hab hb hbs hs hf,
      expProfile_slope_eq_log_div hA' hab hb hbs hs hg, h₁, h₂]
  subst hB
  exact ⟨eq_of_tIntegrate_eq (tIntegrate_expProfile_pos B hab).ne' (hf.mono subset_union_left)
    (hg.mono subset_union_left) h₁, rfl⟩

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
