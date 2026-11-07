/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import EpsilonEridani.Mathematics.Probability.InverseTransform
public import EpsilonEridani.QFT.Shower.Sudakov

/-!
# The law of the first emission scale

The scale at which a shower first emits, as a random variable: the law whose density at `t` is
the emission rate `K t` times the no-emission factor `sudakov K t T` down to `t`, and the theorem
that one uniform variate sampled through the inverse of the Sudakov factor draws from it.

`emissionLaw K T` is that law, defined as a density against Lebesgue measure on the scales below
the hard scale `T` (there is nothing above `T`: the shower starts there). Its distribution
function is `emissionCdf K T`, the Sudakov factor capped at `1`, so that

`emissionLaw K T (Iic x) = ENNReal.ofReal (sudakov K x T)` for `x ≤ T`,

which is the statement that **the Sudakov factor is the probability of emitting below `x`**, and
is what licenses calling `sudakov` a probability at all. The identification is an improper
fundamental theorem of calculus: the density is the derivative in the lower limit of the Sudakov
factor, whose limit at `-∞` is `0`.

The hypotheses are those under which the shower emits: `K` continuous and non-negative, and the
integrated kernel diverging as the scale falls. Without the divergence the law is defective — the
missing mass is the probability of never emitting — and the sampling theorem below genuinely
fails, so the hypothesis is not decoration.

`hasLaw_of_isQuantileFunction` is the sampling theorem, stated for an arbitrary inverse of the
distribution function through `EpsilonEridani.IsQuantileFunction`: an implementation inverts the
Sudakov factor in whatever closed form its kernel allows, which the characterisation accepts
without being told the formula. Reading the characterisation below the hard scale makes the
content explicit: `q u` is the least scale `x` at which the integrated kernel `∫_x^T K` has fallen
to `-log u`, which is the sampler `Γ⁻¹(-log u)` of a kernel with primitive `Γ`. For a constant
kernel everything is in closed form and the sampler is `u ↦ T + log u / r` (`hasLaw_add_log_div`).

The veto algorithm, which samples this same law through an overestimating kernel whose inverse is
available, is the subject of `EpsilonEridani.QFT.Shower.Sudakov`; the identity that makes it
unbiased is proved there, and the law of its output is not treated here.

## Main definitions

* `EpsilonEridani.QFT.Shower.emissionLaw`: the law of the first emission scale.
* `EpsilonEridani.QFT.Shower.emissionCdf`: its distribution function.

## Main results

* `EpsilonEridani.QFT.Shower.setIntegral_Iic_sudakov_density`: the Sudakov density integrates to
  the Sudakov factor on the scales below `x`.
* `EpsilonEridani.QFT.Shower.emissionLaw_Iic` and
  `EpsilonEridani.QFT.Shower.isProbabilityMeasure_emissionLaw`: the Sudakov factor is the
  probability of emitting below a scale, and emission is certain.
* `EpsilonEridani.QFT.Shower.cdf_emissionLaw`: `emissionCdf` is the distribution function of the
  law, in the sense of `ProbabilityTheory.cdf`.
* `EpsilonEridani.QFT.Shower.hasLaw_of_isQuantileFunction` and
  `EpsilonEridani.QFT.Shower.hasLaw_add_log_div`: the scale sampler draws the first emission scale.

## References

* T. Sjöstrand, *A model for initial state parton showers*, Phys. Lett. B 157 (1985) 321, for the
  veto algorithm and the Sudakov density it samples.
* S. Plätzer and M. Sjödahl, *Sudakov veto algorithms*, Eur. Phys. J. Plus 127 (2012) 26.
-/

@[expose] public section

open MeasureTheory Measure Set Filter Topology ProbabilityTheory

open scoped ENNReal

namespace EpsilonEridani

namespace QFT

namespace Shower

variable {K : ℝ → ℝ} {T x : ℝ}

/-- The law of the scale of the first emission: the *Sudakov density* `K t * sudakov K t T` --
the rate at `t` times the probability of no emission between `t` and `T` -- against Lebesgue
measure on the scales below the hard scale. -/
noncomputable def emissionLaw (K : ℝ → ℝ) (T : ℝ) : Measure ℝ :=
  (volume.restrict (Iic T)).withDensity fun t => ENNReal.ofReal (K t * sudakov K t T)

/-- The distribution function of the first emission scale: the Sudakov factor below the hard
scale, and `1` above it. -/
noncomputable def emissionCdf (K : ℝ → ℝ) (T : ℝ) (x : ℝ) : ℝ := min (sudakov K x T) 1

/-- The Sudakov density is non-negative, for a non-negative kernel. -/
theorem sudakov_density_nonneg (hK0 : ∀ t, 0 ≤ K t) (T t : ℝ) : 0 ≤ K t * sudakov K t T :=
  mul_nonneg (hK0 t) (sudakov_pos K t T).le

/-- The distribution function of the first emission scale is non-negative. -/
theorem emissionCdf_nonneg (K : ℝ → ℝ) (T x : ℝ) : 0 ≤ emissionCdf K T x :=
  le_min (sudakov_pos K x T).le zero_le_one

/-- Below the hard scale the distribution function of the first emission scale is the Sudakov
factor. -/
theorem emissionCdf_of_le (hK0 : ∀ t, 0 ≤ K t) (hx : x ≤ T) :
    emissionCdf K T x = sudakov K x T :=
  min_eq_left (sudakov_le_one (intervalIntegral.integral_nonneg hx fun s _ => hK0 s))

/-- At and above the hard scale the first emission has already happened. -/
theorem emissionCdf_of_ge (hK0 : ∀ t, 0 ≤ K t) (hx : T ≤ x) : emissionCdf K T x = 1 := by
  refine min_eq_right ?_
  rw [sudakov, Real.one_le_exp_iff, neg_nonneg, intervalIntegral.integral_symm, neg_nonpos]
  exact intervalIntegral.integral_nonneg hx fun s _ => hK0 s

/-- The Sudakov density is continuous, for a continuous kernel. -/
theorem continuous_sudakov_density (hK : Continuous K) (T : ℝ) :
    Continuous fun t => K t * sudakov K t T :=
  hK.mul (continuous_sudakov hK T)

/-- The Sudakov density is integrable on every interval of scales below a bound: the integral is
a difference of Sudakov factors, hence at most one. -/
theorem integrableOn_sudakov_density (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t) (T x : ℝ) :
    IntegrableOn (fun t => K t * sudakov K t T) (Iic x) := by
  have hcont := continuous_sudakov_density hK T
  refine integrableOn_Iic_of_intervalIntegral_norm_bounded (sudakov K x T) x
    (a := id) (l := atBot) (fun _ => hcont.integrableOn_Ioc) tendsto_id
    (Eventually.of_forall fun y => ?_)
  simp only [id_eq]
  have hnorm : ∫ s in y..x, ‖K s * sudakov K s T‖ = ∫ s in y..x, K s * sudakov K s T :=
    intervalIntegral.integral_congr fun s _ =>
      Real.norm_of_nonneg (sudakov_density_nonneg hK0 T s)
  rw [hnorm, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_sudakov hK s T) (hcont.intervalIntegrable _ _)]
  linarith [sudakov_pos K y T]

/-- **The Sudakov density integrates to the Sudakov factor.** The total emission probability
below the scale `x` is `sudakov K x T`, by the fundamental theorem of calculus on the
left-infinite interval of scales: the primitive is the Sudakov factor, and it vanishes at `-∞`
exactly because the integrated kernel diverges there. -/
theorem setIntegral_Iic_sudakov_density (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) (x : ℝ) :
    ∫ t in Iic x, K t * sudakov K t T = sudakov K x T := by
  have hzero : Tendsto (fun t => sudakov K t T) atBot (𝓝 0) := by
    simpa [sudakov, Function.comp_def] using
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv)
  rw [integral_Iic_of_hasDerivAt_of_tendsto' (fun t _ => hasDerivAt_sudakov hK t T)
    (integrableOn_sudakov_density hK hK0 T x) hzero, sub_zero]

/-- The mass the law of the first emission scale gives to a left-infinite interval, as a
`lintegral` of the Sudakov density over the scales that interval shares with those below the hard
scale. -/
private theorem emissionLaw_Iic_eq_lintegral (K : ℝ → ℝ) (T x : ℝ) :
    emissionLaw K T (Iic x)
      = ∫⁻ t, ENNReal.ofReal (K t * sudakov K t T) ∂volume.restrict (Iic (x ⊓ T)) := by
  rw [emissionLaw, withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Iic]

/-- **The Sudakov factor is the probability of the first emission lying below a scale.** With the
distribution function `emissionCdf`, this holds at every scale: below the hard scale it is the
Sudakov factor, and above it the emission has certainly happened. -/
theorem emissionLaw_Iic (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) (x : ℝ) :
    emissionLaw K T (Iic x) = ENNReal.ofReal (emissionCdf K T x) := by
  have hmass : ∀ y ≤ T, emissionLaw K T (Iic y) = ENNReal.ofReal (sudakov K y T) := by
    intro y hy
    rw [emissionLaw_Iic_eq_lintegral, inf_eq_left.2 hy, ← ofReal_integral_eq_lintegral_ofReal
      (integrableOn_sudakov_density hK hK0 T y)
      (Eventually.of_forall fun t => sudakov_density_nonneg hK0 T t),
      setIntegral_Iic_sudakov_density hK hK0 hdiv y]
  rcases le_or_gt x T with hx | hx
  · rw [hmass x hx, emissionCdf_of_le hK0 hx]
  · -- Above the hard scale the density has no support left, so the interval caps at `T`.
    have hcap : emissionLaw K T (Iic x) = emissionLaw K T (Iic T) := by
      rw [emissionLaw_Iic_eq_lintegral K T x, emissionLaw_Iic_eq_lintegral K T T,
        inf_eq_right.2 hx.le, inf_idem]
    rw [hcap, hmass T le_rfl, sudakov_self, emissionCdf_of_ge hK0 hx.le]

/-- The law of the first emission scale is a probability measure: the emission is certain, which
is what the divergence of the integrated kernel says. -/
theorem isProbabilityMeasure_emissionLaw (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) :
    IsProbabilityMeasure (emissionLaw K T) := by
  refine ⟨?_⟩
  have huniv : emissionLaw K T univ = emissionLaw K T (Iic T) := by
    rw [emissionLaw_Iic_eq_lintegral K T T, inf_idem, emissionLaw,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [huniv, emissionLaw_Iic hK hK0 hdiv T, emissionCdf_of_ge hK0 le_rfl, ENNReal.ofReal_one]

/-- The distribution function of the first emission scale is `emissionCdf`, in the sense of
`ProbabilityTheory.cdf`. -/
theorem cdf_emissionLaw (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) :
    cdf (emissionLaw K T) = emissionCdf K T := by
  have := isProbabilityMeasure_emissionLaw hK hK0 hdiv
  funext x
  rw [← ENNReal.toReal_ofReal (cdf_nonneg _ x), ofReal_cdf, emissionLaw_Iic hK hK0 hdiv x,
    ENNReal.toReal_ofReal (emissionCdf_nonneg K T x)]

/-- **The scale sampler draws the first emission scale.** Any inverse of the Sudakov distribution
function, applied to one uniform variate on `[0, 1]`, has the law of the first emission scale.

This is the specification of the elementary step of a parton shower: the characterisation
`IsQuantileFunction` asks only that `q u` be the least scale whose Sudakov factor reaches `u`, so
an implementation may invert its own kernel in whatever closed form it has. -/
theorem hasLaw_of_isQuantileFunction (hK : Continuous K) (hK0 : ∀ t, 0 ≤ K t)
    (hdiv : Tendsto (fun t => ∫ s in t..T, K s) atBot atTop) {q : ℝ → ℝ}
    (h : IsQuantileFunction (emissionCdf K T) q) :
    HasLaw q (emissionLaw K T) (volume.restrict (Icc (0 : ℝ) 1)) :=
  have := isProbabilityMeasure_emissionLaw hK hK0 hdiv
  h.hasLaw (emissionLaw_Iic hK hK0 hdiv)

/-! ### The constant kernel

The instance where every ingredient is in closed form: a constant emission rate `r`. The
no-emission factor is `exp (-(T - t) r)`, so the sampler is `u ↦ T + log u / r` and the first
emission scale is the hard scale less an exponential variate of rate `r`. -/

variable {r : ℝ}

/-- The integrated constant kernel diverges as the scale falls, so emission is certain. -/
theorem tendsto_integral_const_atBot_atTop (hr : 0 < r) (T : ℝ) :
    Tendsto (fun t => ∫ _s in t..T, r) atBot atTop := by
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  have h : Tendsto (fun t : ℝ => T - t) atBot atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_left atBot T tendsto_neg_atBot_atTop
  exact h.atTop_mul_const hr

/-- `u ↦ T + log u / r` inverts the Sudakov distribution function of a constant kernel of rate
`r`, in closed form: the characterisation is a pair of logarithmic inequalities. -/
theorem isQuantileFunction_emissionCdf_const (hr : 0 < r) (T : ℝ) :
    IsQuantileFunction (emissionCdf (fun _ => r) T) (fun u => T + Real.log u / r) := by
  intro u hu x
  rcases le_or_gt x T with hx | hx
  · have hsud : sudakov (fun _ => r) x T = Real.exp (-((T - x) * r)) := by
      rw [sudakov, intervalIntegral.integral_const, smul_eq_mul]
    rw [emissionCdf_of_le (fun _ => hr.le) hx, hsud, ← Real.log_le_iff_le_exp hu.1,
      show -((T - x) * r) = (x - T) * r by ring, ← div_le_iff₀ hr]
    constructor <;> intro h <;> linarith
  · have hlog : Real.log u / r < 0 := div_neg_of_neg_of_pos (Real.log_neg hu.1 hu.2) hr
    rw [emissionCdf_of_ge (fun _ => hr.le) hx.le]
    exact iff_of_true (by linarith) hu.2.le

/-- **The scale sampler for a constant kernel.** On `[0, 1]` with Lebesgue measure,
`u ↦ T + log u / r` has the law of the first emission scale at constant rate `r`. -/
theorem hasLaw_add_log_div (hr : 0 < r) (T : ℝ) :
    HasLaw (fun u => T + Real.log u / r) (emissionLaw (fun _ => r) T)
      (volume.restrict (Icc (0 : ℝ) 1)) :=
  hasLaw_of_isQuantileFunction continuous_const (fun _ => hr.le)
    (tendsto_integral_const_atBot_atTop hr T) (isQuantileFunction_emissionCdf_const hr T)

end Shower

end QFT

end EpsilonEridani
