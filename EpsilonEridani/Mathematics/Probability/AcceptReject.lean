/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Probability.ConditionalProbability
public import EpsilonEridani.Mathematics.Probability.Distributions.Uniform.Basic

/-!
# Acceptance–rejection sampling

The acceptance–rejection method draws from a target density `f` using a proposal density `g`
it can already sample and a constant `c > 0`: draw `x` from `g`, draw an independent uniform
variate `u` on `[0, 1]`, and accept `x` when `u ≤ f x / (c * g x)`. This file states what that
construction produces as a theorem about measures.

One trial is a point `(x, u)` distributed according to `trialLaw μ g`, the product of the
proposal law `μ.withDensity g` with the standard uniform law
`TauCeti.Probability.uniformMeasure 0 1`. The event that the trial is accepted is
`acceptSet f g c`, and the law of the accepted variate is `acceptedLaw μ f g c`, the first
marginal of the trial law conditioned on acceptance.

Nothing here assumes that `g` is normalised against `μ`, so the trial law's measure of the
acceptance event is a mass, not necessarily a probability. It is the acceptance probability
exactly when the proposal law `μ.withDensity g` is a probability measure, in which case the
trial law is one too.

## Main results

* `AcceptReject.map_fst_restrict_acceptSet`: the accepted part of the trial law, projected to
  the proposal, is `μ.withDensity (min f (c * g) / c)`, with no bound and no sign hypothesis.
* `AcceptReject.trialLaw_acceptSet`: the trial law's measure of the acceptance event is
  `∫⁻ min f (c * g) / c`.
* `AcceptReject.acceptedLaw_eq`: the accepted law is `min f (c * g)` normalised.
* `AcceptReject.acceptedLaw_eq_of_ae_le`: when `f ≤ c * g` almost everywhere, the accepted law is
  `f` normalised.
* `AcceptReject.measureReal_trialLaw_acceptSet_of_ae_le`: for an integrable, almost everywhere
  non-negative target with `f ≤ c * g` almost everywhere, the trial law's measure of the
  acceptance event is `(∫ f) / c`.
* `AcceptReject.acceptedLaw_ne_of_measure_setOf_lt_ne_zero`: the silent bias. For an almost
  everywhere non-negative proposal and a target of finite mass, when the bound fails on a set of
  positive measure and holds on a set of positive measure where `f` is positive, the accepted law
  is not `f` normalised. The second set hypothesis cannot be dropped: for `f = 2 * g` and `c = 1`
  the bound fails wherever `g` is positive, every proposal is accepted, and the accepted law is
  nevertheless `f` normalised.
* `AcceptReject.acceptedLaw_one_add_sq_div_two` and
  `AcceptReject.measureReal_trialLaw_acceptSet_one_add_sq_div_two`: a uniform proposal on
  `[0, 1]` with bound `1` accepts the target `(1 + z ^ 2) / 2` with probability `2 / 3`, and the
  accepted law is the target normalised.
* `AcceptReject.acceptedLaw_two_mul_eq_min`: a bound that is too small. Sampling `2 * z` on `[0, 1]`
  against the bound `3 / 2` yields `min (2 * z) (3 / 2)` normalised, of mass `15 / 16`.

The bound hypothesis is taken almost everywhere. A bound checked at every point, which is what
an implementation can verify, is the case `Filter.Eventually.of_forall`.

## References

* J. von Neumann, "Various techniques used in connection with random digits", National Bureau
  of Standards Applied Mathematics Series 12 (1951) 36.
* L. Devroye, *Non-Uniform Random Variate Generation*, Springer (1986), §II.3.
-/

public section

noncomputable section

namespace EpsilonEridani

open MeasureTheory ProbabilityTheory TauCeti.Probability

open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

namespace AcceptReject

/-- The joint law of one acceptance–rejection trial: a proposal `x` with density `g` against
`μ`, and an independent uniform variate `u` on `[0, 1]`. Negative values of `g` are read
as `0`. When `μ.withDensity g` is a probability measure, so is the trial law. -/
def trialLaw (μ : Measure α) (g : α → ℝ) : Measure (α × ℝ) :=
  (μ.withDensity fun x => ENNReal.ofReal (g x)).prod (uniformMeasure 0 1)

theorem trialLaw_def (μ : Measure α) (g : α → ℝ) :
    trialLaw μ g = (μ.withDensity fun x => ENNReal.ofReal (g x)).prod (uniformMeasure 0 1) :=
  (rfl)

/-- A probability proposal law gives a probability trial law. -/
instance isProbabilityMeasure_trialLaw (μ : Measure α) (g : α → ℝ)
    [IsProbabilityMeasure (μ.withDensity fun x => ENNReal.ofReal (g x))] :
    IsProbabilityMeasure (trialLaw μ g) := by
  have := isProbabilityMeasure_uniformMeasure (zero_lt_one' ℝ)
  rw [trialLaw_def]
  infer_instance

/-- The proposal is the first marginal of the trial law. -/
@[simp]
theorem map_fst_trialLaw (μ : Measure α) (g : α → ℝ) :
    (trialLaw μ g).map Prod.fst = μ.withDensity fun x => ENNReal.ofReal (g x) := by
  simp [trialLaw_def]

/-- The acceptance event of a trial with target `f`, proposal `g` and bound constant `c`: the
uniform variate lies below the acceptance ratio `f x / (c * g x)`. -/
def acceptSet (f g : α → ℝ) (c : ℝ) : Set (α × ℝ) :=
  {p | p.2 ≤ f p.1 / (c * g p.1)}

omit [MeasurableSpace α] in
theorem acceptSet_def (f g : α → ℝ) (c : ℝ) :
    acceptSet f g c = {p : α × ℝ | p.2 ≤ f p.1 / (c * g p.1)} :=
  (rfl)

omit [MeasurableSpace α] in
@[simp]
theorem mem_acceptSet {f g : α → ℝ} {c : ℝ} {p : α × ℝ} :
    p ∈ acceptSet f g c ↔ p.2 ≤ f p.1 / (c * g p.1) :=
  Iff.rfl

@[measurability]
theorem measurableSet_acceptSet {f g : α → ℝ} (c : ℝ) (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet (acceptSet f g c) :=
  measurableSet_le measurable_snd
    ((hf.comp measurable_fst).div ((hg.comp measurable_fst).const_mul c))

/-- The law of the accepted variate: the proposal marginal of the trial law conditioned on the
acceptance event. -/
def acceptedLaw (μ : Measure α) (f g : α → ℝ) (c : ℝ) : Measure α :=
  ((trialLaw μ g)[|acceptSet f g c]).map Prod.fst

theorem acceptedLaw_def (μ : Measure α) (f g : α → ℝ) (c : ℝ) :
    acceptedLaw μ f g c = ((trialLaw μ g)[|acceptSet f g c]).map Prod.fst :=
  (rfl)

/-- The accepted law is a probability measure as soon as the trial law gives the acceptance
event positive, finite measure. -/
theorem isProbabilityMeasure_acceptedLaw {μ : Measure α} {f g : α → ℝ} {c : ℝ}
    (h₀ : trialLaw μ g (acceptSet f g c) ≠ 0) (hfin : trialLaw μ g (acceptSet f g c) ≠ ∞) :
    IsProbabilityMeasure (acceptedLaw μ f g c) := by
  have := cond_isProbabilityMeasure_of_finite h₀ hfin
  rw [acceptedLaw_def]
  infer_instance

variable {μ : Measure α} {f g : α → ℝ} {c : ℝ}

/-- **The accepted part of a trial.** The trials that are accepted, projected to their proposal,
form the measure `μ` with density `min f (c * g) / c`. No bound and no sign hypothesis on `f`
or `g` is needed. -/
theorem map_fst_restrict_acceptSet (hc : 0 < c) (hf : Measurable f) (hg : Measurable g) :
    ((trialLaw μ g).restrict (acceptSet f g c)).map Prod.fst =
      μ.withDensity fun x => ENNReal.ofReal (min (f x) (c * g x) / c) := by
  have hratio : Measurable fun x => f x / (c * g x) := hf.div (hg.const_mul c)
  rw [trialLaw_def, acceptSet_def,
    Measure.map_fst_restrict_setOf_le_prod_uniformMeasure (a := fun x => f x / (c * g x)) _ hratio,
    ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  -- The proposal density times the probability of acceptance is `min f (c * g) / c`.
  rw [Pi.mul_apply]
  rcases le_or_gt (g x) 0 with hgx | hgx
  · rw [ENNReal.ofReal_of_nonpos hgx, zero_mul, ENNReal.ofReal_of_nonpos]
    exact div_nonpos_of_nonpos_of_nonneg
      ((min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos hc.le hgx)) hc.le
  · have hacc : g x * (f x / (c * g x)) = f x / c := by field_simp
    have hcap : g x * 1 = c * g x / c := by field_simp
    rw [← ENNReal.ofReal_mul hgx.le, mul_min_of_nonneg _ _ hgx.le, hacc, hcap,
      min_div_div_right hc.le]

/-- The trial law's measure of the acceptance event is `∫⁻ min f (c * g) / c`; it is the
**acceptance probability** when the proposal law is a probability measure. -/
theorem trialLaw_acceptSet (hc : 0 < c) (hf : Measurable f) (hg : Measurable g) :
    trialLaw μ g (acceptSet f g c) =
      (∫⁻ x, ENNReal.ofReal (min (f x) (c * g x)) ∂μ) / ENNReal.ofReal c := by
  have h := congrArg (· Set.univ) (map_fst_restrict_acceptSet (μ := μ) hc hf hg)
  simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ,
    Measure.restrict_apply_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h
  rw [h, ENNReal.div_eq_inv_mul, ← lintegral_const_mul' _ _ (by simpa using hc)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.div_eq_inv_mul]

/-- **The law of acceptance–rejection.** The accepted variate has the law `min f (c * g)`
normalised against `μ`, whatever the relation between `f` and `c * g`. -/
theorem acceptedLaw_eq (hc : 0 < c) (hf : Measurable f) (hg : Measurable g) :
    acceptedLaw μ f g c = (∫⁻ x, ENNReal.ofReal (min (f x) (c * g x)) ∂μ)⁻¹ •
      μ.withDensity fun x => ENNReal.ofReal (min (f x) (c * g x)) := by
  have hC₀ : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have hden : (fun x => ENNReal.ofReal (min (f x) (c * g x) / c)) =
      (ENNReal.ofReal c)⁻¹ • fun x => ENNReal.ofReal (min (f x) (c * g x)) := by
    funext x
    rw [Pi.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos hc, ENNReal.div_eq_inv_mul]
  -- Normalising by the accepted mass `M / c` undoes the factor `1 / c` in the density.
  have hscalar : ((∫⁻ x, ENNReal.ofReal (min (f x) (c * g x)) ∂μ) / ENNReal.ofReal c)⁻¹ *
      (ENNReal.ofReal c)⁻¹ = (∫⁻ x, ENNReal.ofReal (min (f x) (c * g x)) ∂μ)⁻¹ := by
    rw [ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hC₀), div_eq_mul_inv, mul_comm,
      ← mul_assoc, ENNReal.inv_mul_cancel hC₀ ENNReal.ofReal_ne_top, one_mul]
  rw [acceptedLaw_def, ProbabilityTheory.cond, Measure.map_smul _ measurable_fst.aemeasurable,
    map_fst_restrict_acceptSet hc hf hg, trialLaw_acceptSet hc hf hg, hden,
    withDensity_smul _ (by fun_prop), smul_smul, hscalar]

/-- **Acceptance–rejection has the right law.** When `f ≤ c * g` almost everywhere, the accepted
variate has the law `f` normalised against `μ`. -/
theorem acceptedLaw_eq_of_ae_le (hc : 0 < c) (hf : Measurable f) (hg : Measurable g)
    (hle : ∀ᵐ x ∂μ, f x ≤ c * g x) :
    acceptedLaw μ f g c = (∫⁻ x, ENNReal.ofReal (f x) ∂μ)⁻¹ •
      μ.withDensity fun x => ENNReal.ofReal (f x) := by
  have h : (fun x => ENNReal.ofReal (min (f x) (c * g x))) =ᵐ[μ]
      fun x => ENNReal.ofReal (f x) := hle.mono fun x hx => by simp only [min_eq_left hx]
  rw [acceptedLaw_eq hc hf hg, lintegral_congr_ae h, withDensity_congr_ae h]

/-- When `f ≤ c * g` almost everywhere, the trial law's measure of the acceptance event is
`∫⁻ f / c`. -/
theorem trialLaw_acceptSet_of_ae_le (hc : 0 < c) (hf : Measurable f) (hg : Measurable g)
    (hle : ∀ᵐ x ∂μ, f x ≤ c * g x) :
    trialLaw μ g (acceptSet f g c) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / ENNReal.ofReal c := by
  rw [trialLaw_acceptSet hc hf hg]
  congr 1
  exact lintegral_congr_ae (hle.mono fun x hx => by simp only [min_eq_left hx])

/-- When `f ≤ c * g` almost everywhere and the target has positive, finite mass, the accepted
law is a probability measure. -/
theorem isProbabilityMeasure_acceptedLaw_of_ae_le (hc : 0 < c) (hf : Measurable f)
    (hg : Measurable g) (hle : ∀ᵐ x ∂μ, f x ≤ c * g x)
    (h₀ : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ 0) (hfin : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞) :
    IsProbabilityMeasure (acceptedLaw μ f g c) := by
  refine isProbabilityMeasure_acceptedLaw ?_ ?_ <;> rw [trialLaw_acceptSet_of_ae_le hc hf hg hle]
  · exact ENNReal.div_ne_zero.mpr ⟨h₀, ENNReal.ofReal_ne_top⟩
  · exact ENNReal.div_ne_top hfin (by simpa using hc)

/-- For an integrable, almost everywhere non-negative target dominated almost everywhere by
`c * g`, the trial law's measure of the acceptance event is `(∫ f) / c`. -/
theorem measureReal_trialLaw_acceptSet_of_ae_le (hc : 0 < c) (hf : Measurable f)
    (hg : Measurable g) (hle : ∀ᵐ x ∂μ, f x ≤ c * g x) (hf₀ : 0 ≤ᵐ[μ] f)
    (hfi : Integrable f μ) :
    (trialLaw μ g).real (acceptSet f g c) = (∫ x, f x ∂μ) / c := by
  rw [measureReal_def, trialLaw_acceptSet_of_ae_le hc hf hg hle,
    ← ofReal_integral_eq_lintegral_ofReal hfi hf₀, ← ENNReal.ofReal_div_of_pos hc,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg_of_ae hf₀) hc.le)]

/-- **The silent bias.** Let the proposal `g` be almost everywhere non-negative and the target
`f` have finite mass `∫⁻ f`. Suppose the bound `f ≤ c * g` fails on a set of positive measure,
and holds on a set of positive measure where `f` is positive. Then the accepted law is not `f`
normalised: by `acceptedLaw_eq` it is `min f (c * g)` normalised, and the two differ.

Both set hypotheses are needed. Without the first, the bound holds almost everywhere and
`acceptedLaw_eq_of_ae_le` gives equality. Without the second, take `f = 2 * g` and `c = 1`: the
bound fails wherever `g` is positive, yet every proposal is accepted and the accepted law is `g`
normalised, which is `f` normalised. -/
theorem acceptedLaw_ne_of_measure_setOf_lt_ne_zero (hc : 0 < c) (hf : Measurable f)
    (hg : Measurable g) (hg₀ : 0 ≤ᵐ[μ] g) (hfi : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞)
    (hviol : μ {x | c * g x < f x} ≠ 0) (hresp : μ {x | 0 < f x ∧ f x ≤ c * g x} ≠ 0) :
    acceptedLaw μ f g c ≠ (∫⁻ x, ENNReal.ofReal (f x) ∂μ)⁻¹ •
      μ.withDensity fun x => ENNReal.ofReal (f x) := by
  set S := {x | 0 < f x ∧ f x ≤ c * g x} with hS_def
  have hmF : ∀ x, ENNReal.ofReal (min (f x) (c * g x)) ≤ ENNReal.ofReal (f x) :=
    fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const hf).inter (measurableSet_le hf (hg.const_mul c))
  -- The target mass on the set where the bound holds is positive and finite.
  have hX₀ : ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ ≠ 0 := by
    rw [Ne, setLIntegral_eq_zero_iff hS (by fun_prop)]
    refine fun h => hresp (measure_eq_zero_iff_ae_notMem.mpr ?_)
    filter_upwards [h] with x hx hxS
    exact (ENNReal.ofReal_pos.mpr hxS.1).ne' (hx hxS)
  have hXfin : ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hfi (setLIntegral_le_lintegral _ _)
  -- On the violation set, where `c * g < f`, the thinned density `min f (c * g)` is strictly
  -- below `f`.
  have hlt : ∫⁻ x, ENNReal.ofReal (min (f x) (c * g x)) ∂μ < ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    refine lintegral_strict_mono_of_ae_le_of_ae_lt_on (by fun_prop)
      (ne_top_of_le_ne_top hfi (lintegral_mono hmF)) (ae_of_all _ hmF) hviol ?_
    filter_upwards [hg₀] with x hgx hxV
    rw [min_eq_right (le_of_lt hxV)]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (mul_nonneg hc.le hgx)).mpr hxV
  intro h
  rw [acceptedLaw_eq hc hf hg] at h
  -- Evaluating both sides on the set where the bound holds forces the two masses to agree.
  have hS_eq := congrArg (· S) h
  simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hS] at hS_eq
  have hSm : ∫⁻ x in S, ENNReal.ofReal (min (f x) (c * g x)) ∂μ =
      ∫⁻ x in S, ENNReal.ofReal (f x) ∂μ :=
    setLIntegral_congr_fun hS fun x hx => by rw [min_eq_left hx.2]
  rw [hSm] at hS_eq
  have hinv := (ENNReal.mul_left_inj hX₀ hXfin).mp hS_eq
  exact hlt.ne (inv_injective hinv)

/-- The target `(1 + z ^ 2) / 2` is bounded by `1` on `[0, 1]`, written `1 * 1` to match the
bound `c * g x` at `c = 1` and `g = fun _ => 1`. -/
private theorem ae_one_add_sq_div_two_le :
    ∀ᵐ z ∂uniformMeasure 0 1, (1 + z ^ 2) / 2 ≤ 1 * 1 := by
  filter_upwards [ae_mem_Ioc_uniformMeasure] with z hz
  nlinarith [hz.1, hz.2]

/-- The target `(1 + z ^ 2) / 2` has integral `2 / 3` over `[0, 1]`. -/
private theorem lintegral_one_add_sq_div_two :
    ∫⁻ z, ENNReal.ofReal ((1 + z ^ 2) / 2) ∂uniformMeasure 0 1 = ENNReal.ofReal (2 / 3) := by
  have hfi : Integrable (fun z : ℝ => (1 + z ^ 2) / 2) (uniformMeasure 0 1) :=
    (by fun_prop : Continuous fun z : ℝ => (1 + z ^ 2) / 2).integrable_uniformMeasure
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun z => by positivity),
    uniformMeasure_zero_one, ← intervalIntegral.integral_of_le zero_le_one]
  norm_num [intervalIntegral.integral_div, integral_pow]

/-- A uniform proposal on `[0, 1]` with the constant bound `1` accepts the target
`(1 + z ^ 2) / 2` with probability `2 / 3`, its integral over the interval. The target is the
ratio of the quark splitting kernel `(1 + z ^ 2) / (1 - z)` to its overestimate `2 / (1 - z)`. -/
theorem measureReal_trialLaw_acceptSet_one_add_sq_div_two :
    (trialLaw (uniformMeasure 0 1) fun _ => 1).real
      (acceptSet (fun z => (1 + z ^ 2) / 2) (fun _ => 1) 1) = 2 / 3 := by
  rw [measureReal_def, trialLaw_acceptSet_of_ae_le one_pos (by fun_prop) measurable_const
    ae_one_add_sq_div_two_le, lintegral_one_add_sq_div_two, ENNReal.ofReal_one, div_one,
    ENNReal.toReal_ofReal (by norm_num)]

/-- A uniform proposal on `[0, 1]` with the constant bound `1` produces the target
`(1 + z ^ 2) / 2` normalised by its integral `2 / 3`. -/
theorem acceptedLaw_one_add_sq_div_two :
    acceptedLaw (uniformMeasure 0 1) (fun z => (1 + z ^ 2) / 2) (fun _ => 1) 1 =
      (ENNReal.ofReal (2 / 3))⁻¹ •
        (uniformMeasure 0 1).withDensity fun z => ENNReal.ofReal ((1 + z ^ 2) / 2) := by
  rw [acceptedLaw_eq_of_ae_le one_pos (by fun_prop) measurable_const ae_one_add_sq_div_two_le,
    lintegral_one_add_sq_div_two]

/-- The clipped target `min (2 * z) (3 / 2)` has integral `15 / 16` over `[0, 1]`. -/
private theorem lintegral_min_two_mul :
    ∫⁻ z, ENNReal.ofReal (min (2 * z) (3 / 2)) ∂uniformMeasure 0 1 = ENNReal.ofReal (15 / 16) := by
  have hcont : Continuous fun z : ℝ => min (2 * z) (3 / 2) := by fun_prop
  have hfi : Integrable (fun z : ℝ => min (2 * z) (3 / 2)) (uniformMeasure 0 1) :=
    hcont.integrable_uniformMeasure
  have hf₀ : 0 ≤ᵐ[uniformMeasure 0 1] fun z : ℝ => min (2 * z) (3 / 2) := by
    filter_upwards [ae_mem_Ioc_uniformMeasure] with z hz
    rw [Pi.zero_apply]
    exact le_min (by linarith [hz.1]) (by norm_num)
  -- Split `[0, 1]` at the crossing point `3 / 4`, where `2 * z` meets the bound.
  have hlo : ∫ z in (0 : ℝ)..3 / 4, min (2 * z) (3 / 2) = ∫ z in (0 : ℝ)..3 / 4, 2 * z :=
    intervalIntegral.integral_congr fun z hz => by
      rw [Set.uIcc_of_le (by norm_num)] at hz
      exact min_eq_left (by linarith [hz.2])
  have hhi : ∫ z in (3 / 4 : ℝ)..1, min (2 * z) (3 / 2) = ∫ _ in (3 / 4 : ℝ)..1, (3 / 2 : ℝ) :=
    intervalIntegral.integral_congr fun z hz => by
      rw [Set.uIcc_of_le (by norm_num)] at hz
      exact min_eq_right (by linarith [hz.1])
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hf₀, uniformMeasure_zero_one,
    ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 3 / 4)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), hlo, hhi,
    intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
  norm_num

/-- **A bound that is too small.** Sampling the target `2 * z` on `[0, 1]` from a uniform
proposal against the bound `3 / 2`, which `2 * z` exceeds above `z = 3 / 4`, produces the
clipped target `min (2 * z) (3 / 2)` normalised by its integral `15 / 16`. -/
theorem acceptedLaw_two_mul_eq_min :
    acceptedLaw (uniformMeasure 0 1) (fun z => 2 * z) (fun _ => 1) (3 / 2) =
      (ENNReal.ofReal (15 / 16))⁻¹ •
        (uniformMeasure 0 1).withDensity fun z => ENNReal.ofReal (min (2 * z) (3 / 2)) := by
  rw [acceptedLaw_eq (by norm_num) (by fun_prop) measurable_const]
  simp only [mul_one]
  rw [lintegral_min_two_mul]

end AcceptReject

end EpsilonEridani
