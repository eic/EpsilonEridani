/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Probability.ConditionalProbability
public import TauCeti.Probability.Distributions.Uniform.Basic

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

## Main results

* `map_fst_restrict_prod`: the part of a product measure carried by a measurable set, projected
  to the first factor, has density the measure of the slices.
* `map_fst_restrict_prod_uniformMeasure`: thinning by a uniform variate. Keeping a proposal `x`
  when an independent standard uniform variate lies below `a x` multiplies its law by the
  density `min (a x) 1`, clipped at `0`.
* `AcceptReject.map_fst_restrict_acceptSet`: the accepted part of the trial law, projected to
  the proposal, is `μ.withDensity (min f (c * g) / c)`, with no bound and no sign hypothesis.
* `AcceptReject.trialLaw_acceptSet`: the acceptance probability is `∫⁻ min f (c * g) / c`.
* `AcceptReject.acceptedLaw_eq`: the accepted law is `min f (c * g)` normalised.
* `AcceptReject.acceptedLaw_eq_of_ae_le` and `AcceptReject.measureReal_trialLaw_acceptSet`:
  when `f ≤ c * g` almost everywhere, the accepted law is `f` normalised and the acceptance
  probability is `(∫ f) / c`.
* `AcceptReject.acceptedLaw_ne_of_violation`: the silent bias. When the bound fails on a set of
  positive measure and holds on a set of positive measure where `f` is positive, the accepted
  law is not `f` normalised. The second hypothesis cannot be dropped: for `f = 2 * g` and
  `c = 1` the bound fails everywhere, every proposal is accepted, and the accepted law is
  nevertheless `f` normalised.

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

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The part of a product measure carried by a measurable set `s`, pushed forward to the first
factor, is the first factor with density `x ↦ ρ (Prod.mk x ⁻¹' s)`, the measure of the slice of
`s` above `x`. -/
theorem map_fst_restrict_prod (ν : Measure α) (ρ : Measure β) [SFinite ρ] {s : Set (α × β)}
    (hs : MeasurableSet s) :
    ((ν.prod ρ).restrict s).map Prod.fst = ν.withDensity fun x => ρ (Prod.mk x ⁻¹' s) := by
  ext t ht
  rw [Measure.map_apply measurable_fst ht, Measure.restrict_apply (measurable_fst ht),
    Measure.prod_apply ((measurable_fst ht).inter hs), withDensity_apply _ ht,
    ← lintegral_indicator ht]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ t <;> simp [hx, Set.preimage_inter, Set.preimage_preimage]

/-- The uniform measure of a closed lower tail: the fraction of `Set.Ioc a b` lying below `t`,
which is `0` below the interval and `1` above it. -/
theorem uniformMeasure_Iic {a b : ℝ} (hab : a < b) (t : ℝ) :
    uniformMeasure a b (Set.Iic t) = ENNReal.ofReal ((min t b - a) / (b - a)) := by
  have hset : Set.Iic t ∩ Set.Ioc a b = Set.Ioc a (min t b) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc, le_min_iff]
    tauto
  rw [uniformMeasure_apply measurableSet_Iic, hset, Real.volume_Ioc,
    ENNReal.ofReal_div_of_pos (sub_pos.mpr hab), ENNReal.div_eq_inv_mul]

/-- **Thinning by a uniform variate.** Draw `x` from `ν` and an independent standard uniform
variate `u`, and keep `x` when `u ≤ a x`. The kept part of the law of `x` is `ν` with density
`min (a x) 1`, read as `0` where `a x` is negative. -/
theorem map_fst_restrict_prod_uniformMeasure (ν : Measure α) {a : α → ℝ} (ha : Measurable a) :
    ((ν.prod (uniformMeasure 0 1)).restrict {p | p.2 ≤ a p.1}).map Prod.fst =
      ν.withDensity fun x => ENNReal.ofReal (min (a x) 1) := by
  have hs : MeasurableSet {p : α × ℝ | p.2 ≤ a p.1} :=
    measurableSet_le measurable_snd (ha.comp measurable_fst)
  rw [map_fst_restrict_prod ν _ hs]
  congr 1
  funext x
  have hslice : Prod.mk x ⁻¹' {p : α × ℝ | p.2 ≤ a p.1} = Set.Iic (a x) := by
    ext u
    simp
  rw [hslice, uniformMeasure_Iic zero_lt_one]
  simp

namespace AcceptReject

/-- The joint law of one acceptance–rejection trial: a proposal `x` with density `g` against
`μ`, and an independent uniform variate `u` on `[0, 1]`. Negative values of `g` are read
as `0`. -/
def trialLaw (μ : Measure α) (g : α → ℝ) : Measure (α × ℝ) :=
  (μ.withDensity fun x => ENNReal.ofReal (g x)).prod (uniformMeasure 0 1)

theorem trialLaw_def (μ : Measure α) (g : α → ℝ) :
    trialLaw μ g = (μ.withDensity fun x => ENNReal.ofReal (g x)).prod (uniformMeasure 0 1) :=
  (rfl)

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

/-- The accepted law is a probability measure as soon as acceptance has positive, finite
probability. -/
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
  rw [trialLaw_def, acceptSet, map_fst_restrict_prod_uniformMeasure _ hratio,
    ← withDensity_mul _ (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  -- The proposal density times the probability of acceptance is `min f (c * g) / c`.
  rw [Pi.mul_apply]
  rcases le_or_gt (g x) 0 with hgx | hgx
  · rw [ENNReal.ofReal_of_nonpos hgx, zero_mul, ENNReal.ofReal_of_nonpos]
    exact div_nonpos_of_nonpos_of_nonneg
      ((min_le_right _ _).trans (mul_nonpos_of_nonneg_of_nonpos hc.le hgx)) hc.le
  · rw [← ENNReal.ofReal_mul hgx.le, mul_min_of_nonneg _ _ hgx.le, ← min_div_div_right hc.le]
    congr 2 <;> field_simp

/-- **The acceptance probability** of one trial is `∫⁻ min f (c * g) / c`. -/
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
  rw [acceptedLaw_def, ProbabilityTheory.cond, Measure.map_smul,
    map_fst_restrict_acceptSet hc hf hg, trialLaw_acceptSet hc hf hg, hden,
    withDensity_smul _ (by fun_prop), smul_smul,
    ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top) (Or.inl hC₀), div_eq_mul_inv, mul_comm,
    ← mul_assoc, ENNReal.inv_mul_cancel hC₀ ENNReal.ofReal_ne_top, one_mul]
  exact measurable_fst.aemeasurable

/-- **Acceptance–rejection has the right law.** When `f ≤ c * g` almost everywhere, the accepted
variate has the law `f` normalised against `μ`. -/
theorem acceptedLaw_eq_of_ae_le (hc : 0 < c) (hf : Measurable f) (hg : Measurable g)
    (hle : ∀ᵐ x ∂μ, f x ≤ c * g x) :
    acceptedLaw μ f g c = (∫⁻ x, ENNReal.ofReal (f x) ∂μ)⁻¹ •
      μ.withDensity fun x => ENNReal.ofReal (f x) := by
  have h : (fun x => ENNReal.ofReal (min (f x) (c * g x))) =ᵐ[μ]
      fun x => ENNReal.ofReal (f x) := hle.mono fun x hx => by simp only [min_eq_left hx]
  rw [acceptedLaw_eq hc hf hg, lintegral_congr_ae h, withDensity_congr_ae h]

/-- When `f ≤ c * g` almost everywhere, the acceptance probability is `∫⁻ f / c`. -/
theorem trialLaw_acceptSet_of_ae_le (hc : 0 < c) (hf : Measurable f) (hg : Measurable g)
    (hle : ∀ᵐ x ∂μ, f x ≤ c * g x) :
    trialLaw μ g (acceptSet f g c) = (∫⁻ x, ENNReal.ofReal (f x) ∂μ) / ENNReal.ofReal c := by
  rw [trialLaw_acceptSet hc hf hg]
  congr 1
  exact lintegral_congr_ae (hle.mono fun x hx => by simp only [min_eq_left hx])

/-- **The acceptance probability is `(∫ f) / c`** for an integrable, almost everywhere
non-negative target dominated almost everywhere by `c * g`. -/
theorem measureReal_trialLaw_acceptSet (hc : 0 < c) (hf : Measurable f) (hg : Measurable g)
    (hle : ∀ᵐ x ∂μ, f x ≤ c * g x) (hf₀ : 0 ≤ᵐ[μ] f) (hfi : Integrable f μ) :
    (trialLaw μ g).real (acceptSet f g c) = (∫ x, f x ∂μ) / c := by
  rw [measureReal_def, trialLaw_acceptSet_of_ae_le hc hf hg hle,
    ← ofReal_integral_eq_lintegral_ofReal hfi hf₀, ← ENNReal.ofReal_div_of_pos hc,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg_of_ae hf₀) hc.le)]

/-- **The silent bias.** Suppose the bound `f ≤ c * g` fails on a set of positive measure, and
holds on a set of positive measure where `f` is positive. Then the accepted law is not `f`
normalised: by `acceptedLaw_eq` it is `min f (c * g)` normalised, and the two differ.

Both hypotheses are needed. For `f = 2 * g` and `c = 1` the bound fails wherever `g` is
positive, yet every proposal is accepted and the accepted law is `g` normalised, which is `f`
normalised. -/
theorem acceptedLaw_ne_of_violation (hc : 0 < c) (hf : Measurable f) (hg : Measurable g)
    (hg₀ : 0 ≤ᵐ[μ] g) (hfi : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ∞)
    (hviol : μ {x | c * g x < f x} ≠ 0) (hresp : μ {x | 0 < f x ∧ f x ≤ c * g x} ≠ 0) :
    acceptedLaw μ f g c ≠ (∫⁻ x, ENNReal.ofReal (f x) ∂μ)⁻¹ •
      μ.withDensity fun x => ENNReal.ofReal (f x) := by
  set m : α → ℝ≥0∞ := fun x => ENNReal.ofReal (min (f x) (c * g x)) with hm_def
  set F : α → ℝ≥0∞ := fun x => ENNReal.ofReal (f x) with hF_def
  have hmF : ∀ x, m x ≤ F x := fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)
  have hS : MeasurableSet {x | 0 < f x ∧ f x ≤ c * g x} :=
    (measurableSet_lt measurable_const hf).inter (measurableSet_le hf (hg.const_mul c))
  -- The target mass on the set where the bound holds is positive and finite.
  have hX₀ : ∫⁻ x in {x | 0 < f x ∧ f x ≤ c * g x}, F x ∂μ ≠ 0 := by
    rw [Ne, setLIntegral_eq_zero_iff hS (by fun_prop)]
    refine fun h => hresp (measure_eq_zero_iff_ae_notMem.mpr ?_)
    filter_upwards [h] with x hx hxS
    exact (ENNReal.ofReal_pos.mpr hxS.1).ne' (hx hxS)
  have hXfin : ∫⁻ x in {x | 0 < f x ∧ f x ≤ c * g x}, F x ∂μ ≠ ∞ :=
    ne_top_of_le_ne_top hfi (setLIntegral_le_lintegral _ _)
  -- The thinned mass is strictly smaller than the target mass.
  have hlt : ∫⁻ x, m x ∂μ < ∫⁻ x, F x ∂μ := by
    refine lintegral_strict_mono_of_ae_le_of_frequently_ae_lt (by fun_prop)
      (ne_top_of_le_ne_top hfi (lintegral_mono hmF)) (ae_of_all _ hmF) fun hall => hviol ?_
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hall, hg₀] with x hx hgx hxV
    have hcg : 0 ≤ c * g x := mul_nonneg hc.le hgx
    simp only [hm_def, hF_def, not_not, min_eq_right hxV.le] at hx
    exact hxV.ne ((ENNReal.ofReal_eq_ofReal_iff hcg (hcg.trans hxV.le)).mp hx)
  intro h
  rw [acceptedLaw_eq hc hf hg] at h
  -- Evaluating both sides on the set where the bound holds forces the two masses to agree.
  have hS_eq := congrArg (· {x | 0 < f x ∧ f x ≤ c * g x}) h
  simp only [Measure.smul_apply, smul_eq_mul, withDensity_apply _ hS] at hS_eq
  have hSm : ∫⁻ x in {x | 0 < f x ∧ f x ≤ c * g x}, ENNReal.ofReal (min (f x) (c * g x)) ∂μ =
      ∫⁻ x in {x | 0 < f x ∧ f x ≤ c * g x}, F x ∂μ :=
    setLIntegral_congr_fun hS fun x hx => by simp only [hF_def, min_eq_left hx.2]
  rw [hSm] at hS_eq
  have hinv := (ENNReal.mul_left_inj hX₀ hXfin).mp hS_eq
  exact hlt.ne (inv_injective hinv)

/-- A uniform proposal on `[0, 1]` with the constant bound `1` accepts the target
`(1 + z ^ 2) / 2` with probability `2 / 3`, its integral over the interval. The target is the
ratio of the quark splitting kernel `(1 + z ^ 2) / (1 - z)` to its overestimate `2 / (1 - z)`. -/
theorem measureReal_trialLaw_acceptSet_one_add_sq_div_two :
    (trialLaw (uniformMeasure 0 1) fun _ => 1).real
      (acceptSet (fun z => (1 + z ^ 2) / 2) (fun _ => 1) 1) = 2 / 3 := by
  have hunif : uniformMeasure 0 1 = volume.restrict (Set.Ioc 0 1) := by
    simp [uniformMeasure_eq_smul]
  have hle : ∀ᵐ z ∂uniformMeasure 0 1, (1 + z ^ 2) / 2 ≤ 1 * 1 := by
    filter_upwards [ae_mem_Ioc_uniformMeasure] with z hz
    nlinarith [hz.1, hz.2]
  have hfi : Integrable (fun z : ℝ => (1 + z ^ 2) / 2) (uniformMeasure 0 1) := by
    rw [hunif]
    exact (by fun_prop : Continuous fun z : ℝ => (1 + z ^ 2) / 2).integrableOn_Icc.mono_set
      Set.Ioc_subset_Icc_self
  rw [measureReal_trialLaw_acceptSet one_pos (by fun_prop) measurable_const hle
    (ae_of_all _ fun z => by positivity) hfi, hunif,
    ← intervalIntegral.integral_of_le zero_le_one]
  norm_num [intervalIntegral.integral_div, integral_pow]

end AcceptReject

end EpsilonEridani
