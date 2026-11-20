/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Path-length functionals of a medium

A parton produced at a point `x` of a nucleus and moving in a direction `v` traverses the nuclear
medium along the ray `s ↦ x + s • v`, `s ≥ 0`. Two functionals measure how much medium it
traverses.

* The *geometric path length* `geometricPathLength S x v` is the length of the part of the ray that
  lies in the set `S`, which is the support of the nuclear density: the Lebesgue measure of
  `{s | 0 ≤ s ∧ x + s • v ∈ S}`. For a convex support containing the production point this is the
  distance from `x` to the boundary of `S` along the ray (`geometricPathLength_eq_sSup`).
* The *density-weighted path length* `densityWeightedPathLength ρ ρ₀ x v` is the integral of the
  density `ρ` along the ray, divided by the central density `ρ₀`: the length of uniform medium of
  density `ρ₀` with the same number of nucleons per unit area along the ray.

For a uniform medium the two are proportional, with constant the ratio of the density to the
central density (`densityWeightedPathLength_indicator_const`). For a general bounded profile the
density-weighted length is only bounded by the ratio of the maximal to the central density times
the geometric one (`densityWeightedPathLength_le`). Local quantities per unit path length, such as
transport coefficients, pair with the density-weighted length, while an absorption factor that
depends only on whether the hadron forms inside the nucleus pairs with the geometric one.

The ambient space is any real normed space; the physical case is three-dimensional space with
`‖v‖ = 1`.

## Main definitions

* `geometricPathLength S x v`: the length of the ray from `x` in direction `v` inside `S`.
* `densityWeightedPathLength ρ ρ₀ x v`: `ρ₀⁻¹ * ∫ s in Ici 0, ρ (x + s • v)`.

## Main results

* `geometricPathLength_le_diam`: for a bounded support and a unit direction, the geometric path
  length is at most the diameter of the support.
* `densityWeightedPathLength_le`: for a density bounded by `M` with bounded support, the
  density-weighted path length is at most `M / ρ₀` times the geometric one.
* `measurable_geometricPathLength`, `measurable_densityWeightedPathLength`: both functionals are
  measurable in the pair `(x, v)`.
* `densityWeightedPathLength_indicator_const`: for the uniform density `c` on `S`, the
  density-weighted path length is `c / ρ₀` times the geometric one.
* `densityWeightedPathLength_smul`: the density-weighted path length depends on the profile only
  through its shape, i.e. it is unchanged when the density and the central density are rescaled
  together.
* `geometricPathLength_eq_sSup`: for a convex support containing `x`, the geometric path length is
  the distance from `x` to the boundary of the support along the ray.
* `geometricPathLength_closedBall`: for the hard sphere of radius `R` about `c` and a unit
  direction, the geometric path length from a point `x` of the sphere is
  `√(⟪x - c, v⟫² + R² - ‖x - c‖²) - ⟪x - c, v⟫`.

## References

* A. Accardi, F. Arleo, W. K. Brooks, D. D'Enterria, V. Muccifora, *Parton propagation and
  fragmentation in QCD matter*, Riv. Nuovo Cim. 32 (2009) 439, §2.
-/

public section

open MeasureTheory Metric Set
open scoped InnerProductSpace

namespace EpsilonEridani
namespace Nuclear
namespace Medium

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The geometric path length of the ray from `x` in direction `v` through the set `S`: the
Lebesgue measure of the set of path parameters `s ≥ 0` with `x + s • v ∈ S`. With `S` the support
of a nuclear density and `‖v‖ = 1` this is the length of nuclear matter that a parton produced at
`x` and moving along `v` traverses. When that set has infinite measure the value is `0`. -/
noncomputable def geometricPathLength (S : Set E) (x v : E) : ℝ :=
  volume.real {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S}

theorem geometricPathLength_def (S : Set E) (x v : E) :
    geometricPathLength S x v = volume.real {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S} := (rfl)

/-- The density-weighted path length of the ray from `x` in direction `v` through the density
`ρ`, normalised by the central density `ρ₀`: `ρ₀⁻¹ * ∫ s in Ici 0, ρ (x + s • v)`. This is the
length of a uniform medium of density `ρ₀` containing as many nucleons per unit transverse area
along the ray as `ρ` does. -/
noncomputable def densityWeightedPathLength (ρ : E → ℝ) (ρ₀ : ℝ) (x v : E) : ℝ :=
  ρ₀⁻¹ * ∫ s in Ici (0 : ℝ), ρ (x + s • v)

theorem densityWeightedPathLength_def (ρ : E → ℝ) (ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength ρ ρ₀ x v = ρ₀⁻¹ * ∫ s in Ici (0 : ℝ), ρ (x + s • v) := (rfl)

variable {S : Set E} {ρ : E → ℝ} {ρ₀ : ℝ} {x v : E}

theorem geometricPathLength_nonneg (S : Set E) (x v : E) : 0 ≤ geometricPathLength S x v :=
  measureReal_nonneg

@[simp]
theorem geometricPathLength_empty (x v : E) : geometricPathLength (∅ : Set E) x v = 0 := by
  simp [geometricPathLength_def]

theorem densityWeightedPathLength_nonneg (hρ : 0 ≤ ρ) (hρ₀ : 0 ≤ ρ₀) (x v : E) :
    0 ≤ densityWeightedPathLength ρ ρ₀ x v :=
  mul_nonneg (inv_nonneg.2 hρ₀) (setIntegral_nonneg measurableSet_Ici fun _ _ => hρ _)

/-- The vacuum has zero density-weighted path length. -/
@[simp]
theorem densityWeightedPathLength_zero (ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength (0 : E → ℝ) ρ₀ x v = 0 := by
  simp [densityWeightedPathLength_def]

/-- The density-weighted path length depends on the density profile only through its shape:
rescaling the density and the central density by the same nonzero factor leaves it unchanged. -/
theorem densityWeightedPathLength_smul {c : ℝ} (hc : c ≠ 0) (ρ : E → ℝ) (ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength (c • ρ) (c * ρ₀) x v = densityWeightedPathLength ρ ρ₀ x v := by
  simp only [densityWeightedPathLength_def, Pi.smul_apply, smul_eq_mul, integral_const_mul,
    mul_inv]
  rw [mul_comm c⁻¹, mul_assoc, inv_mul_cancel_left₀ hc]

/-- The set of path parameters along a unit direction has measure at most the diameter of `S`,
because `s ↦ x + s • v` is an isometry for `‖v‖ = 1`. -/
private theorem volume_setOf_le_ediam (hv : ‖v‖ = 1) :
    volume {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S} ≤ ediam S := by
  have hiso : Isometry fun s : ℝ => x + s • v := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, Real.dist_eq,
      Real.norm_eq_abs]
  calc volume {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S}
      ≤ ediam {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S} := Real.volume_le_diam _
    _ = ediam ((fun s : ℝ => x + s • v) '' {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S}) :=
        (hiso.ediam_image _).symm
    _ ≤ ediam S := ediam_mono (image_subset_iff.2 fun _ hs => hs.2)

/-- For a bounded support and a unit direction, the geometric path length is at most the diameter
of the support. In particular it is finite for a medium of compact support. -/
theorem geometricPathLength_le_diam (hS : Bornology.IsBounded S) (hv : ‖v‖ = 1) :
    geometricPathLength S x v ≤ diam S :=
  ENNReal.toReal_mono hS.ediam_ne_top (volume_setOf_le_ediam hv)

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- On the uniform density `c` on a measurable set `S` the density-weighted path length is
`c / ρ₀` times the geometric path length through `S`. With `ρ₀ = c` the two coincide
(`densityWeightedPathLength_indicator_const_self`). -/
theorem densityWeightedPathLength_indicator_const (hS : MeasurableSet S) (c ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength (S.indicator fun _ => c) ρ₀ x v =
      c / ρ₀ * geometricPathLength S x v := by
  have hpre : MeasurableSet ((fun s : ℝ => x + s • v) ⁻¹' S) :=
    hS.preimage (by fun_prop : Continuous fun s : ℝ => x + s • v).measurable
  have hset : {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S} = (fun s : ℝ => x + s • v) ⁻¹' S ∩ Ici 0 := by
    ext s
    simp [and_comm]
  rw [densityWeightedPathLength_def, geometricPathLength_def, hset,
    ← measureReal_restrict_apply hpre]
  simp_rw [← Set.indicator_comp_right (fun s : ℝ => x + s • v) (g := fun _ => c), Function.comp_def]
  rw [integral_indicator_const _ hpre, smul_eq_mul]
  ring

/-- For a uniform medium normalised by its own density, the density-weighted and the geometric
path lengths coincide. -/
theorem densityWeightedPathLength_indicator_const_self (hS : MeasurableSet S) {c : ℝ}
    (hc : c ≠ 0) (x v : E) :
    densityWeightedPathLength (S.indicator fun _ => c) c x v = geometricPathLength S x v := by
  rw [densityWeightedPathLength_indicator_const hS, div_self hc, one_mul]

/-- For a nonnegative density bounded by `M`, supported in a bounded measurable set `S`, the
density-weighted path length along a unit direction is at most `M / ρ₀` times the geometric path
length through `S`. In particular it is finite for a bounded density of compact support. -/
theorem densityWeightedPathLength_le (hS : MeasurableSet S) (hSb : Bornology.IsBounded S)
    (hv : ‖v‖ = 1) (hρ : 0 ≤ ρ) (hρS : Function.support ρ ⊆ S) {M : ℝ} (hρM : ∀ y, ρ y ≤ M)
    (hρ₀ : 0 ≤ ρ₀) :
    densityWeightedPathLength ρ ρ₀ x v ≤ M / ρ₀ * geometricPathLength S x v := by
  rw [← densityWeightedPathLength_indicator_const hS, densityWeightedPathLength_def,
    densityWeightedPathLength_def]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ₀)
  have hpre : MeasurableSet ((fun s : ℝ => x + s • v) ⁻¹' S) :=
    hS.preimage (by fun_prop : Continuous fun s : ℝ => x + s • v).measurable
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => hρ _) ?_
    (Filter.Eventually.of_forall fun s => ?_)
  · simp_rw [← Set.indicator_comp_right (fun s : ℝ => x + s • v) (g := fun _ => M),
      Function.comp_def]
    refine (integrable_indicator_iff hpre).2 (integrableOn_const ?_)
    rw [Measure.restrict_apply hpre]
    refine ne_top_of_le_ne_top hSb.ediam_ne_top (le_trans (measure_mono fun s hs => ?_)
      (volume_setOf_le_ediam (x := x) hv))
    exact ⟨hs.2, hs.1⟩
  · dsimp only
    by_cases hs : x + s • v ∈ S
    · simpa [Set.indicator_of_mem hs] using hρM _
    · rw [Set.indicator_of_notMem hs, Function.notMem_support.1 fun h => hs (hρS h)]

variable [SecondCountableTopology E]

/-- The geometric path length through a measurable set is measurable in the production point and
the direction. -/
theorem measurable_geometricPathLength (hS : MeasurableSet S) :
    Measurable fun p : E × E => geometricPathLength S p.1 p.2 := by
  have hset : MeasurableSet {q : (E × E) × ℝ | 0 ≤ q.2 ∧ q.1.1 + q.2 • q.1.2 ∈ S} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (hS.preimage (by fun_prop : Continuous fun q : (E × E) × ℝ => q.1.1 + q.2 • q.1.2).measurable)
  exact (measurable_measure_prodMk_left hset).ennreal_toReal

/-- The density-weighted path length of a measurable density is measurable in the production
point and the direction. -/
theorem measurable_densityWeightedPathLength (hρ : Measurable ρ) (ρ₀ : ℝ) :
    Measurable fun p : E × E => densityWeightedPathLength ρ ρ₀ p.1 p.2 := by
  have hf : Measurable fun q : (E × E) × ℝ => ρ (q.1.1 + q.2 • q.1.2) :=
    hρ.comp (by fun_prop : Continuous fun q : (E × E) × ℝ => q.1.1 + q.2 • q.1.2).measurable
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ici 0))).measurable
    |>.const_mul _

end Measurable

/-- For a convex support containing the production point, the geometric path length is the
distance from `x` to the boundary of the support along the ray: the supremum of the path
parameters `s ≥ 0` with `x + s • v ∈ S`. (Both sides are `0` when the ray never leaves `S`.) -/
theorem geometricPathLength_eq_sSup (hS : Convex ℝ S) (hx : x ∈ S) :
    geometricPathLength S x v = sSup {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S} := by
  set T := {s : ℝ | 0 ≤ s ∧ x + s • v ∈ S}
  have hT0 : (0 : ℝ) ∈ T := ⟨le_rfl, by simpa using hx⟩
  -- `T` is convex, hence an interval of `ℝ` containing `0`.
  have hord : T.OrdConnected := by
    refine convex_iff_ordConnected.1 ?_
    convert (convex_Ici 0).inter
      ((hS.translate_preimage_right x).is_linear_preimage (IsLinearMap.isLinearMap_smul' v)) using 1
    ext s
    simp [T]
  rw [geometricPathLength_def]
  by_cases hb : BddAbove T
  · -- `T` lies between `[0, sSup T)` and `[0, sSup T]`, both of length `sSup T`.
    have hm : 0 ≤ sSup T := le_csSup hb hT0
    have h₁ : T ⊆ Icc 0 (sSup T) := fun s hs => ⟨hs.1, le_csSup hb hs⟩
    have h₂ : Ico 0 (sSup T) ⊆ T := fun s hs => by
      obtain ⟨t, ht, hst⟩ := exists_lt_of_lt_csSup ⟨0, hT0⟩ hs.2
      exact hord.out hT0 ht ⟨hs.1, hst.le⟩
    have hvol : volume T = ENNReal.ofReal (sSup T) := by
      refine le_antisymm ((measure_mono h₁).trans_eq ?_) (le_of_eq_of_le ?_ (measure_mono h₂))
      · simp [Real.volume_Icc]
      · simp [Real.volume_Ico]
    rw [measureReal_def, hvol, ENNReal.toReal_ofReal hm]
  · -- Otherwise `T` contains `[0, ∞)`, so both sides are `0`.
    have h : Ici 0 ⊆ T := fun s hs => by
      obtain ⟨t, ht, hst⟩ := not_bddAbove_iff.1 hb s
      exact hord.out hT0 ht ⟨hs, hst.le⟩
    have hvol : volume T = ⊤ := top_unique (Real.volume_Ici.symm.trans_le (measure_mono h))
    rw [measureReal_def, hvol, ENNReal.toReal_top, Real.sSup_of_not_bddAbove hb]

end NormedSpace

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The hard sphere: for a point `x` of the closed ball of radius `R` about `c` and a unit
direction `v`, the geometric path length is the larger root
`√(⟪x - c, v⟫² + R² - ‖x - c‖²) - ⟪x - c, v⟫` of `‖x + s • v - c‖ = R`. Together with
`densityWeightedPathLength_indicator_const` this gives both path-length functionals of the uniform
sphere in closed form. -/
theorem geometricPathLength_closedBall {c x v : F} {R : ℝ} (hx : x ∈ closedBall c R)
    (hv : ‖v‖ = 1) :
    geometricPathLength (closedBall c R) x v =
      √(⟪x - c, v⟫_ℝ ^ 2 + R ^ 2 - ‖x - c‖ ^ 2) - ⟪x - c, v⟫_ℝ := by
  set b := ⟪x - c, v⟫_ℝ
  set D := b ^ 2 + R ^ 2 - ‖x - c‖ ^ 2
  have hxc : ‖x - c‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hx
  have hR : 0 ≤ R := (norm_nonneg _).trans hxc
  have hb2 : b ^ 2 ≤ D := by
    have : ‖x - c‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hxc 2
    linarith
  have hD : 0 ≤ D := (sq_nonneg b).trans hb2
  have hbD := abs_le.1 (Real.abs_le_sqrt hb2)
  -- `‖x + s • v - c‖ ≤ R` is the quadratic inequality `(s + b)² ≤ D`.
  have hset : {s : ℝ | 0 ≤ s ∧ x + s • v ∈ closedBall c R} = Icc 0 (√D - b) := by
    ext s
    have hnorm : ‖x + s • v - c‖ ^ 2 = (s + b) ^ 2 - D + R ^ 2 := by
      rw [show x + s • v - c = (x - c) + s • v by abel, norm_add_sq_real, inner_smul_right,
        norm_smul, hv, Real.norm_eq_abs, mul_one, sq_abs]
      ring
    simp only [mem_ofPred_eq, mem_Icc, mem_closedBall, dist_eq_norm,
      ← sq_le_sq₀ (norm_nonneg _) hR, hnorm, and_congr_right_iff]
    intro hs
    rw [show (s + b) ^ 2 - D + R ^ 2 ≤ R ^ 2 ↔ (s + b) ^ 2 ≤ D by
      constructor <;> intro h <;> linarith, Real.sq_le hD]
    constructor
    · exact fun h => by linarith [h.2]
    · exact fun h => ⟨by linarith, by linarith⟩
  rw [geometricPathLength_def, hset, Real.volume_real_Icc, sub_zero,
    max_eq_left (by linarith)]

end InnerProductSpace

end Medium
end Nuclear
end EpsilonEridani
