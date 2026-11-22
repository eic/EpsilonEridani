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
  lies in the set `S`, which is the support of the nuclear density: the Lebesgue measure of the set
  `pathParameters S x v = {s | 0 ≤ s ∧ x + s • v ∈ S}`. For a support star-shaped about the
  production point this is the path parameter at which the ray leaves `S`, which for `‖v‖ = 1` is
  the distance along the ray from `x` to its exit point
  (`geometricPathLength_eq_sSup_of_starConvex`); when the ray never leaves `S`, both sides are `0`.
* The *density-weighted path length* `densityWeightedPathLength ρ ρ₀ x v` is the integral of the
  density `ρ` along the ray, divided by the central density `ρ₀`: the length of uniform medium of
  density `ρ₀` with the same number of nucleons per unit area along the ray.

For a uniform medium the two are proportional, with constant the ratio of the density to the
central density (`densityWeightedPathLength_indicator_const`). For a general bounded profile the
density-weighted length is only bounded by the ratio of the maximal to the central density times
the geometric one (`densityWeightedPathLength_le_mul_geometricPathLength`). Local quantities per
unit path length, such as transport coefficients, pair with the density-weighted length, while an
absorption factor that depends only on whether the hadron forms inside the nucleus pairs with the
geometric one.

The ambient space is any real normed space; the physical case is three-dimensional space with
`‖v‖ = 1`.

## Main definitions

* `pathParameters S x v`: the set of path parameters `s ≥ 0` with `x + s • v ∈ S`.
* `geometricPathLength S x v`: the measure of `pathParameters S x v`; for `‖v‖ = 1`, the length of
  the ray from `x` in direction `v` inside `S`.
* `densityWeightedPathLength ρ ρ₀ x v`: `ρ₀⁻¹ * ∫ s in Ici 0, ρ (x + s • v)`.

## Main results

* `volume_pathParameters_le_ediam`, `volume_pathParameters_ne_top_of_isBounded`: for a unit
  direction, the set of path parameters has measure at most the diameter of `S`, so it has finite
  measure when `S` is bounded; the geometric path length is then an honest length rather than the
  junk value `0`.
* `geometricPathLength_le_diam`: for a bounded support and a unit direction, the geometric path
  length is at most the diameter of the support.
* `integrableOn_Ici_comp_add_smul`: a measurable bounded density supported in a set whose set of
  path parameters has finite measure is integrable along the ray, so the density-weighted path
  length is an honest integral.
* `densityWeightedPathLength_le_mul_geometricPathLength`: for a nonnegative density bounded by `M`
  supported in such a set, and a nonnegative central density `ρ₀`, the density-weighted path length
  is at most `M / ρ₀` times the geometric one.
* `measurable_geometricPathLength`, `measurable_densityWeightedPathLength`: both functionals are
  measurable in the pair `(x, v)`, with the dot-notation forms `Measurable.geometricPathLength`
  and `Measurable.densityWeightedPathLength` along a measurably varying production point and
  direction.
* `densityWeightedPathLength_indicator_const`: for the uniform density `c` on `S`, the
  density-weighted path length is `c / ρ₀` times the geometric one.
* `densityWeightedPathLength_smul`, `densityWeightedPathLength_smul_mul`: the density-weighted path
  length is homogeneous in the density, and depends on the profile only through its shape, i.e. it
  is unchanged when the density and the central density are rescaled by the same nonzero factor.
* `geometricPathLength_eq_sSup`, `geometricPathLength_eq_sSup_of_starConvex`: when the path
  parameters are star-shaped about `0` (for instance for a support star-shaped about `x`), the
  geometric path length is the supremum of the path parameters `s ≥ 0` with `x + s • v ∈ S`: the
  parameter at which the ray leaves `S`, which for `‖v‖ = 1` is the distance along the ray from `x`
  to its exit point.
* `pathParameters_closedBall`, `geometricPathLength_closedBall`: for the hard sphere of radius `R`
  about `c` and a unit direction, the path parameters from a point `x` of the sphere form the
  interval from `0` to `√(⟪x - c, v⟫² + R² - ‖x - c‖²) - ⟪x - c, v⟫`, which is the geometric path
  length.

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

/-- The set of path parameters `s ≥ 0` at which the ray from `x` in direction `v` lies in `S`. -/
def pathParameters (S : Set E) (x v : E) : Set ℝ :=
  {s | 0 ≤ s ∧ x + s • v ∈ S}

@[simp]
theorem mem_pathParameters {S : Set E} {x v : E} {s : ℝ} :
    s ∈ pathParameters S x v ↔ 0 ≤ s ∧ x + s • v ∈ S :=
  Iff.rfl

/-- The set of path parameters is the preimage of `S` under the ray map, restricted to `Ici 0`. -/
theorem pathParameters_eq_preimage_inter (S : Set E) (x v : E) :
    pathParameters S x v = (fun s : ℝ => x + s • v) ⁻¹' S ∩ Ici 0 := by
  ext s
  simp [and_comm]

/-- The geometric path length of the ray from `x` in direction `v` through the set `S`: the
Lebesgue measure of the set `pathParameters S x v` of path parameters `s ≥ 0` with
`x + s • v ∈ S`. With `S` the support of a nuclear density and `‖v‖ = 1` this is the length of
nuclear matter that a parton produced at `x` and moving along `v` traverses. When that set has
infinite measure the value is `0`. -/
noncomputable def geometricPathLength (S : Set E) (x v : E) : ℝ :=
  volume.real (pathParameters S x v)

theorem geometricPathLength_def (S : Set E) (x v : E) :
    geometricPathLength S x v = volume.real (pathParameters S x v) := (rfl)

/-- The density-weighted path length of the ray from `x` in direction `v` through the density
`ρ`, normalised by the central density `ρ₀`: `ρ₀⁻¹ * ∫ s in Ici 0, ρ (x + s • v)`. This is the
length of a uniform medium of density `ρ₀` containing as many nucleons per unit transverse area
along the ray as `ρ` does. When `s ↦ ρ (x + s • v)` is not integrable on `Ici 0`, or `ρ₀ = 0`, the
value is `0`; `integrableOn_Ici_comp_add_smul` gives integrability for a bounded density. -/
noncomputable def densityWeightedPathLength (ρ : E → ℝ) (ρ₀ : ℝ) (x v : E) : ℝ :=
  ρ₀⁻¹ * ∫ s in Ici (0 : ℝ), ρ (x + s • v)

theorem densityWeightedPathLength_def (ρ : E → ℝ) (ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength ρ ρ₀ x v = ρ₀⁻¹ * ∫ s in Ici (0 : ℝ), ρ (x + s • v) := (rfl)

variable {S : Set E} {ρ : E → ℝ} {ρ₀ : ℝ} {x v : E}

@[simp]
theorem geometricPathLength_nonneg (S : Set E) (x v : E) : 0 ≤ geometricPathLength S x v :=
  measureReal_nonneg

@[simp]
theorem geometricPathLength_empty (x v : E) : geometricPathLength (∅ : Set E) x v = 0 := by
  simp [geometricPathLength_def, pathParameters_eq_preimage_inter]

theorem densityWeightedPathLength_nonneg (hρ : 0 ≤ ρ) (hρ₀ : 0 ≤ ρ₀) (x v : E) :
    0 ≤ densityWeightedPathLength ρ ρ₀ x v :=
  mul_nonneg (inv_nonneg.2 hρ₀) (setIntegral_nonneg measurableSet_Ici fun _ _ => hρ _)

/-- The vacuum has zero density-weighted path length. -/
@[simp]
theorem densityWeightedPathLength_zero (ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength (0 : E → ℝ) ρ₀ x v = 0 := by
  simp [densityWeightedPathLength_def]

/-- The junk value: normalising by a zero central density gives `0`. -/
@[simp]
theorem densityWeightedPathLength_centralDensity_zero (ρ : E → ℝ) (x v : E) :
    densityWeightedPathLength ρ 0 x v = 0 := by
  simp [densityWeightedPathLength_def]

/-- The density-weighted path length is homogeneous in the density. -/
theorem densityWeightedPathLength_smul (c : ℝ) (ρ : E → ℝ) (ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength (c • ρ) ρ₀ x v = c * densityWeightedPathLength ρ ρ₀ x v := by
  simp only [densityWeightedPathLength_def, Pi.smul_apply, smul_eq_mul, integral_const_mul]
  ring

/-- The density-weighted path length depends on the density profile only through its shape:
rescaling the density and the central density by the same nonzero factor leaves it unchanged. -/
theorem densityWeightedPathLength_smul_mul {c : ℝ} (hc : c ≠ 0) (ρ : E → ℝ) (ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength (c • ρ) (c * ρ₀) x v = densityWeightedPathLength ρ ρ₀ x v := by
  rw [densityWeightedPathLength_smul, densityWeightedPathLength_def,
    densityWeightedPathLength_def]
  field_simp

/-- The set of path parameters along a unit direction has measure at most the diameter of `S`,
because `s ↦ x + s • v` is an isometry for `‖v‖ = 1`. -/
theorem volume_pathParameters_le_ediam (hv : ‖v‖ = 1) :
    volume (pathParameters S x v) ≤ ediam S := by
  have hiso : Isometry fun s : ℝ => x + s • v :=
    (isometry_add_left x).comp (LinearIsometry.toSpanSingleton ℝ E hv).isometry
  calc volume (pathParameters S x v)
      ≤ ediam (pathParameters S x v) := Real.volume_le_diam _
    _ = ediam ((fun s : ℝ => x + s • v) '' pathParameters S x v) := (hiso.ediam_image _).symm
    _ ≤ ediam S := ediam_mono (image_subset_iff.2 fun _ hs => (mem_pathParameters.1 hs).2)

/-- For a bounded support and a unit direction, the set of path parameters has finite measure, so
the geometric path length is its honest measure rather than the junk value `0`. -/
theorem volume_pathParameters_ne_top_of_isBounded (hS : Bornology.IsBounded S) (hv : ‖v‖ = 1) :
    volume (pathParameters S x v) ≠ ⊤ :=
  ne_top_of_le_ne_top hS.ediam_ne_top (volume_pathParameters_le_ediam hv)

/-- For a bounded support and a unit direction, the geometric path length is at most the diameter
of the support. That it is the honest measure of the set of path parameters, not the junk value
`0`, is `volume_pathParameters_ne_top_of_isBounded`. -/
theorem geometricPathLength_le_diam (hS : Bornology.IsBounded S) (hv : ‖v‖ = 1) :
    geometricPathLength S x v ≤ diam S := by
  rw [geometricPathLength_def, measureReal_def, Metric.diam]
  exact ENNReal.toReal_mono hS.ediam_ne_top (volume_pathParameters_le_ediam hv)

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

private theorem measurable_ray (x v : E) : Measurable fun s : ℝ => x + s • v :=
  (by fun_prop : Continuous fun s : ℝ => x + s • v).measurable

private theorem measurableSet_preimage_ray (hS : MeasurableSet S) :
    MeasurableSet ((fun s : ℝ => x + s • v) ⁻¹' S) :=
  hS.preimage (measurable_ray x v)

@[measurability]
theorem measurableSet_pathParameters (hS : MeasurableSet S) (x v : E) :
    MeasurableSet (pathParameters S x v) := by
  rw [pathParameters_eq_preimage_inter]
  exact (measurableSet_preimage_ray hS).inter measurableSet_Ici

/-- The uniform density `M` on `S` is integrable along the ray when the set of path parameters has
finite measure. -/
private theorem integrableOn_indicator_const (hS : MeasurableSet S)
    (hfin : volume (pathParameters S x v) ≠ ⊤) (M : ℝ) :
    IntegrableOn (fun s : ℝ => S.indicator (fun _ => M) (x + s • v)) (Ici 0) := by
  simp_rw [← Set.indicator_comp_right (fun s : ℝ => x + s • v) (g := fun _ => M),
    Function.comp_def]
  refine (integrable_indicator_iff (measurableSet_preimage_ray hS)).2 (integrableOn_const ?_)
  rwa [Measure.restrict_apply (measurableSet_preimage_ray hS), ← pathParameters_eq_preimage_inter]

/-- On the uniform density `c` on a measurable set `S` the density-weighted path length is
`c / ρ₀` times the geometric path length through `S`. With `ρ₀ = c ≠ 0` the two coincide. -/
theorem densityWeightedPathLength_indicator_const (hS : MeasurableSet S) (c ρ₀ : ℝ) (x v : E) :
    densityWeightedPathLength (S.indicator fun _ => c) ρ₀ x v =
      c / ρ₀ * geometricPathLength S x v := by
  have hpre := measurableSet_preimage_ray (x := x) (v := v) hS
  rw [densityWeightedPathLength_def, geometricPathLength_def, pathParameters_eq_preimage_inter,
    ← measureReal_restrict_apply hpre]
  simp_rw [← Set.indicator_comp_right (fun s : ℝ => x + s • v) (g := fun _ => c), Function.comp_def]
  rw [integral_indicator_const _ hpre, smul_eq_mul]
  ring

/-- A measurable density bounded by `M` and supported in a measurable set `S` is integrable along
the ray from `x` in direction `v` when the set of path parameters in `S` has finite measure (for a
bounded `S` and `‖v‖ = 1`, see `volume_pathParameters_ne_top_of_isBounded`). The density-weighted
path length is then an honest integral rather than the junk value `0`. -/
theorem integrableOn_Ici_comp_add_smul (hS : MeasurableSet S)
    (hfin : volume (pathParameters S x v) ≠ ⊤) (hρm : Measurable ρ)
    (hρS : Function.support ρ ⊆ S) {M : ℝ} (hρM : ∀ y, |ρ y| ≤ M) :
    IntegrableOn (fun s : ℝ => ρ (x + s • v)) (Ici 0) :=
  (integrableOn_indicator_const hS hfin M).mono'
    (hρm.comp (measurable_ray x v)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => (Real.norm_eq_abs _).trans_le <|
      Set.le_indicator (f := fun y => |ρ y|) (fun y _ => hρM y)
        (fun y hy => by simp [Function.notMem_support.1 fun h => hy (hρS h)]) _)

/-- For a nonnegative density bounded by `M`, supported in a measurable set `S` whose set of path
parameters along the ray has finite measure (for a bounded `S` and `‖v‖ = 1`, see
`volume_pathParameters_ne_top_of_isBounded`), and a nonnegative central density `ρ₀`, the
density-weighted path length is at most `M / ρ₀` times the geometric path length through `S`. -/
theorem densityWeightedPathLength_le_mul_geometricPathLength (hS : MeasurableSet S)
    (hfin : volume (pathParameters S x v) ≠ ⊤) (hρ : 0 ≤ ρ)
    (hρS : Function.support ρ ⊆ S) {M : ℝ} (hρM : ∀ y, ρ y ≤ M) (hρ₀ : 0 ≤ ρ₀) :
    densityWeightedPathLength ρ ρ₀ x v ≤ M / ρ₀ * geometricPathLength S x v := by
  rw [← densityWeightedPathLength_indicator_const hS, densityWeightedPathLength_def,
    densityWeightedPathLength_def]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hρ₀)
  exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => hρ _)
    (integrableOn_indicator_const hS hfin M) (Filter.Eventually.of_forall fun _ =>
      Set.le_indicator (fun y _ => hρM y) (fun y hy => (Function.notMem_support.1 fun h =>
        hy (hρS h)).le) _)

variable [SecondCountableTopology E]

private theorem measurable_rayProd : Measurable fun q : (E × E) × ℝ => q.1.1 + q.2 • q.1.2 :=
  (by fun_prop : Continuous fun q : (E × E) × ℝ => q.1.1 + q.2 • q.1.2).measurable

/-- The geometric path length through a measurable set is measurable in the production point and
the direction. -/
theorem measurable_geometricPathLength (hS : MeasurableSet S) :
    Measurable fun p : E × E => geometricPathLength S p.1 p.2 := by
  have hset : MeasurableSet {q : (E × E) × ℝ | 0 ≤ q.2 ∧ q.1.1 + q.2 • q.1.2 ∈ S} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (hS.preimage measurable_rayProd)
  simp only [geometricPathLength_def, measureReal_def]
  -- The section of `hset` at `p` is, by definition, `pathParameters S p.1 p.2`.
  exact (measurable_measure_prodMk_left hset).ennreal_toReal

/-- The density-weighted path length of a measurable density is measurable in the production
point and the direction. -/
theorem measurable_densityWeightedPathLength (hρ : Measurable ρ) (ρ₀ : ℝ) :
    Measurable fun p : E × E => densityWeightedPathLength ρ ρ₀ p.1 p.2 := by
  have hf : Measurable fun q : (E × E) × ℝ => ρ (q.1.1 + q.2 • q.1.2) :=
    hρ.comp measurable_rayProd
  exact (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ici 0))).measurable
    |>.const_mul _

/-- The geometric path length through a measurable set, along a measurably varying production
point and direction, is measurable. -/
@[fun_prop]
theorem _root_.Measurable.geometricPathLength {α : Type*} [MeasurableSpace α]
    {g h : α → E} (hg : Measurable g) (hh : Measurable h) (hS : MeasurableSet S) :
    Measurable fun a => Medium.geometricPathLength S (g a) (h a) :=
  (measurable_geometricPathLength hS).comp (hg.prodMk hh)

/-- The density-weighted path length of a measurable density, along a measurably varying
production point and direction, is measurable. -/
@[fun_prop]
theorem _root_.Measurable.densityWeightedPathLength {α : Type*} [MeasurableSpace α]
    {g h : α → E} (hg : Measurable g) (hh : Measurable h) (hρ : Measurable ρ) (ρ₀ : ℝ) :
    Measurable fun a => Medium.densityWeightedPathLength ρ ρ₀ (g a) (h a) :=
  (measurable_densityWeightedPathLength hρ ρ₀).comp (hg.prodMk hh)

end Measurable

/-- For a support star-shaped about the production point, the path parameters are star-shaped
about `0`: with `t` they contain `[0, t]`. -/
theorem starConvex_pathParameters (hS : StarConvex ℝ x S) (v : E) :
    StarConvex ℝ 0 (pathParameters S x v) := by
  rintro t ⟨ht0, ht⟩ a b ha hb hab
  rw [smul_zero, zero_add, smul_eq_mul, mem_pathParameters]
  refine ⟨mul_nonneg hb ht0, ?_⟩
  convert hS ht ha hb hab using 1
  rw [smul_add, smul_smul, ← add_assoc, ← add_smul, hab, one_smul]

/-- When the path parameters are star-shaped about `0`, i.e. the ray does not re-enter `S` once
it has left it, the geometric path length is the supremum of the path parameters `s ≥ 0` with
`x + s • v ∈ S`: the path parameter at which the ray leaves `S`, which for `‖v‖ = 1` is the distance
along the ray from `x` to its exit point. (Both sides are `0` when the ray never leaves `S`, and
when it never meets `S`.) -/
theorem geometricPathLength_eq_sSup (hT : StarConvex ℝ 0 (pathParameters S x v)) :
    geometricPathLength S x v = sSup (pathParameters S x v) := by
  rw [geometricPathLength_def]
  set T := pathParameters S x v
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · rw [hTe, measureReal_empty, Real.sSup_empty]
  have hT0 : (0 : ℝ) ∈ T := hT.mem hTne
  have hord : T.OrdConnected := hT.ordConnected hT0
  by_cases hb : BddAbove T
  · -- `T` lies between `[0, sSup T)` and `[0, sSup T]`, both of length `sSup T`.
    have hm : 0 ≤ sSup T := le_csSup hb hT0
    have h₁ : T ⊆ Icc 0 (sSup T) := fun s hs => ⟨(mem_pathParameters.1 hs).1, le_csSup hb hs⟩
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

/-- For a support star-shaped about the production point (for instance a convex support containing
it), the geometric path length is the path parameter at which the ray leaves `S`. -/
theorem geometricPathLength_eq_sSup_of_starConvex (hS : StarConvex ℝ x S) :
    geometricPathLength S x v = sSup (pathParameters S x v) :=
  geometricPathLength_eq_sSup (starConvex_pathParameters hS v)

end NormedSpace

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The hard sphere: for a point `x` of the closed ball of radius `R` about `c` and a unit
direction `v`, the path parameters inside the ball form the interval from `0` to the larger root
`√(⟪x - c, v⟫² + R² - ‖x - c‖²) - ⟪x - c, v⟫` of `‖x + s • v - c‖ = R`. -/
theorem pathParameters_closedBall {c x v : F} {R : ℝ} (hx : x ∈ closedBall c R) (hv : ‖v‖ = 1) :
    pathParameters (closedBall c R) x v =
      Icc 0 (√(⟪x - c, v⟫_ℝ ^ 2 + R ^ 2 - ‖x - c‖ ^ 2) - ⟪x - c, v⟫_ℝ) := by
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
  ext s
  have hnorm : ‖x + s • v - c‖ ^ 2 = (s + b) ^ 2 - D + R ^ 2 := by
    rw [show x + s • v - c = (x - c) + s • v by abel, norm_add_sq_real, inner_smul_right,
      norm_smul, hv, Real.norm_eq_abs, mul_one, sq_abs]
    ring
  simp only [mem_pathParameters, mem_Icc, mem_closedBall, dist_eq_norm,
    ← sq_le_sq₀ (norm_nonneg _) hR, hnorm, and_congr_right_iff]
  intro hs
  rw [show (s + b) ^ 2 - D + R ^ 2 ≤ R ^ 2 ↔ (s + b) ^ 2 ≤ D by
    constructor <;> intro h <;> linarith, Real.sq_le hD]
  constructor
  · exact fun h => by linarith [h.2]
  · exact fun h => ⟨by linarith, by linarith⟩

/-- The hard sphere: for a point `x` of the closed ball of radius `R` about `c` and a unit
direction `v`, the geometric path length is the larger root
`√(⟪x - c, v⟫² + R² - ‖x - c‖²) - ⟪x - c, v⟫` of `‖x + s • v - c‖ = R`. Together with
`densityWeightedPathLength_indicator_const` this gives both path-length functionals of the uniform
sphere in closed form. -/
theorem geometricPathLength_closedBall {c x v : F} {R : ℝ} (hx : x ∈ closedBall c R)
    (hv : ‖v‖ = 1) :
    geometricPathLength (closedBall c R) x v =
      √(⟪x - c, v⟫_ℝ ^ 2 + R ^ 2 - ‖x - c‖ ^ 2) - ⟪x - c, v⟫_ℝ := by
  -- The production point itself is in the ball, so the interval is nonempty.
  have h0 : (0 : ℝ) ∈ pathParameters (closedBall c R) x v := ⟨le_rfl, by simpa using hx⟩
  rw [pathParameters_closedBall hx hv] at h0
  rw [geometricPathLength_def, pathParameters_closedBall hx hv, Real.volume_real_Icc, sub_zero,
    max_eq_left h0.2]

end InnerProductSpace

end Medium
end Nuclear
end EpsilonEridani
