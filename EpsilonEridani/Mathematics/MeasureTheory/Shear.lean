/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Group.Prod
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
/-!
# The scaled shear of the plane

For `a ≠ 0` the map `(x, y) ↦ (x, x + a * y)` of `ℝ × ℝ` is the composite of a rescaling of the
second coordinate by `a` and Mathlib's shear `(x, y) ↦ (x, x + y)`
(`MeasureTheory.measurePreserving_prod_add`), packaged as the measurable equivalence
`measurableEquivProdAddMul`. It is therefore a measurable embedding
(`measurableEmbedding_prod_add_mul`) that sends Lebesgue measure to `|a⁻¹|` times itself
(`measurePreserving_prod_add_mul`), which gives the change of variables
`∫ g (x, x + a * y) = |a⁻¹| • ∫ g` (`integral_comp_prod_add_mul`, which also holds for `a = 0`)
and the corresponding integrability criterion (`integrable_comp_prod_add_mul_iff`).

This is the two-dimensional substitution `x ↦ β + a α` that turns an integral along the lines
`x = β + a α` of the `(β, α)` plane into an integral over the `(β, x)` plane; the moments of a
generalized parton distribution built from a double distribution are computed with it.
-/

@[expose] public section

namespace EpsilonEridani

open MeasureTheory

/-- For `a ≠ 0` the scaled shear `(x, y) ↦ (x, x + a * y)` of the plane as a measurable
equivalence: the rescaling `y ↦ a * y` of the second coordinate followed by Mathlib's shear
`MeasurableEquiv.shearAddRight`. -/
noncomputable def measurableEquivProdAddMul {a : ℝ} (ha : a ≠ 0) : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.mulLeft₀ a ha)).trans
    (MeasurableEquiv.shearAddRight ℝ)

/-- The scaled shear `measurableEquivProdAddMul` is `(x, y) ↦ (x, x + a * y)`. -/
@[simp]
lemma coe_measurableEquivProdAddMul {a : ℝ} (ha : a ≠ 0) :
    ⇑(measurableEquivProdAddMul ha) = fun p : ℝ × ℝ => (p.1, p.1 + a * p.2) :=
  rfl

/-- For `a ≠ 0` the scaled shear `(x, y) ↦ (x, x + a * y)` is a measurable embedding. -/
lemma measurableEmbedding_prod_add_mul {a : ℝ} (ha : a ≠ 0) :
    MeasurableEmbedding fun p : ℝ × ℝ => (p.1, p.1 + a * p.2) := by
  rw [← coe_measurableEquivProdAddMul ha]
  exact (measurableEquivProdAddMul ha).measurableEmbedding

/-- For `a ≠ 0` the scaled shear `(x, y) ↦ (x, x + a * y)` sends Lebesgue measure on the plane
to `|a⁻¹|` times Lebesgue measure. -/
lemma measurePreserving_prod_add_mul {a : ℝ} (ha : a ≠ 0) :
    MeasurePreserving (fun p : ℝ × ℝ => (p.1, p.1 + a * p.2)) volume
      (ENNReal.ofReal |a⁻¹| • volume) := by
  -- the rescaling of the second coordinate scales Lebesgue measure by `|a⁻¹|`
  have hS : MeasurePreserving ((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.mulLeft₀ a ha))
      (volume : Measure (ℝ × ℝ)) (ENNReal.ofReal |a⁻¹| • volume) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_smul_right]
    exact (MeasurePreserving.id _).prod
      ⟨(MeasurableEquiv.mulLeft₀ a ha).measurable, Real.map_volume_mul_left ha⟩
  -- the shear preserves Lebesgue measure, hence also its multiples
  have hA := (measurePreserving_prod_add (volume : Measure ℝ) volume).smul_measure
    (ENNReal.ofReal |a⁻¹|)
  rw [← Measure.volume_eq_prod] at hA
  rw [← coe_measurableEquivProdAddMul ha, measurableEquivProdAddMul, MeasurableEquiv.coe_trans]
  exact hA.comp hS

/-- For `a ≠ 0`, a function on the plane is integrable if and only if its composite with the
scaled shear `(x, y) ↦ (x, x + a * y)` is. -/
lemma integrable_comp_prod_add_mul_iff {E : Type*} [NormedAddCommGroup E] (g : ℝ × ℝ → E)
    {a : ℝ} (ha : a ≠ 0) :
    Integrable (fun p : ℝ × ℝ => g (p.1, p.1 + a * p.2)) ↔ Integrable g := by
  rw [← integrable_smul_measure (μ := volume) (f := g) (c := ENNReal.ofReal |a⁻¹|)
    (by simp [ha]) ENNReal.ofReal_ne_top]
  exact (measurePreserving_prod_add_mul ha).integrable_comp_emb
    (measurableEmbedding_prod_add_mul ha)

/-- **Change of variables along the scaled shear.**
`∫ g (x, x + a * y) d(x, y) = |a⁻¹| • ∫ g`. For `a = 0` the identity is degenerate, not a
change of variables: the left side vanishes because the integrand is constant in `y` and
Lebesgue measure on the line is infinite, and the right side vanishes because `|0⁻¹| = 0`. -/
lemma integral_comp_prod_add_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ × ℝ → E) (a : ℝ) :
    ∫ p : ℝ × ℝ, g (p.1, p.1 + a * p.2) = |a⁻¹| • ∫ q, g q := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp only [zero_mul, add_zero, inv_zero, abs_zero, zero_smul]
    by_cases hint : Integrable fun p : ℝ × ℝ => g (p.1, p.1)
    · rw [Measure.volume_eq_prod, integral_prod _ hint]
      refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
      by_cases hE : CompleteSpace E
      · simp [integral_const, measureReal_def]
      · exact integral_of_not_completeSpace hE
    · exact integral_undef hint
  · rw [(measurePreserving_prod_add_mul ha).integral_comp (measurableEmbedding_prod_add_mul ha),
      integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _)]

end EpsilonEridani
