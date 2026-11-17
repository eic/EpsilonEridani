/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrals over the unit triangle

The closed unit triangle `{(x, y) | 0 ≤ x, 0 ≤ y, x + y ≤ 1}` in `ℝ × ℝ` is the domain of a pair
of momentum fractions that share one unit of momentum. This file gives the Fubini theorem for it
in the form that integrates the first coordinate innermost,

`∫_{triangle} g = ∫_0^1 dy ∫_0^{1-y} dx g(x, y)`,

together with the integrability of the outer integrand, and the invariance of integrals over the
triangle under the exchange of the two coordinates. Combining the two gives the other order of
integration.

## Main definitions

* `EpsilonEridani.unitTriangle`: the closed unit triangle, a compact set
  (`EpsilonEridani.isCompact_unitTriangle`).

## Main statements

* `EpsilonEridani.setIntegral_unitTriangle`: Fubini on the triangle, the first coordinate
  innermost.
* `EpsilonEridani.integrableOn_integral_unitTriangle`: the outer integrand of that formula is
  integrable on `[0, 1]`.
* `EpsilonEridani.setIntegral_unitTriangle_comp_swap`: integrals over the triangle are invariant
  under exchanging the two coordinates.
-/

public section

noncomputable section

namespace EpsilonEridani

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit triangle `{(x, y) | 0 ≤ x, 0 ≤ y, x + y ≤ 1}`. -/
def unitTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1}

theorem mem_unitTriangle {p : ℝ × ℝ} :
    p ∈ unitTriangle ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 :=
  Iff.rfl

theorem measurableSet_unitTriangle : MeasurableSet unitTriangle :=
  (measurableSet_le measurable_const measurable_fst).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le (measurable_fst.add measurable_snd) measurable_const))

theorem isClosed_unitTriangle : IsClosed unitTriangle :=
  (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

theorem unitTriangle_subset_Icc_prod_Icc :
    unitTriangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun p ⟨h1, h2, h12⟩ =>
  ⟨⟨h1, by linarith⟩, h2, by linarith⟩

theorem isCompact_unitTriangle : IsCompact unitTriangle :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_unitTriangle
    unitTriangle_subset_Icc_prod_Icc

@[simp]
theorem swap_mem_unitTriangle {p : ℝ × ℝ} : p.swap ∈ unitTriangle ↔ p ∈ unitTriangle := by
  simp only [mem_unitTriangle, Prod.fst_swap, Prod.snd_swap, add_comm p.2]
  tauto

@[simp]
theorem preimage_swap_unitTriangle : Prod.swap ⁻¹' unitTriangle = unitTriangle :=
  Set.ext fun _ => swap_mem_unitTriangle

/-- A point lies in the unit triangle exactly when its second coordinate lies in `[0, 1]` and its
first in `[0, 1 - y]`. -/
theorem mk_mem_unitTriangle_iff {x y : ℝ} :
    (x, y) ∈ unitTriangle ↔ y ∈ Icc (0 : ℝ) 1 ∧ x ∈ Icc 0 (1 - y) := by
  simp only [mem_unitTriangle, mem_Icc]
  constructor
  · rintro ⟨hx, hy, hxy⟩
    exact ⟨⟨hy, by linarith⟩, hx, by linarith⟩
  · rintro ⟨⟨hy, -⟩, hx, hxy⟩
    exact ⟨hx, hy, by linarith⟩

/-- The integral of the extension by zero of `g` along a horizontal line. -/
theorem integral_indicator_unitTriangle_mk (g : ℝ × ℝ → E) (y : ℝ) :
    ∫ x, unitTriangle.indicator g (x, y) =
      (Icc (0 : ℝ) 1).indicator (fun y => ∫ x in Icc 0 (1 - y), g (x, y)) y := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · rw [indicator_of_mem hy, ← integral_indicator measurableSet_Icc]
    congr 1 with x
    by_cases hx : x ∈ Icc 0 (1 - y)
    · rw [indicator_of_mem (mk_mem_unitTriangle_iff.2 ⟨hy, hx⟩), indicator_of_mem hx]
    · rw [indicator_of_notMem (fun h => hx (mk_mem_unitTriangle_iff.1 h).2),
        indicator_of_notMem hx]
  · rw [indicator_of_notMem hy]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun x => ?_)
    exact indicator_of_notMem (fun h => hy (mk_mem_unitTriangle_iff.1 h).1) _

/-- **Fubini on the unit triangle**, with the first coordinate integrated innermost:
`∫_{triangle} g = ∫_0^1 dy ∫_0^{1-y} dx g(x, y)`. -/
theorem setIntegral_unitTriangle {g : ℝ × ℝ → E} (hg : IntegrableOn g unitTriangle) :
    ∫ p in unitTriangle, g p = ∫ y in Icc (0 : ℝ) 1, ∫ x in Icc 0 (1 - y), g (x, y) := by
  have hint : Integrable (unitTriangle.indicator g) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hg.integrable_indicator measurableSet_unitTriangle
  rw [← integral_indicator measurableSet_unitTriangle, Measure.volume_eq_prod,
    integral_prod_symm _ hint, ← integral_indicator measurableSet_Icc]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
    integral_indicator_unitTriangle_mk g y)

/-- The outer integrand `y ↦ ∫_0^{1-y} dx g(x, y)` of `setIntegral_unitTriangle` is integrable
on `[0, 1]`. -/
theorem integrableOn_integral_unitTriangle {g : ℝ × ℝ → E} (hg : IntegrableOn g unitTriangle) :
    IntegrableOn (fun y => ∫ x in Icc 0 (1 - y), g (x, y)) (Icc (0 : ℝ) 1) := by
  have hint : Integrable (unitTriangle.indicator g) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hg.integrable_indicator measurableSet_unitTriangle
  rw [← integrable_indicator_iff measurableSet_Icc]
  exact hint.integral_prod_right.congr
    (Filter.Eventually.of_forall fun y => integral_indicator_unitTriangle_mk g y)

/-- Integrals over the unit triangle are invariant under exchanging the two coordinates. -/
theorem setIntegral_unitTriangle_comp_swap (g : ℝ × ℝ → E) :
    ∫ p in unitTriangle, g p.swap = ∫ p in unitTriangle, g p := by
  have h : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    simpa only [← Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  conv_lhs => rw [← preimage_swap_unitTriangle]
  exact h.setIntegral_preimage_emb MeasurableEquiv.prodComm.measurableEmbedding g unitTriangle

omit [NormedSpace ℝ E] in
/-- Integrability on the unit triangle is invariant under exchanging the two coordinates. -/
theorem integrableOn_unitTriangle_comp_swap_iff {g : ℝ × ℝ → E} :
    IntegrableOn (fun p => g p.swap) unitTriangle ↔ IntegrableOn g unitTriangle := by
  have h : MeasurePreserving (Prod.swap : ℝ × ℝ → ℝ × ℝ) := by
    simpa only [← Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume))
  conv_lhs => rw [← preimage_swap_unitTriangle]
  exact h.integrableOn_comp_preimage MeasurableEquiv.prodComm.measurableEmbedding

end EpsilonEridani
