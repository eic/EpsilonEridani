/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import EpsilonEridani.Mathematics.MeasureTheory.SetIntegralProd

/-!
# Integrals over the unit triangle

The closed unit triangle `{(x, y) | 0 ≤ x, 0 ≤ y, x + y ≤ 1}` in `ℝ × ℝ` is the domain of a pair
of momentum fractions that share one unit of momentum. This file gives the Fubini theorem for it
in the form that integrates the first coordinate innermost,

`∫_{triangle} g = ∫_0^1 dy ∫_0^{1-y} dx g(x, y)`,

together with the integrability of the outer integrand, and the invariance of integrals over the
triangle under the exchange of the two coordinates. Combining the two gives the other order of
integration. Both Fubini statements are the slice-by-slice Fubini theorem
`EpsilonEridani.setIntegral_prod_eq_integral_setIntegral_preimage_mk` for a measurable subset of a
product, applied after exchanging the coordinates, once the slices of the triangle are computed.

## Main definitions

* `EpsilonEridani.unitTriangle`: the closed unit triangle, a compact set
  (`EpsilonEridani.isCompact_unitTriangle`).

## Main statements

* `EpsilonEridani.setIntegral_unitTriangle`: Fubini on the triangle, the first coordinate
  innermost.
* `EpsilonEridani.integrableOn_Icc_integral_unitTriangle`: the outer integrand of that formula is
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

@[simp, measurability]
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

/-- Integrals over the unit triangle are invariant under exchanging the two coordinates. -/
theorem setIntegral_unitTriangle_comp_swap (g : ℝ × ℝ → E) :
    ∫ p in unitTriangle, g p.swap = ∫ p in unitTriangle, g p := by
  conv_lhs => rw [← preimage_swap_unitTriangle]
  exact Measure.measurePreserving_swap.setIntegral_preimage_emb
    MeasurableEquiv.prodComm.measurableEmbedding g unitTriangle

omit [NormedSpace ℝ E] in
/-- Integrability on the unit triangle is invariant under exchanging the two coordinates. -/
theorem integrableOn_unitTriangle_comp_swap_iff {g : ℝ × ℝ → E} :
    IntegrableOn (fun p => g p.swap) unitTriangle ↔ IntegrableOn g unitTriangle := by
  conv_lhs => rw [← preimage_swap_unitTriangle]
  exact Measure.measurePreserving_swap.integrableOn_comp_preimage
    MeasurableEquiv.prodComm.measurableEmbedding

/-- The slice `{x | (y, x) ∈ unitTriangle}` of the unit triangle at `y ∈ [0, 1]` is `[0, 1 - y]`. -/
theorem preimage_mk_unitTriangle_of_mem {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Prod.mk y ⁻¹' unitTriangle = Icc 0 (1 - y) := by
  ext x
  simp only [mem_preimage, mem_unitTriangle, mem_Icc]
  constructor
  · rintro ⟨-, hx, hxy⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨hy.1, hx, by linarith⟩

/-- The slice `{x | (y, x) ∈ unitTriangle}` of the unit triangle at `y ∉ [0, 1]` is empty. -/
theorem preimage_mk_unitTriangle_of_notMem {y : ℝ} (hy : y ∉ Icc (0 : ℝ) 1) :
    Prod.mk y ⁻¹' unitTriangle = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨hy0, hx, hxy⟩ => hy ⟨hy0, by linarith⟩

/-- The integral of `g (·, y)` over the slice of the unit triangle at `y`: the interval integral
`∫_0^{1-y} dx g(x, y)` for `y ∈ [0, 1]`, and zero otherwise. -/
theorem setIntegral_preimage_mk_unitTriangle (g : ℝ × ℝ → E) (y : ℝ) :
    ∫ x in Prod.mk y ⁻¹' unitTriangle, g (x, y) =
      (Icc (0 : ℝ) 1).indicator (fun y => ∫ x in 0..1 - y, g (x, y)) y := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · rw [preimage_mk_unitTriangle_of_mem hy, indicator_of_mem hy, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith [hy.2])]
  · rw [preimage_mk_unitTriangle_of_notMem hy, setIntegral_empty, indicator_of_notMem hy]

/-- **Fubini on the unit triangle**, with the first coordinate integrated innermost:
`∫_{triangle} g = ∫_0^1 dy ∫_0^{1-y} dx g(x, y)`. -/
theorem setIntegral_unitTriangle {g : ℝ × ℝ → E} (hg : IntegrableOn g unitTriangle) :
    ∫ p in unitTriangle, g p = ∫ y in Icc (0 : ℝ) 1, ∫ x in 0..1 - y, g (x, y) := by
  rw [← setIntegral_unitTriangle_comp_swap, Measure.volume_eq_prod,
    setIntegral_prod_eq_integral_setIntegral_preimage_mk measurableSet_unitTriangle
      (integrableOn_unitTriangle_comp_swap_iff.2 hg), ← integral_indicator measurableSet_Icc]
  simp only [Prod.swap_prod_mk, setIntegral_preimage_mk_unitTriangle]

/-- The outer integrand `y ↦ ∫_0^{1-y} dx g(x, y)` of `setIntegral_unitTriangle` is integrable
on `[0, 1]`. -/
theorem integrableOn_Icc_integral_unitTriangle {g : ℝ × ℝ → E}
    (hg : IntegrableOn g unitTriangle) :
    IntegrableOn (fun y => ∫ x in 0..1 - y, g (x, y)) (Icc (0 : ℝ) 1) := by
  rw [← integrable_indicator_iff measurableSet_Icc]
  refine (integrable_setIntegral_preimage_mk (g := fun p => g p.swap) measurableSet_unitTriangle
    (integrableOn_unitTriangle_comp_swap_iff.2 hg)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [Prod.swap_prod_mk, setIntegral_preimage_mk_unitTriangle]

end EpsilonEridani
