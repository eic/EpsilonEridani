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
triangle under the exchange of the two coordinates. Both Fubini statements are the slice-by-slice
Fubini theorem `EpsilonEridani.setIntegral_prod_eq_integral_setIntegral_mk_preimage` for a
measurable subset of a product, applied after exchanging the coordinates, once the slices of the
triangle are computed.

The same triangle appears in `ℂ` as `TauCeti.Green.standardTriangle`, whose graph-cell API
(`TauCeti.Green.integral_horizontalRegion`, `TauCeti.Green.integrable_verticalRegion_fiberIntegral`,
`TauCeti.Green.integral_comp_coordinateSwapCLE_verticalRegion`) gives the analogous Fubini and
coordinate-swap statements. The `ℝ × ℝ` formulation here is deliberate: the integrands are
functions of a pair of real momentum fractions, and with `ℝ × ℝ` the coordinate swap is
Mathlib's measure-preserving `Prod.swap` and Fubini is the product-measure theorem directly, so no
transport along `Complex.measurableEquivRealProd` is needed.

## Main definitions

* `EpsilonEridani.unitTriangle`: the closed unit triangle, a compact set
  (`EpsilonEridani.isCompact_unitTriangle`).

## Main statements

* `EpsilonEridani.setIntegral_unitTriangle`: Fubini on the triangle, the first coordinate
  innermost.
* `EpsilonEridani.integrableOn_Icc_intervalIntegral_of_integrableOn_unitTriangle`: the outer
  integrand of that formula is integrable on `[0, 1]`.
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

@[simp]
theorem mem_unitTriangle {p : ℝ × ℝ} :
    p ∈ unitTriangle ↔ 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 1 :=
  Iff.rfl

theorem isClosed_unitTriangle : IsClosed unitTriangle := by
  -- `unitTriangle` is the intersection of the three half-planes cut out by its inequalities.
  simp only [unitTriangle, ofPred_and]
  exact (isClosed_le continuous_const continuous_fst).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const))

@[simp, measurability]
theorem measurableSet_unitTriangle : MeasurableSet unitTriangle :=
  isClosed_unitTriangle.measurableSet

theorem unitTriangle_subset_Icc_prod_Icc :
    unitTriangle ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 := fun p ⟨h1, h2, h12⟩ =>
  ⟨⟨h1, by linarith⟩, h2, by linarith⟩

theorem isCompact_unitTriangle : IsCompact unitTriangle :=
  (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset isClosed_unitTriangle
    unitTriangle_subset_Icc_prod_Icc

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
  exact setIntegral_preimage_swap unitTriangle g

omit [NormedSpace ℝ E] in
/-- Integrability on the unit triangle is invariant under exchanging the two coordinates. -/
theorem integrableOn_unitTriangle_comp_swap_iff {g : ℝ × ℝ → E} :
    IntegrableOn (fun p => g p.swap) unitTriangle ↔ IntegrableOn g unitTriangle := by
  conv_lhs => rw [← preimage_swap_unitTriangle]
  exact integrableOn_preimage_swap_iff

/-- The slice `{x | (y, x) ∈ unitTriangle}` of the unit triangle at `y ≥ 0` is `[0, 1 - y]`, which
is empty for `y > 1`. -/
theorem mk_preimage_unitTriangle_of_nonneg {y : ℝ} (hy : 0 ≤ y) :
    Prod.mk y ⁻¹' unitTriangle = Icc 0 (1 - y) := by
  ext x
  simp only [mem_preimage, mem_unitTriangle, mem_Icc]
  constructor
  · rintro ⟨-, hx, hxy⟩
    exact ⟨hx, by linarith⟩
  · rintro ⟨hx, hxy⟩
    exact ⟨hy, hx, by linarith⟩

/-- The slice `{x | (y, x) ∈ unitTriangle}` of the unit triangle at `y ∉ [0, 1]` is empty. -/
theorem mk_preimage_unitTriangle_eq_empty_of_notMem_Icc {y : ℝ} (hy : y ∉ Icc (0 : ℝ) 1) :
    Prod.mk y ⁻¹' unitTriangle = ∅ :=
  eq_empty_of_forall_notMem fun _ ⟨hy0, hx, hxy⟩ => hy ⟨hy0, by linarith⟩

/-- The integral of `g (·, y)` over the slice of the unit triangle at `y`: the interval integral
`∫_0^{1-y} dx g(x, y)` for `y ∈ [0, 1]`, and zero otherwise. -/
private theorem setIntegral_mk_preimage_unitTriangle (g : ℝ × ℝ → E) (y : ℝ) :
    ∫ x in Prod.mk y ⁻¹' unitTriangle, g (x, y) =
      (Icc (0 : ℝ) 1).indicator (fun y => ∫ x in 0..1 - y, g (x, y)) y := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · rw [mk_preimage_unitTriangle_of_nonneg hy.1, indicator_of_mem hy, integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith [hy.2])]
  · rw [mk_preimage_unitTriangle_eq_empty_of_notMem_Icc hy, setIntegral_empty,
      indicator_of_notMem hy]

/-- **Fubini on the unit triangle**, with the first coordinate integrated innermost:
`∫_{triangle} g = ∫_0^1 dy ∫_0^{1-y} dx g(x, y)`. -/
theorem setIntegral_unitTriangle {g : ℝ × ℝ → E} (hg : IntegrableOn g unitTriangle) :
    ∫ p in unitTriangle, g p = ∫ y in Icc (0 : ℝ) 1, ∫ x in 0..1 - y, g (x, y) := by
  rw [← setIntegral_unitTriangle_comp_swap, Measure.volume_eq_prod,
    setIntegral_prod_eq_integral_setIntegral_mk_preimage measurableSet_unitTriangle
      (integrableOn_unitTriangle_comp_swap_iff.2 hg), ← integral_indicator measurableSet_Icc]
  simp only [Prod.swap_prod_mk, setIntegral_mk_preimage_unitTriangle]

/-- The outer integrand `y ↦ ∫_0^{1-y} dx g(x, y)` of `setIntegral_unitTriangle` is integrable
on `[0, 1]`. -/
theorem integrableOn_Icc_intervalIntegral_of_integrableOn_unitTriangle {g : ℝ × ℝ → E}
    (hg : IntegrableOn g unitTriangle) :
    IntegrableOn (fun y => ∫ x in 0..1 - y, g (x, y)) (Icc (0 : ℝ) 1) := by
  rw [← integrable_indicator_iff measurableSet_Icc]
  refine (integrable_setIntegral_mk_preimage (g := fun p => g p.swap) measurableSet_unitTriangle
    (integrableOn_unitTriangle_comp_swap_iff.2 hg)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [Prod.swap_prod_mk, setIntegral_mk_preimage_unitTriangle]

end EpsilonEridani
