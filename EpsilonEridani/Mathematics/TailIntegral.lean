/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Integrals over a tail interval `[x, b]`

This module collects facts about the set integral `∫ y in Icc x b, h y` as a function of its
lower endpoint `x`, as used for densities on the momentum-fraction interval.

## Main results

- `div_mem_Ioc_of_pos_of_le`: for `0 < x ≤ y`, the ratio `x / y` lies in `(0,1]`.
- `setIntegral_Icc_comp_div_div`: the measure `dy / y` on `[x,1]` is invariant under
  `y ↦ x / y`, i.e. `∫_x^1 h (x / y) dy / y = ∫_x^1 h y dy / y` for `0 < x`.
- `tendsto_setIntegral_Icc_nhdsLT`: the tail integral `∫ y in Icc x b, h y` tends to `0` as
  `x → b⁻`, for every `h`.

Nothing in this file is physics-specific.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace EpsilonEridani

/-- For `0 < x ≤ y`, the ratio `x / y` lies in `(0,1]`. -/
theorem div_mem_Ioc_of_pos_of_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : x / y ∈ Ioc (0 : ℝ) 1 :=
  have hy : 0 < y := hx.trans_le hxy
  ⟨div_pos hx hy, (div_le_one hy).mpr hxy⟩

/-- The measure `dy / y` on `[x,1]` is invariant under `y ↦ x / y`: for `0 < x`,
`∫_{[x,1]} h (x / y) / y dy = ∫_{[x,1]} h y / y dy`. -/
theorem setIntegral_Icc_comp_div_div (h : ℝ → ℝ) {x : ℝ} (hx : 0 < x) :
    ∫ y in Icc x 1, h (x / y) / y = ∫ y in Icc x 1, h y / y := by
  have himage : (fun u => x / u) '' Icc x 1 = Icc x 1 := by
    refine Subset.antisymm ?_ fun v hv => ?_
    · rintro _ ⟨u, hu, rfl⟩
      exact ⟨(le_div_iff₀ (hx.trans_le hu.1)).mpr (by nlinarith [hu.2]),
        (div_mem_Ioc_of_pos_of_le hx hu.1).2⟩
    · refine ⟨x / v, ⟨(le_div_iff₀ (hx.trans_le hv.1)).mpr (by nlinarith [hv.2]),
        (div_mem_Ioc_of_pos_of_le hx hv.1).2⟩, div_div_cancel₀ hx.ne'⟩
  have hderiv : ∀ u ∈ Icc x 1,
      HasDerivWithinAt (fun u => x / u) (-x / u ^ 2) (Icc x 1) u := fun u hu => by
    convert ((hasDerivAt_inv (hx.trans_le hu.1).ne').const_mul x).hasDerivWithinAt using 1
    · funext y
      exact div_eq_mul_inv x y
    · ring
  have hinj : InjOn (fun u => x / u) (Icc x 1) := fun u _ v _ huv => by
    simpa [div_div_cancel₀ hx.ne'] using congrArg (x / ·) huv
  conv_rhs =>
    rw [← himage, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc hderiv hinj]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  have hu0 : 0 < u := hx.trans_le hu.1
  simp only [smul_eq_mul, neg_div, abs_neg, abs_of_pos (by positivity :
    0 < x / u ^ 2)]
  field_simp

/-- The tail integral `∫ y in Icc x b, h y` tends to `0` as `x` tends to `b` from the left, for
every `h`. -/
theorem tendsto_setIntegral_Icc_nhdsLT {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ℝ → E) (b : ℝ) :
    Tendsto (fun x => ∫ y in Icc x b, h y) (𝓝[<] b) (𝓝 0) := by
  by_cases hint : ∃ a < b, IntegrableOn h (Icc a b)
  · obtain ⟨a, hab, hint⟩ := hint
    have hcont := intervalIntegral.continuousOn_primitive_interval_left (μ := volume)
      (by rwa [uIcc_of_le hab.le] : IntegrableOn h (uIcc a b))
    have htends := (hcont b right_mem_uIcc).tendsto.mono_left
      (nhdsWithin_le_of_mem (by rw [uIcc_of_le hab.le]; exact Icc_mem_nhdsLT hab))
    rw [intervalIntegral.integral_same] at htends
    refine htends.congr' (eventually_nhdsWithin_of_forall fun x (hx : x < b) => ?_)
    rw [intervalIntegral.integral_of_le hx.le]
    exact integral_Icc_eq_integral_Ioc.symm
  · simp only [not_exists, not_and] at hint
    refine tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun x (hx : x < b) => ?_)
    exact (integral_undef (hint x hx)).symm

end EpsilonEridani
