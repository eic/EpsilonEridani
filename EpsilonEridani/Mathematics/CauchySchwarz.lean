/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# The Cauchy-Schwarz inequality on a set of finite measure

For a function `G` that is square-integrable on a set `S` of finite measure, the integral of
`|G|` over `S` is bounded by the square root of the measure of `S` times the square root of the
integral of `G ^ 2` over `S`:

`(∫ y in S, |G y| ∂μ) ^ 2 ≤ μ.real S * ∫ y in S, G y ^ 2 ∂μ`

(`sq_setIntegral_abs_le_measureReal_mul_setIntegral_sq`). The statement is purely
measure-theoretic: it holds on an arbitrary measure space, for an arbitrary set of finite
measure. It is the `L¹`-`L²` estimate behind bounds that compare an average of a function with
the size of the region it lives on, such as the bound on the effective cross section of a
transverse profile confined to a region.
-/

public section

noncomputable section

open MeasureTheory Real

namespace EpsilonEridani
namespace CauchySchwarz

variable {T : Type*} [MeasurableSpace T] {μ : Measure T}

/-- The Cauchy-Schwarz inequality on a set of finite measure:
`(∫_S |G|)² ≤ |S| ∫_S G²` for `G` square-integrable on `S`. -/
theorem sq_setIntegral_abs_le_measureReal_mul_setIntegral_sq {G : T → ℝ} {S : Set T}
    (hμS : μ S ≠ ⊤) (hG2 : MemLp G 2 (μ.restrict S)) :
    (∫ y in S, |G y| ∂μ) ^ 2 ≤ μ.real S * ∫ y in S, G y ^ 2 ∂μ := by
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hμS
  -- Hölder with `p = q = 2` for `1 ⬝ |G|`: `∫_S |G| ≤ |S|^(1/2) (∫_S G²)^(1/2)`.
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict S) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ)) (g := |G|) (ae_of_all _ fun _ => zero_le_one)
    (ae_of_all _ fun y => abs_nonneg (G y)) (by simpa using memLp_const (1 : ℝ))
    (by simpa using hG2.abs)
  rw [← Real.sqrt_le_sqrt_iff (by positivity), Real.sqrt_sq (integral_nonneg fun y => abs_nonneg _),
    Real.sqrt_mul measureReal_nonneg, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa [Real.rpow_two] using hcs

end CauchySchwarz
end EpsilonEridani
