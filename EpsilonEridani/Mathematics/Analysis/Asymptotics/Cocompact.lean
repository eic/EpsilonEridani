/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Decay of `x⁻¹` at infinity

Elementary facts for estimating functions on a proper normed division ring (such as `ℝ` or `ℂ`)
as `‖x‖ → ∞`, the limit expressed by the filter `cocompact 𝕜`:

* `Filter.eventually_ne_cocompact`: a point is eventually avoided along `cocompact X`;
* `Filter.tendsto_inv₀_cocompact`: `x⁻¹ → 0` along `cocompact 𝕜`;
* `Asymptotics.isBigO_inv_of_isBigO_mul_one`: if `x f(x)` is bounded along a filter on which `x`
  is eventually nonzero, such as `cocompact 𝕜`, then `f(x) = O(1 / x)`;
* `Asymptotics.isBigO_inv_of_isBigO_mul_sub_inv`: if `x f(x)` is within `O(1 / x)` of a bounded
  function along `cocompact 𝕜`, then `f(x) = O(1 / x)`;
* `Asymptotics.isBigO_inv_mul_inv_sq`: multiplying an `O(1 / x)` function by `x⁻¹` gives an
  `O(1 / x ^ 2)` function;
* `Real.isBigO_sin_comp_one`: `sin (f x)` is bounded along any filter.

They are the estimates by which large-argument asymptotics of special functions, such as the
spherical Bessel functions, are reduced from `O(1 / x)` bounds on `x f(x)` to bounds on `f(x)`.
-/

public section

open Filter Topology Asymptotics

namespace Filter

/-- Along `cocompact X`, a given point `a` is eventually avoided. -/
theorem eventually_ne_cocompact {X : Type*} [TopologicalSpace X] (a : X) :
    ∀ᶠ x in cocompact X, x ≠ a := by
  filter_upwards [isCompact_singleton.compl_mem_cocompact] with x hx
  exact Set.mem_compl_singleton_iff.mp hx

/-- In a proper normed division ring, `x⁻¹ → 0` as `‖x‖ → ∞`. -/
theorem tendsto_inv₀_cocompact {𝕜 : Type*} [NormedDivisionRing 𝕜] [ProperSpace 𝕜] :
    Tendsto (fun x : 𝕜 => x⁻¹) (cocompact 𝕜) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_inv₀_cobounded

end Filter

namespace Asymptotics

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-- If `x f(x)` is bounded along a filter on which `x` is eventually nonzero, then
`f(x) = O(1 / x)` there, since `f(x) = x⁻¹ (x f(x))` for `x ≠ 0`. -/
theorem isBigO_inv_of_isBigO_mul_one {l : Filter 𝕜} {f : 𝕜 → 𝕜} (h₀ : ∀ᶠ x in l, x ≠ 0)
    (h : (fun x => x * f x) =O[l] fun _ => (1 : 𝕜)) :
    f =O[l] fun x => x⁻¹ := by
  refine ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul h).congr' ?_ (.of_forall fun x => mul_one _)
  filter_upwards [h₀] with x hx
  rw [inv_mul_cancel_left₀ hx]

/-- If `x f(x)` is within `O(1 / x)` of a bounded function `g` along `cocompact 𝕜`, then
`f(x) = O(1 / x)`: `x f(x)` is then itself bounded. -/
theorem isBigO_inv_of_isBigO_mul_sub_inv [ProperSpace 𝕜] {f g : 𝕜 → 𝕜}
    (h : (fun x => x * f x - g x) =O[cocompact 𝕜] fun x => x⁻¹)
    (hg : g =O[cocompact 𝕜] fun _ => (1 : 𝕜)) :
    f =O[cocompact 𝕜] fun x => x⁻¹ :=
  isBigO_inv_of_isBigO_mul_one (eventually_ne_cocompact 0) <|
    ((h.trans (tendsto_inv₀_cocompact.isBigO_one 𝕜)).add hg).congr_left fun _ => sub_add_cancel _ _

/-- Multiplying an `O(1 / x)` function by `x⁻¹` gives an `O(1 / x ^ 2)` function. -/
theorem isBigO_inv_mul_inv_sq {l : Filter 𝕜} {f : 𝕜 → 𝕜} (h : f =O[l] fun x => x⁻¹) :
    (fun x => x⁻¹ * f x) =O[l] fun x => (x ^ 2)⁻¹ :=
  ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul h).congr_right fun x => by rw [← sq, inv_pow]

end Asymptotics

namespace Real

/-- The sine of any function is bounded, along any filter. -/
theorem isBigO_sin_comp_one {α : Type*} (l : Filter α) (f : α → ℝ) :
    (fun x => sin (f x)) =O[l] fun _ => (1 : ℝ) :=
  .of_bound 1 (.of_forall fun x => by simpa using abs_sin_le_one (f x))

end Real
