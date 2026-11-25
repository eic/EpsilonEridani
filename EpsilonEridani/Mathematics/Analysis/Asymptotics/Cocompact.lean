/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Topology.MetricSpace.Bounded
public import EpsilonEridani.Mathematics.Topology.Compactness.Compact

/-!
# Decay of `x⁻¹` at infinity

Elementary facts for estimating functions on a proper normed division ring (such as `ℝ` or `ℂ`)
as `‖x‖ → ∞`, the limit expressed by the filter `cocompact 𝕜`:

* `Filter.tendsto_inv₀_cocompact`: `x⁻¹ → 0` along `cocompact 𝕜`;
* `Asymptotics.IsBigO.inv_of_mul`: if `x f(x)` is bounded along a filter on which `x` is
  eventually nonzero, such as `cocompact 𝕜`, then `f(x) = O(1 / x)`;
* `Asymptotics.IsBigO.inv_of_mul_sub_cocompact`: if `x f(x)` is within `O(1 / x)` of a bounded
  function along `cocompact 𝕜`, then `f(x) = O(1 / x)`;
* `Asymptotics.IsBigO.inv_mul_inv_sq`: multiplying an `O(1 / x)` function by `x⁻¹` gives an
  `O(1 / x ^ 2)` function;
* `Asymptotics.isLittleO_inv_sq_inv`: along a filter on which `x⁻¹ → 0`, `1 / x ^ 2 = o(1 / x)`,
  and `Asymptotics.isLittleO_inv_sq_inv_cocompact`: the same along `cocompact 𝕜`.

That a point is eventually avoided along `cocompact 𝕜` is `Filter.eventually_ne_cocompact`.

They are the estimates by which large-argument asymptotics of special functions, such as the
spherical Bessel functions, are reduced from `O(1 / x)` bounds on `x f(x)` to bounds on `f(x)`.
-/

public section

open Filter Topology Asymptotics

namespace Filter

/-- In a proper normed division ring, `x⁻¹ → 0` as `‖x‖ → ∞`. -/
theorem tendsto_inv₀_cocompact {𝕜 : Type*} [NormedDivisionRing 𝕜] [ProperSpace 𝕜] :
    Tendsto (fun x : 𝕜 => x⁻¹) (cocompact 𝕜) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_inv₀_cobounded

end Filter

namespace Asymptotics

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {l : Filter 𝕜}

/-- If `x f(x)` is bounded along a filter on which `x` is eventually nonzero, then
`f(x) = O(1 / x)` there, since `f(x) = x⁻¹ (x f(x))` for `x ≠ 0`. -/
theorem IsBigO.inv_of_mul {f : 𝕜 → 𝕜} (h : (fun x => x * f x) =O[l] fun _ => (1 : 𝕜))
    (h₀ : ∀ᶠ x in l, x ≠ 0) : f =O[l] fun x => x⁻¹ := by
  refine ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul h).congr' ?_ (.of_forall fun x => mul_one _)
  filter_upwards [h₀] with x hx
  rw [inv_mul_cancel_left₀ hx]

/-- If `x f(x)` is within `O(1 / x)` of a bounded function `g` along `cocompact 𝕜`, then
`f(x) = O(1 / x)`: since `x⁻¹` is bounded there, `x f(x)` is itself bounded
(`Asymptotics.IsBigO.inv_of_mul`). -/
theorem IsBigO.inv_of_mul_sub_cocompact [ProperSpace 𝕜] {f g : 𝕜 → 𝕜}
    (h : (fun x => x * f x - g x) =O[cocompact 𝕜] fun x => x⁻¹)
    (hg : g =O[cocompact 𝕜] fun _ => (1 : 𝕜)) : f =O[cocompact 𝕜] fun x => x⁻¹ :=
  (((h.trans (tendsto_inv₀_cocompact.isBigO_one 𝕜)).add hg).congr_left
    fun _ => sub_add_cancel _ _).inv_of_mul (eventually_ne_cocompact 0)

/-- Multiplying an `O(1 / x)` function by `x⁻¹` gives an `O(1 / x ^ 2)` function. -/
theorem IsBigO.inv_mul_inv_sq {f : 𝕜 → 𝕜} (h : f =O[l] fun x => x⁻¹) :
    (fun x => x⁻¹ * f x) =O[l] fun x => (x ^ 2)⁻¹ :=
  ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul h).congr_right fun x => by rw [← sq, inv_pow]

/-- Along a filter on which `x⁻¹ → 0`, `1 / x ^ 2` decays faster than `1 / x`. -/
theorem isLittleO_inv_sq_inv (h : Tendsto (fun x : 𝕜 => x⁻¹) l (𝓝 0)) :
    (fun x : 𝕜 => (x ^ 2)⁻¹) =o[l] fun x => x⁻¹ :=
  ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 h)).congr
    (fun x => by rw [← sq, inv_pow]) fun _ => mul_one _

/-- As `‖x‖ → ∞`, `1 / x ^ 2` decays faster than `1 / x`. -/
theorem isLittleO_inv_sq_inv_cocompact [ProperSpace 𝕜] :
    (fun x : 𝕜 => (x ^ 2)⁻¹) =o[cocompact 𝕜] fun x => x⁻¹ :=
  isLittleO_inv_sq_inv tendsto_inv₀_cocompact

end Asymptotics
