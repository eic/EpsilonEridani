/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Analysis.Asymptotics.Lemmas
public import EpsilonEridani.Mathematics.Topology.Compactness.Compact
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Decay of `x⁻¹` at infinity

Estimates for functions on a proper normed division ring (such as `ℝ` or `ℂ`) as `‖x‖ → ∞`, the
limit expressed by the filter `cocompact 𝕜`:

* `Filter.tendsto_inv₀_cocompact`: `x⁻¹ → 0` along `cocompact 𝕜`;
* `Asymptotics.IsBigO.inv_of_mul_sub_cocompact`: if `x f(x)` is within `O(1 / x)` of a bounded
  function along `cocompact 𝕜`, then `f(x) = O(1 / x)`;
* `Asymptotics.isLittleO_inv_sq_inv_cocompact`: `1 / x ^ 2 = o(1 / x)` along `cocompact 𝕜`.

They specialise the filter-general estimates of
`EpsilonEridani.Mathematics.Analysis.Asymptotics.Lemmas` to `cocompact 𝕜`, on which `x` is
eventually nonzero (`Filter.eventually_ne_cocompact`) and `x⁻¹` is bounded.
-/

public section

open Filter Topology

namespace Filter

/-- In a proper normed division ring, `x⁻¹ → 0` as `‖x‖ → ∞`. -/
theorem tendsto_inv₀_cocompact {𝕜 : Type*} [NormedDivisionRing 𝕜] [ProperSpace 𝕜] :
    Tendsto (fun x : 𝕜 => x⁻¹) (cocompact 𝕜) (𝓝 0) := by
  rw [← Metric.cobounded_eq_cocompact]
  exact tendsto_inv₀_cobounded

end Filter

namespace Asymptotics

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [ProperSpace 𝕜]

/-- If `x f(x)` is within `O(1 / x)` of a bounded function `g` along `cocompact 𝕜`, then
`f(x) = O(1 / x)`: since `x⁻¹` is bounded there, this is `Asymptotics.IsBigO.inv_of_mul_sub`. -/
theorem IsBigO.inv_of_mul_sub_cocompact {f g : 𝕜 → 𝕜}
    (h : (fun x => x * f x - g x) =O[cocompact 𝕜] fun x => x⁻¹)
    (hg : g =O[cocompact 𝕜] fun _ => (1 : 𝕜)) : f =O[cocompact 𝕜] fun x => x⁻¹ :=
  (h.trans (tendsto_inv₀_cocompact.isBigO_one 𝕜)).inv_of_mul_sub hg (eventually_ne_cocompact 0)

/-- As `‖x‖ → ∞`, `1 / x ^ 2` decays faster than `1 / x`. -/
theorem isLittleO_inv_sq_inv_cocompact :
    (fun x : 𝕜 => (x ^ 2)⁻¹) =o[cocompact 𝕜] fun x => x⁻¹ :=
  isLittleO_inv_sq_inv tendsto_inv₀_cocompact

end Asymptotics
