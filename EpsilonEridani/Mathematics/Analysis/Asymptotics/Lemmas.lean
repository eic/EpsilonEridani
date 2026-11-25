/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Comparisons with `x⁻¹` along a filter

Elementary estimates for functions on a normed division ring (such as `ℝ` or `ℂ`) against powers
of `x⁻¹`, along an arbitrary filter:

* `Asymptotics.IsBigO.inv_of_mul`: if `x f(x)` is bounded along a filter on which `x` is
  eventually nonzero, then `f(x) = O(1 / x)`;
* `Asymptotics.IsBigO.inv_of_mul_sub`: the same when `x f(x)` is within `O(1)` of a bounded
  function;
* `Asymptotics.IsBigO.div_inv`: a bounded function divided by `x` is `O(1 / x)`;
* `Asymptotics.IsBigO.inv_mul_inv_sq`: multiplying an `O(1 / x)` function by `x⁻¹` gives an
  `O(1 / x ^ 2)` function;
* `Asymptotics.isLittleO_inv_sq_inv`: along a filter on which `x⁻¹ → 0`, `1 / x ^ 2 = o(1 / x)`.

They are the estimates by which large-argument asymptotics of special functions, such as the
spherical Bessel functions, are reduced from bounds on `x f(x)` to bounds on `f(x)`; the forms
along `cocompact 𝕜` are in `EpsilonEridani.Mathematics.Analysis.Asymptotics.Cocompact`.
-/

public section

open Filter Topology

namespace Asymptotics

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] {l : Filter 𝕜}

/-- If `x f(x)` is bounded along a filter on which `x` is eventually nonzero, then
`f(x) = O(1 / x)` there, since `f(x) = x⁻¹ (x f(x))` for `x ≠ 0`. -/
theorem IsBigO.inv_of_mul {f : 𝕜 → 𝕜} (h : (fun x => x * f x) =O[l] fun _ => (1 : 𝕜))
    (h₀ : ∀ᶠ x in l, x ≠ 0) : f =O[l] fun x => x⁻¹ := by
  refine ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul h).congr' ?_ (.of_forall fun x => mul_one _)
  filter_upwards [h₀] with x hx
  rw [inv_mul_cancel_left₀ hx]

/-- If `x f(x)` is within `O(1)` of a bounded function `g` along a filter on which `x` is
eventually nonzero, then `f(x) = O(1 / x)`: `x f(x)` is then itself bounded. -/
theorem IsBigO.inv_of_mul_sub {f g : 𝕜 → 𝕜}
    (h : (fun x => x * f x - g x) =O[l] fun _ => (1 : 𝕜)) (hg : g =O[l] fun _ => (1 : 𝕜))
    (h₀ : ∀ᶠ x in l, x ≠ 0) : f =O[l] fun x => x⁻¹ :=
  ((h.add hg).congr_left fun _ => sub_add_cancel _ _).inv_of_mul h₀

/-- A bounded function divided by `x` is `O(1 / x)`. -/
theorem IsBigO.div_inv {f : 𝕜 → 𝕜} (h : f =O[l] fun _ => (1 : 𝕜)) :
    (fun x => f x / x) =O[l] fun x => x⁻¹ :=
  (h.mul (isBigO_refl (fun x : 𝕜 => x⁻¹) _)).congr (fun _ => (div_eq_mul_inv _ _).symm)
    fun _ => one_mul _

/-- Multiplying an `O(1 / x)` function by `x⁻¹` gives an `O(1 / x ^ 2)` function. -/
theorem IsBigO.inv_mul_inv_sq {f : 𝕜 → 𝕜} (h : f =O[l] fun x => x⁻¹) :
    (fun x => x⁻¹ * f x) =O[l] fun x => (x ^ 2)⁻¹ :=
  ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul h).congr_right fun x => by rw [← sq, inv_pow]

/-- Along a filter on which `x⁻¹ → 0`, `1 / x ^ 2` decays faster than `1 / x`. -/
theorem isLittleO_inv_sq_inv (h : Tendsto (fun x : 𝕜 => x⁻¹) l (𝓝 0)) :
    (fun x : 𝕜 => (x ^ 2)⁻¹) =o[l] fun x => x⁻¹ :=
  ((isBigO_refl (fun x : 𝕜 => x⁻¹) _).mul_isLittleO ((isLittleO_one_iff 𝕜).2 h)).congr
    (fun x => by rw [← sq, inv_pow]) fun _ => mul_one _

end Asymptotics
