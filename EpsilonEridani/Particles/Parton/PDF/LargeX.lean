/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.Model

/-!
# The large-`x` exponent of a density

Near the kinematic endpoint `x → 1` a parton density typically behaves as a power of `1 - x`:
`f(x) ≈ c (1 - x)^β` with `0 < c`. The exponent `β` is what quark-counting arguments predict and
what a fit parameterises; it is a property of the function of the momentum fraction at one scale,
not of its moments. This module names it. A function `g` of the momentum fraction has large-`x`
exponent `β`, `PDF.HasLargeXExponent g β`, when `g x / (1 - x)^β` has a positive finite limit as
`x → 1⁻`; equivalently `g` is asymptotically equivalent there, in the sense of Mathlib's
`Asymptotics.IsEquivalent`, to `c (1 - x)^β` for some `c > 0`
(`hasLargeXExponent_iff_exists_isEquivalent`).

The exponent is unique when it exists (`HasLargeXExponent.unique`), so two densities with
different exponents are different functions however many of their moments agree. It is preserved
by positive rescaling and by sums of functions with the same exponent, and the model shape
`x^a (1 - x)^b` of `PDF.modelPdf` has exponent `b` (`hasLargeXExponent_modelPdf`).

## Main definitions

* `PDF.HasLargeXExponent g β`: `g x / (1 - x)^β` tends to a positive limit as `x → 1⁻`.

## Main results

* `PDF.hasLargeXExponent_iff_exists_isEquivalent`: the exponent as an asymptotic equivalence.
* `PDF.HasLargeXExponent.unique`: the large-`x` exponent of a function is unique.
* `PDF.hasLargeXExponent_modelPdf`: the model density `x^a (1 - x)^b` has exponent `b`.

## References

* G. R. Farrar and D. R. Jackson, *Pion and nucleon structure functions near x = 1*,
  Phys. Rev. Lett. 35 (1975) 1416.
-/

public section

noncomputable section

open Filter Topology

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace PDF

/-- A function `g` of the momentum fraction **has large-`x` exponent `β`** when `g x / (1 - x)^β`
tends to a positive finite limit as `x → 1⁻`: near the endpoint, `g` behaves as `c (1 - x)^β`
with `0 < c`. -/
def HasLargeXExponent (g : ℝ → ℝ) (β : ℝ) : Prop :=
  ∃ c, 0 < c ∧ Tendsto (fun x => g x / (1 - x) ^ β) (𝓝[<] 1) (𝓝 c)

variable {g g' : ℝ → ℝ} {β β' : ℝ}

theorem hasLargeXExponent_iff :
    HasLargeXExponent g β ↔ ∃ c, 0 < c ∧ Tendsto (fun x => g x / (1 - x) ^ β) (𝓝[<] 1) (𝓝 c) :=
  Iff.rfl

/-- **The large-`x` exponent as an asymptotic equivalence**: `g` has exponent `β` exactly when it
is asymptotically equivalent, as `x → 1⁻`, to `c (1 - x)^β` for some `c > 0`. -/
theorem hasLargeXExponent_iff_exists_isEquivalent :
    HasLargeXExponent g β ↔
      ∃ c, 0 < c ∧ Asymptotics.IsEquivalent (𝓝[<] 1) g fun x => c * (1 - x) ^ β := by
  refine exists_congr fun c => and_congr_right fun hc => ?_
  have hne : ∀ᶠ x in 𝓝[<] (1 : ℝ), c * (1 - x) ^ β ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero hc.ne' (Real.rpow_pos_of_pos (sub_pos.2 hx) β).ne'
  rw [Asymptotics.isEquivalent_iff_tendsto_one hne]
  constructor
  · intro h
    have h' := h.div_const c
    rw [div_self hc.ne'] at h'
    exact h'.congr fun x => by rw [Pi.div_apply, div_div, mul_comm]
  · intro h
    have h' := h.const_mul c
    rw [mul_one] at h'
    exact h'.congr fun x => by rw [Pi.div_apply, mul_div_assoc', mul_div_mul_left _ _ hc.ne']

/-- **The large-`x` exponent is unique**: a function cannot behave as a positive multiple of two
different powers of `1 - x` at the endpoint. -/
theorem HasLargeXExponent.unique (h : HasLargeXExponent g β) (h' : HasLargeXExponent g β') :
    β = β' := by
  suffices key : ∀ {β β' : ℝ}, HasLargeXExponent g β → HasLargeXExponent g β' → ¬β < β' by
    rcases lt_trichotomy β β' with hlt | heq | hgt
    · exact absurd hlt (key h h')
    · exact heq
    · exact absurd hgt (key h' h)
  rintro β β' ⟨c, hc, hgc⟩ ⟨c', -, hgc'⟩ hlt
  -- `g / (1 - x)^β` is `g / (1 - x)^β'` times `(1 - x)^(β' - β)`, which tends to zero.
  have hd : 0 < β' - β := sub_pos.2 hlt
  have hpow : Tendsto (fun x : ℝ => (1 - x) ^ (β' - β)) (𝓝[<] 1) (𝓝 0) := by
    have hc1 : Continuous fun x : ℝ => (1 - x) ^ (β' - β) :=
      (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hd.le
    have h1 := hc1.tendsto 1
    rw [sub_self, Real.zero_rpow hd.ne'] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have hprod := hgc'.mul hpow
  rw [mul_zero] at hprod
  refine hc.ne' (tendsto_nhds_unique hgc (hprod.congr' ?_))
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : 0 < 1 - x := sub_pos.2 hx
  rw [Real.rpow_sub hx', div_mul_div_comm, mul_comm (g x), mul_div_mul_left _ _
    (Real.rpow_pos_of_pos hx' β').ne']

/-- The large-`x` exponent depends only on the function near the endpoint `x = 1`, below it. -/
theorem HasLargeXExponent.congr (h : HasLargeXExponent g β) (hg : g =ᶠ[𝓝[<] 1] g') :
    HasLargeXExponent g' β := by
  obtain ⟨c, hc, hgc⟩ := h
  exact ⟨c, hc, hgc.congr' (hg.mono fun x hx => by rw [hx])⟩

/-- A positive multiple of a function has the same large-`x` exponent. -/
theorem HasLargeXExponent.const_mul (h : HasLargeXExponent g β) {k : ℝ} (hk : 0 < k) :
    HasLargeXExponent (fun x => k * g x) β := by
  obtain ⟨c, hc, hgc⟩ := h
  exact ⟨k * c, mul_pos hk hc, by simpa only [mul_div_assoc] using hgc.const_mul k⟩

/-- The sum of two functions with the same large-`x` exponent has that exponent. -/
theorem HasLargeXExponent.add (h : HasLargeXExponent g β) (h' : HasLargeXExponent g' β) :
    HasLargeXExponent (fun x => g x + g' x) β := by
  obtain ⟨c, hc, hgc⟩ := h
  obtain ⟨c', hc', hgc'⟩ := h'
  exact ⟨c + c', add_pos hc hc', by simpa only [add_div] using hgc.add hgc'⟩

/-- The power `(1 - x)^β` has large-`x` exponent `β`. -/
theorem hasLargeXExponent_one_sub_rpow (β : ℝ) : HasLargeXExponent (fun x => (1 - x) ^ β) β := by
  refine ⟨1, one_pos, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [div_self (Real.rpow_pos_of_pos (sub_pos.2 hx) β).ne']

/-- **The model density `x^a (1 - x)^b` has large-`x` exponent `b`**, at every parton and every
scale, with limit `1` for the ratio. -/
theorem hasLargeXExponent_modelPdf (Flavor : Type) (a b : ℕ) (i : Flavor) (Q2 : ℝ) :
    HasLargeXExponent (fun x => modelPdf Flavor a b i x Q2) b := by
  refine ⟨1, one_pos, ?_⟩
  have hx : Tendsto (fun x : ℝ => x ^ a) (𝓝[<] 1) (𝓝 1) := by
    simpa only [one_pow] using ((continuous_pow a).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  refine hx.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
  rw [modelPdf_apply, Set.indicator_of_mem (Set.Ioo_subset_Icc_self hx), betaShape,
    Real.rpow_natCast, mul_div_assoc, div_self (pow_ne_zero _ (sub_pos.2 hx.2).ne'), mul_one]

end PDF
end Parton
end Particles
end EpsilonEridani
