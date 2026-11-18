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
by multiplication by a function with a positive limit at the endpoint
(`HasLargeXExponent.mul_left`), in particular by positive rescaling, and by sums of functions with
the same exponent. A function `h x (1 - x)^β` with `h` tending to a positive limit at the
endpoint has exponent `β` (`hasLargeXExponent_mul_one_sub_rpow`); in particular the model shape
`x^a (1 - x)^b` of `PDF.modelPdf` has exponent `b` (`hasLargeXExponent_modelPdf`).

The moments do not see the exponent. The model `PDF.exponentTwoModelPdf ι` carries on every parton
the shape `(2/3) (1 - x)^2 (1 + 5 x)`, which has the number and momentum moments `1/2` and `1/6`
of `1 - x` (`mellinMoment_exponentTwoModelPdf`), so that rescaled by weights summing to six it
carries the sum-rule bundle (`PDF.sumRuleAssumptionsWeight`) as the rescaled shape `1 - x` does;
but it has exponent two (`hasLargeXExponent_exponentTwoModelPdf`) where `1 - x` has exponent one.

## Main definitions

* `PDF.HasLargeXExponent g β`: `g x / (1 - x)^β` tends to a positive limit as `x → 1⁻`.
* `PDF.exponentTwoModelPdf ι`: the shape `(2/3) (1 - x)^2 (1 + 5 x)` at every parton.

## Main results

* `PDF.hasLargeXExponent_iff_exists_isEquivalent`: the exponent as an asymptotic equivalence.
* `PDF.HasLargeXExponent.unique`: the large-`x` exponent of a function is unique.
* `PDF.HasLargeXExponent.mul_left`: multiplying by a function with a positive limit at the endpoint
  preserves the exponent.
* `PDF.hasLargeXExponent_mul_one_sub_rpow`: a function tending to a positive limit times
  `(1 - x)^β` has exponent `β`.
* `PDF.hasLargeXExponent_modelPdf`: the model density `x^a (1 - x)^b` has exponent `b`.
* `PDF.mellinMoment_exponentTwoModelPdf`, `PDF.hasLargeXExponent_exponentTwoModelPdf`: the model
  of exponent two has the moments `n ≤ 1` of the shape `1 - x`, and exponent two.

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
theorem HasLargeXExponent.congr' (h : HasLargeXExponent g β) (hg : g =ᶠ[𝓝[<] 1] g') :
    HasLargeXExponent g' β := by
  obtain ⟨c, hc, hgc⟩ := h
  exact ⟨c, hc, hgc.congr' (hg.mono fun x hx => by rw [hx])⟩

/-- Pointwise equal functions have the same large-`x` exponent. -/
theorem HasLargeXExponent.congr (h : HasLargeXExponent g β) (hg : ∀ x, g x = g' x) :
    HasLargeXExponent g' β :=
  h.congr' (Eventually.of_forall hg)

/-- **Multiplying by a function with a positive limit at the endpoint preserves the exponent**: if
`k` tends to `c > 0` as `x → 1⁻`, then `k x * g x` has the large-`x` exponent of `g`. -/
theorem HasLargeXExponent.mul_left (h : HasLargeXExponent g β) {k : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hk : Tendsto k (𝓝[<] 1) (𝓝 c)) : HasLargeXExponent (fun x => k x * g x) β := by
  obtain ⟨d, hd, hgd⟩ := h
  exact ⟨c * d, mul_pos hc hd, by simpa only [mul_div_assoc] using hk.mul hgd⟩

/-- A positive multiple of a function has the same large-`x` exponent. -/
theorem HasLargeXExponent.const_mul (h : HasLargeXExponent g β) {k : ℝ} (hk : 0 < k) :
    HasLargeXExponent (fun x => k * g x) β :=
  h.mul_left hk tendsto_const_nhds

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

/-- **A positive limit times a power of `1 - x`**: if `h` tends to `c > 0` as `x → 1⁻`, then
`h x (1 - x)^β` has large-`x` exponent `β`. -/
theorem hasLargeXExponent_mul_one_sub_rpow {h : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hh : Tendsto h (𝓝[<] 1) (𝓝 c)) : HasLargeXExponent (fun x => h x * (1 - x) ^ β) β :=
  (hasLargeXExponent_one_sub_rpow β).mul_left hc hh

/-- **The model density `x^a (1 - x)^b` has large-`x` exponent `b`**, at every parton and every
scale. -/
theorem hasLargeXExponent_modelPdf (Flavor : Type) (a b : ℕ) (i : Flavor) (Q2 : ℝ) :
    HasLargeXExponent (fun x => modelPdf Flavor a b i x Q2) b := by
  have hx : Tendsto (fun x : ℝ => x ^ a) (𝓝[<] 1) (𝓝 1) := by
    simpa only [one_pow] using ((continuous_pow a).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  refine (hasLargeXExponent_mul_one_sub_rpow one_pos hx).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with x hx
  rw [modelPdf_apply, Set.indicator_of_mem (Set.Ioo_subset_Icc_self hx), betaShape,
    Real.rpow_natCast]

/-! ### A shape with the moments `n ≤ 1` of `1 - x` and exponent two -/

section ExponentTwoModel

variable (ι : Type)

/-- **A model density of large-`x` exponent two with the number and momentum moments of `1 - x`**:
every parton carries the shape `(2/3) (1 - x)^2 + (10/3) x (1 - x)^2 = (2/3) (1 - x)^2 (1 + 5 x)`
on the unit interval. Its moments `n = 0` and `n = 1` are the moments `1/2` and `1/6` of the
shape `1 - x` of `modelPdf ι 0 1` (`mellinMoment_exponentTwoModelPdf`), but it vanishes
quadratically at `x = 1` (`hasLargeXExponent_exponentTwoModelPdf`). -/
def exponentTwoModelPdf : Pdf ι :=
  weight (fun _ => 2 / 3) (modelPdf ι 0 2) + weight (fun _ => 10 / 3) (modelPdf ι 1 2)

@[simp]
lemma exponentTwoModelPdf_apply (i : ι) (x Q2 : ℝ) :
    exponentTwoModelPdf ι i x Q2 = 2 / 3 * modelPdf ι 0 2 i x Q2 + 10 / 3 * modelPdf ι 1 2 i x Q2 :=
  (rfl)

/-- The model of exponent two satisfies the density assumptions: it is a sum of positive multiples
of model densities. -/
lemma assumptions_exponentTwoModelPdf : Assumptions (exponentTwoModelPdf ι) :=
  ((assumptions_modelPdf _ 0 2).weight fun _ => by norm_num).add
    ((assumptions_modelPdf _ 1 2).weight fun _ => by norm_num)

/-- **The Mellin moments of the model of exponent two**: `4 (2 n + 3) / ((n + 1) (n + 2) (n + 3)
(n + 4))`, in particular `1/2` at `n = 0` and `1/6` at `n = 1`, the moments of `1 - x`. -/
@[simp]
lemma mellinMoment_exponentTwoModelPdf (n : ℕ) (i : ι) (Q2 : ℝ) :
    mellinMoment (exponentTwoModelPdf ι) n i Q2 = 4 * (2 * (n : ℝ) + 3) /
      (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3) * ((n : ℝ) + 4)) := by
  rw [exponentTwoModelPdf, mellinMoment_add
    (((regularity_modelPdf _ 0 2).weight _).momentIntegrable n i Q2).integrableOn
    (((regularity_modelPdf _ 1 2).weight _).momentIntegrable n i Q2).integrableOn,
    mellinMoment_weight, mellinMoment_weight, mellinMoment_modelPdf_succ_left,
    mellinMoment_modelPdf_zero_two, mellinMoment_modelPdf_zero_two]
  push_cast
  field_simp
  ring

/-- **The model of exponent two has large-`x` exponent two**, at every parton and every scale. -/
theorem hasLargeXExponent_exponentTwoModelPdf (i : ι) (Q2 : ℝ) :
    HasLargeXExponent (fun x => exponentTwoModelPdf ι i x Q2) 2 := by
  have h := ((hasLargeXExponent_modelPdf ι 0 2 i Q2).const_mul (k := 2 / 3) (by norm_num)).add
    ((hasLargeXExponent_modelPdf ι 1 2 i Q2).const_mul (k := 10 / 3) (by norm_num))
  rw [Nat.cast_ofNat] at h
  exact h.congr fun x => (exponentTwoModelPdf_apply ι i x Q2).symm

end ExponentTwoModel

end PDF
end Parton
end Particles
end EpsilonEridani
