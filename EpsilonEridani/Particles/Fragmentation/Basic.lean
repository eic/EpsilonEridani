/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Fragmentation Function Interfaces (Stage 13)

This module introduces minimal fragmentation-function interfaces for
semi-inclusive DIS extensions.

It also provides basic lemmas about the `z`-moments `zMoment` (as interval integrals,
non-negativity, and the moments of monomials `c zᵐ`), and the construction
`indicatorUnitInterval`, which cuts a family off outside the unit interval and is used to build
explicit fragmentation families satisfying `Assumptions`.

Finally it provides the pullback `comap τ σ D` of a family along a map `τ` of the observed
hadrons and a map `σ` of the parton flavours, which is how charge conjugation and the flavour
symmetries of a hadron multiplet act on fragmentation families. The pullback preserves
`Assumptions` and carries every `z`-moment to a `z`-moment.

-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani
namespace Particles
namespace Fragmentation

variable {Hadron Flavor : Type}

/-- Fragmentation-function family `D_h^i(z,Q2)`. -/
abbrev Frag (Hadron Flavor : Type) : Type := Hadron → Flavor → ℝ → ℝ → ℝ

/-- Structural assumptions for fragmentation functions. -/
structure Assumptions (D : Frag Hadron Flavor) : Prop where
  support : ∀ h i z Q2, z < 0 ∨ 1 < z → D h i z Q2 = 0
  nonneg : ∀ h i z Q2, 0 ≤ z → z ≤ 1 → 0 ≤ D h i z Q2

/-- Mellin-like z-moment for fragmentation functions. -/
def zMoment
    (D : Frag Hadron Flavor)
    (n : ℕ)
    (h : Hadron)
    (i : Flavor)
    (Q2 : ℝ) : ℝ :=
  ∫ z in Set.Icc (0 : ℝ) 1, z ^ n * D h i z Q2

/-- A `z`-moment as an interval integral over `0..1`. -/
lemma zMoment_eq_intervalIntegral (D : Frag Hadron Flavor) (n : ℕ) (h : Hadron) (i : Flavor)
    (Q2 : ℝ) : zMoment D n h i Q2 = ∫ z in (0 : ℝ)..1, z ^ n * D h i z Q2 := by
  rw [zMoment, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

/-- A `z`-moment of a family that is non-negative on the unit interval is non-negative. -/
lemma zMoment_nonneg {D : Frag Hadron Flavor} {h : Hadron} {i : Flavor} {Q2 : ℝ}
    (hD : ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ D h i z Q2) (n : ℕ) : 0 ≤ zMoment D n h i Q2 :=
  setIntegral_nonneg measurableSet_Icc fun z hz => mul_nonneg (pow_nonneg hz.1 n) (hD z hz)

/-- The `k`-th moment over the unit interval of the monomial `c zᵐ` is `c / (k + m + 1)`. -/
lemma integral_pow_mul_const_mul_pow (c : ℝ) (k m : ℕ) :
    ∫ z in (0 : ℝ)..1, z ^ k * (c * z ^ m) = c / (k + m + 1) := by
  have : ∀ z : ℝ, z ^ k * (c * z ^ m) = c * z ^ (k + m) := fun z => by ring
  simp only [this, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-- The `k`-th moment of the monomial family `c zᵐ` is `c / (k + m + 1)`. -/
lemma zMoment_const_mul_pow (c : ℝ) (m k : ℕ) (h : Hadron) (i : Flavor) (Q2 : ℝ) :
    zMoment (fun _ _ z _ => c * z ^ m : Frag Hadron Flavor) k h i Q2 = c / (k + m + 1) := by
  rw [zMoment_eq_intervalIntegral, integral_pow_mul_const_mul_pow]

/-- Support consequence outside the physical z-interval. -/
lemma eq_zero_of_not_mem_unitInterval
    (D : Frag Hadron Flavor)
    (hD : Assumptions D)
    (h : Hadron)
    (i : Flavor)
    (z Q2 : ℝ)
    (hz : z < 0 ∨ 1 < z) :
    D h i z Q2 = 0 :=
  hD.support h i z Q2 hz

/-- The family that agrees with `f` for `z ∈ [0, 1]` and vanishes outside. -/
def indicatorUnitInterval (f : Frag Hadron Flavor) : Frag Hadron Flavor :=
  fun h i z Q2 => (Icc (0 : ℝ) 1).indicator (fun z => f h i z Q2) z

/-- On the unit interval, `indicatorUnitInterval f` agrees with `f`. -/
@[simp]
lemma indicatorUnitInterval_of_mem (f : Frag Hadron Flavor) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1)
    (h : Hadron) (i : Flavor) (Q2 : ℝ) : indicatorUnitInterval f h i z Q2 = f h i z Q2 :=
  indicator_of_mem hz _

/-- Off the unit interval, `indicatorUnitInterval f` vanishes. -/
@[simp]
lemma indicatorUnitInterval_of_notMem (f : Frag Hadron Flavor) {z : ℝ} (hz : z ∉ Icc (0 : ℝ) 1)
    (h : Hadron) (i : Flavor) (Q2 : ℝ) : indicatorUnitInterval f h i z Q2 = 0 :=
  indicator_of_notMem hz _

/-- Cutting off outside the unit interval does not change the `z`-moments, which only see the unit
interval. -/
@[simp]
lemma zMoment_indicatorUnitInterval (f : Frag Hadron Flavor) :
    zMoment (indicatorUnitInterval f) = zMoment f := by
  ext n h i Q2
  exact setIntegral_congr_fun measurableSet_Icc fun z hz => by
    rw [indicatorUnitInterval_of_mem f hz]

/-- Cutting off outside the unit interval does not change integrability on the unit interval: for
any `F : ℝ → ℝ → ℝ`, the integrand `fun z => F z (D h i z Q2)` is integrable on `[0, 1]` for
`D = indicatorUnitInterval f` exactly when it is for `D = f`. With `F := fun z y => z ^ n * y` this
covers the `z`-moment integrands, and with `F := fun _ y => y` the family itself. -/
lemma integrableOn_indicatorUnitInterval_iff (f : Frag Hadron Flavor) (F : ℝ → ℝ → ℝ)
    (h : Hadron) (i : Flavor) (Q2 : ℝ) :
    IntegrableOn (fun z => F z (indicatorUnitInterval f h i z Q2)) (Icc 0 1) ↔
      IntegrableOn (fun z => F z (f h i z Q2)) (Icc 0 1) :=
  integrableOn_congr_fun (fun z hz => by rw [indicatorUnitInterval_of_mem f hz]) measurableSet_Icc

/-- The first-moment integrand of the cut-off of a family that is continuous in `z` on the unit
interval is integrable there. -/
lemma integrableOn_mul_indicatorUnitInterval {f : Frag Hadron Flavor} {h : Hadron} {i : Flavor}
    {Q2 : ℝ} (hf : ContinuousOn (fun z => f h i z Q2) (Icc 0 1)) :
    IntegrableOn (fun z => z * indicatorUnitInterval f h i z Q2) (Icc 0 1) :=
  (integrableOn_indicatorUnitInterval_iff f (fun z y => z * y) h i Q2).2
    (continuousOn_id.mul hf).integrableOn_Icc

/-- The cut-off of a family that is non-negative on the unit interval satisfies `Assumptions`. -/
lemma assumptions_indicatorUnitInterval {f : Frag Hadron Flavor}
    (hf : ∀ h i z Q2, 0 ≤ z → z ≤ 1 → 0 ≤ f h i z Q2) : Assumptions (indicatorUnitInterval f) where
  support h i z Q2 hz := indicatorUnitInterval_of_notMem f (by grind) h i Q2
  nonneg h i z Q2 hz₀ hz₁ := by
    rw [indicatorUnitInterval_of_mem f ⟨hz₀, hz₁⟩]
    exact hf h i z Q2 hz₀ hz₁

section Comap

variable {Hadron' Flavor' Hadron'' Flavor'' : Type}

/-- The family over `Hadron'` and `Flavor'` whose fragmentation of parton `i` into hadron `h` is
the fragmentation of `σ i` into `τ h` in `D`. Charge conjugation and the flavour symmetries of a
hadron multiplet act on fragmentation families this way. -/
def comap (τ : Hadron' → Hadron) (σ : Flavor' → Flavor) (D : Frag Hadron Flavor) :
    Frag Hadron' Flavor' :=
  fun h i => D (τ h) (σ i)

@[simp]
lemma comap_apply (τ : Hadron' → Hadron) (σ : Flavor' → Flavor) (D : Frag Hadron Flavor)
    (h : Hadron') (i : Flavor') (z Q2 : ℝ) : comap τ σ D h i z Q2 = D (τ h) (σ i) z Q2 :=
  (rfl)

@[simp]
lemma comap_id (D : Frag Hadron Flavor) : comap id id D = D :=
  (rfl)

@[simp]
lemma comap_comap (τ : Hadron' → Hadron) (σ : Flavor' → Flavor) (τ' : Hadron'' → Hadron')
    (σ' : Flavor'' → Flavor') (D : Frag Hadron Flavor) :
    comap τ' σ' (comap τ σ D) = comap (τ ∘ τ') (σ ∘ σ') D :=
  (rfl)

/-- Cutting off outside the unit interval commutes with a pullback: both act on the value of the
family and neither touches the momentum fraction. -/
@[simp]
lemma comap_indicatorUnitInterval (τ : Hadron' → Hadron) (σ : Flavor' → Flavor)
    (f : Frag Hadron Flavor) :
    comap τ σ (indicatorUnitInterval f) = indicatorUnitInterval (comap τ σ f) :=
  (rfl)

@[simp]
lemma zMoment_comap (τ : Hadron' → Hadron) (σ : Flavor' → Flavor) (D : Frag Hadron Flavor)
    (n : ℕ) (h : Hadron') (i : Flavor') (Q2 : ℝ) :
    zMoment (comap τ σ D) n h i Q2 = zMoment D n (τ h) (σ i) Q2 :=
  (rfl)

/-- A pullback preserves the structural assumptions. -/
lemma Assumptions.comap {D : Frag Hadron Flavor} (hD : Assumptions D) (τ : Hadron' → Hadron)
    (σ : Flavor' → Flavor) : Assumptions (Fragmentation.comap τ σ D) where
  support h i z Q2 hz := hD.support (τ h) (σ i) z Q2 hz
  nonneg h i z Q2 hz₀ hz₁ := hD.nonneg (τ h) (σ i) z Q2 hz₀ hz₁

end Comap

end Fragmentation
end Particles
end EpsilonEridani
