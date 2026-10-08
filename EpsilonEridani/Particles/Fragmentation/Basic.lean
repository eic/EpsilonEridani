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
def extendByZero (f : Frag Hadron Flavor) : Frag Hadron Flavor :=
  fun h i z Q2 => (Icc (0 : ℝ) 1).indicator (fun z => f h i z Q2) z

/-- Unfolding lemma for `extendByZero`. -/
lemma extendByZero_apply (f : Frag Hadron Flavor) (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    extendByZero f h i z Q2 = (Icc (0 : ℝ) 1).indicator (fun z => f h i z Q2) z :=
  (rfl)

/-- On the unit interval, `extendByZero f` agrees with `f`. -/
@[simp]
lemma extendByZero_of_mem (f : Frag Hadron Flavor) {z : ℝ} (hz : z ∈ Icc (0 : ℝ) 1)
    (h : Hadron) (i : Flavor) (Q2 : ℝ) : extendByZero f h i z Q2 = f h i z Q2 :=
  indicator_of_mem hz _

/-- Off the unit interval, `extendByZero f` vanishes. -/
@[simp]
lemma extendByZero_of_notMem (f : Frag Hadron Flavor) {z : ℝ} (hz : z ∉ Icc (0 : ℝ) 1)
    (h : Hadron) (i : Flavor) (Q2 : ℝ) : extendByZero f h i z Q2 = 0 :=
  indicator_of_notMem hz _

/-- Extending by zero does not change the `z`-moments, which only see the unit interval. -/
@[simp]
lemma zMoment_extendByZero (f : Frag Hadron Flavor) : zMoment (extendByZero f) = zMoment f := by
  ext n h i Q2
  exact setIntegral_congr_fun measurableSet_Icc fun z hz => by
    rw [extendByZero_of_mem f hz]

/-- Extending by zero does not change integrability on the unit interval. -/
lemma integrableOn_extendByZero_iff (f : Frag Hadron Flavor) (F : ℝ → ℝ → ℝ) (h : Hadron)
    (i : Flavor) (Q2 : ℝ) :
    IntegrableOn (fun z => F z (extendByZero f h i z Q2)) (Icc 0 1) ↔
      IntegrableOn (fun z => F z (f h i z Q2)) (Icc 0 1) :=
  integrableOn_congr_fun (fun z hz => by rw [extendByZero_of_mem f hz]) measurableSet_Icc

/-- The extension by zero of a family that is non-negative on the unit interval satisfies
`Assumptions`. -/
lemma assumptions_extendByZero {f : Frag Hadron Flavor}
    (hf : ∀ h i z Q2, 0 ≤ z → z ≤ 1 → 0 ≤ f h i z Q2) : Assumptions (extendByZero f) where
  support h i z Q2 hz := extendByZero_of_notMem f (by grind) h i Q2
  nonneg h i z Q2 hz₀ hz₁ := by
    rw [extendByZero_of_mem f ⟨hz₀, hz₁⟩]
    exact hf h i z Q2 hz₀ hz₁

end Fragmentation
end Particles
end EpsilonEridani
