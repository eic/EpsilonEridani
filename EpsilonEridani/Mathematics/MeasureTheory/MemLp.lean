/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Function.L2Space

/-!
# `MemLp` functions: vanishing square integral and support in a set

Two facts about `MemLp` functions used for wave functions on a half-line.

* `integral_sq_eq_zero_iff`: a square-integrable real function has `∫ f ^ 2 = 0` exactly when
  it vanishes almost everywhere, so a probability `∫ u ^ 2` is zero only for a null amplitude.
* `memLp_of_support_subset_of_restrict`: a function supported in a set `s` that is in `Lᵖ` for
  the measure restricted to `s` is in `Lᵖ` for the whole measure.
-/

@[expose] public section

namespace EpsilonEridani

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A square-integrable real function has vanishing integral of its square exactly when it
vanishes almost everywhere. -/
theorem integral_sq_eq_zero_iff {f : α → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ = 0 ↔ f =ᵐ[μ] 0 := by
  rw [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hf.integrable_sq]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with x hx <;> simpa using hx

/-- A function supported in `s` that is in `Lᵖ` for `μ` restricted to `s` is in `Lᵖ` for `μ`. -/
theorem memLp_of_support_subset_of_restrict {E : Type*} [NormedAddCommGroup E]
    {p : ENNReal} {s : Set α} {f : α → E} (hs : NullMeasurableSet s μ)
    (hsupp : Function.support f ⊆ s) (hf : MemLp f p (μ.restrict s)) : MemLp f p μ := by
  rw [← indicator_eq_self.2 hsupp]
  exact (memLp_indicator_iff_restrict hs).2 hf

end EpsilonEridani
