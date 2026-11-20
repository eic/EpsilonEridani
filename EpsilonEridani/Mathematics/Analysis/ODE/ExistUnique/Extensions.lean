/-
Copyright (c) 2026 Joseph Tooby-Smith, Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import Mathlib.Analysis.ODE.ExistUnique

/-!
# Uniqueness of ODE solutions for vector fields Lipschitz on balls

Mathlib's `ODE_solution_unique_of_mem_Icc` needs one Lipschitz constant on a set that contains
both solutions. For a vector field that is only Lipschitz on each closed ball, with a constant
depending on the radius (a quadratic vector field, say), a continuous solution on a compact
interval is bounded, so it stays in one such ball. This file records that step:

* `ODE_solution_unique_of_mem_Icc_of_lipschitzOnWith_closedBall`: two solutions on `Ioo a b`,
  continuous on `Icc a b` and agreeing at a point of `Ioo a b`, agree on `Icc a b`, when the
  vector field is Lipschitz on every closed ball centred at the origin.

The lemma is the uniqueness step inlined in the proof of `bkSolution_unique_on_Icc` in
`EpsilonEridani/QFT/Factorization/Evolution/SmallX.lean` (Joseph Tooby-Smith), generalised from the
Balitsky-Kovchegov right-hand side to an arbitrary time-dependent vector field.
-/

@[expose] public section

open Metric Set

namespace EpsilonEridani

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Uniqueness of ODE solutions on a compact interval for a vector field that is Lipschitz on
every closed ball centred at the origin, with a constant that may depend on the radius. No bound
on the solutions is assumed: continuity on the compact interval supplies one. -/
theorem _root_.ODE_solution_unique_of_mem_Icc_of_lipschitzOnWith_closedBall
    {v : ℝ → E → E} {f g : ℝ → E} {a b t₀ : ℝ}
    (hv : ∀ R, 0 ≤ R → ∃ K, ∀ t ∈ Ioo a b, LipschitzOnWith K (v t) (closedBall 0 R))
    (ht : t₀ ∈ Ioo a b)
    (hf : ContinuousOn f (Icc a b)) (hf' : ∀ t ∈ Ioo a b, HasDerivAt f (v t (f t)) t)
    (hg : ContinuousOn g (Icc a b)) (hg' : ∀ t ∈ Ioo a b, HasDerivAt g (v t (g t)) t)
    (heq : f t₀ = g t₀) :
    EqOn f g (Icc a b) := by
  obtain ⟨R₁, hR₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨R₂, hR₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  obtain ⟨K, hK⟩ := hv (max (max R₁ R₂) 0) (le_max_right _ _)
  refine ODE_solution_unique_of_mem_Icc hK ht hf hf' (fun t ht => ?_) hg hg' (fun t ht => ?_) heq
  · exact mem_closedBall_zero_iff.2 ((hR₁ t (Ioo_subset_Icc_self ht)).trans
      ((le_max_left _ _).trans (le_max_left _ _)))
  · exact mem_closedBall_zero_iff.2 ((hR₂ t (Ioo_subset_Icc_self ht)).trans
      ((le_max_right _ _).trans (le_max_left _ _)))

end EpsilonEridani
