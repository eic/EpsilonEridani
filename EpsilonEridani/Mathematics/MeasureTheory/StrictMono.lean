/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable sets of monotone functions

Over a countable index type, the strictly monotone functions into a second-countable
order-closed linear order form a measurable subset of the function space: strict monotonicity
is a countable conjunction of comparisons, each measurable in the product σ-algebra by
`measurableSet_lt`.  The ordered region of `EpsilonEridani.Mathematics.OrderedSimplexIntegral`
is built from this fact.
-/

@[expose] public section

namespace EpsilonEridani

open MeasureTheory

/-- Over a countable index type, the strictly monotone functions into a second-countable
order-closed linear order form a measurable set. -/
@[measurability]
lemma measurableSet_strictMono {ι α : Type*} [Countable ι] [Preorder ι]
    [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] [SecondCountableTopology α]
    [MeasurableSpace α] [OpensMeasurableSpace α] :
    MeasurableSet {p : ι → α | StrictMono p} := by
  simp only [StrictMono, Set.ofPred_forall]
  exact .iInter fun i => .iInter fun j => .iInter fun _ =>
    measurableSet_lt (measurable_pi_apply i) (measurable_pi_apply j)

end EpsilonEridani
