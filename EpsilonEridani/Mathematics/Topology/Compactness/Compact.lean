/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Topology.Compactness.Compact

/-!
# Points are eventually avoided along `cocompact`

In any topological space a singleton is compact (`isCompact_singleton`), so its complement belongs
to the filter `cocompact X`: every given point is eventually avoided "at infinity". This is
`Filter.eventually_ne_cocompact`, the `cocompact` counterpart of `Filter.eventually_ne_atTop`. It
is used, for example, to divide by the argument in large-argument asymptotics on `ℝ`.
-/

public section

open Filter

namespace Filter

/-- Along `cocompact X`, a given point `a` is eventually avoided. -/
theorem eventually_ne_cocompact {X : Type*} [TopologicalSpace X] (a : X) :
    ∀ᶠ x in cocompact X, x ≠ a := by
  filter_upwards [isCompact_singleton.compl_mem_cocompact] with x hx
  exact Set.mem_compl_singleton_iff.mp hx

end Filter
