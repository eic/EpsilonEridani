/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Fermions.Dirac.Basic

/-!
# Extensions of the Dirac fermions

The space `Fermion.Dirac` of Dirac spinors is finite-dimensional over `ℂ`, as witnessed by
Physlib's chiral basis `Fermion.Dirac.chiralBasis`, and has dimension four (`finrank_eq_four`).
Exposing this as an instance lets the
`finrank` and `trace` API of Mathlib apply to Dirac spinors and their endomorphisms without
re-deriving it.
-/

public section

namespace Fermion
namespace Dirac

/-- The Dirac spinors form a finite-dimensional complex vector space, with the chiral basis. -/
instance : Module.Finite ℂ Dirac :=
  .of_basis chiralBasis

/-- The Dirac spinors form a four-dimensional complex vector space. -/
@[simp]
theorem finrank_eq_four : Module.finrank ℂ Dirac = 4 := by
  rw [Module.finrank_eq_card_basis chiralBasis, Fintype.card_fin]

end Dirac
end Fermion
