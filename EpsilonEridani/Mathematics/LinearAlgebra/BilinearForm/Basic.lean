/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# The square of a sum under a symmetric bilinear form

For a symmetric bilinear form `B`, the value on the diagonal at a sum expands as
`B (x + y) (x + y) = B x x + 2 B x y + B y y`. This is the form in which Minkowski invariants
such as `(p + q)²` are expanded into scalar products; it complements Mathlib's
`LinearMap.BilinForm.IsSymm.polarization`, which solves the same identity for `B x y` over a
field of characteristic not two.

## Main results

* `LinearMap.BilinForm.IsSymm.apply_add_self`: the expansion
  `B (x + y) (x + y) = B x x + 2 * B x y + B y y`.
-/

public section

namespace LinearMap.BilinForm

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {B : LinearMap.BilinForm R M}

/-- The square of a sum under a symmetric bilinear form,
`B (x + y) (x + y) = B x x + 2 * B x y + B y y`. -/
theorem IsSymm.apply_add_self (hB : B.IsSymm) (x y : M) :
    B (x + y) (x + y) = B x x + 2 * B x y + B y y := by
  simp only [map_add, LinearMap.add_apply, hB.eq y x]
  ring

end LinearMap.BilinForm
