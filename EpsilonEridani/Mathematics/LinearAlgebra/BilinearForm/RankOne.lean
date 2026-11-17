/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Rank-one bilinear forms

For a real bilinear form `g` on `V` and vectors `a`, `b`, the rank-one form
`LinearMap.BilinForm.rankOne g a b : (v, w) ↦ g a v * g b w` is the product of the functionals
`g a` and `g b`, built with `LinearMap.smulRight`. It is symmetric when `a = b`
(`LinearMap.BilinForm.rankOne_isSymm`).
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Rank-one bilinear form `(v,w) ↦ g(a,v) g(b,w)` derived from a background bilinear form
`g`, as the Mathlib combinator `LinearMap.smulRight (g a) (g b)`, the map
`v ↦ g a v • g b`. -/
def rankOne (g : BilinForm ℝ V) (a b : V) : BilinForm ℝ V :=
  (g a).smulRight (g b)

@[simp] lemma rankOne_apply (g : BilinForm ℝ V) (a b v w : V) :
    rankOne g a b v w = g a v * g b w := (rfl)

/-- A rank-one form built from a single vector is symmetric. -/
lemma rankOne_isSymm (g : BilinForm ℝ V) (a : V) : (rankOne g a a).IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp [rankOne_apply, mul_comm]

end LinearMap.BilinForm
