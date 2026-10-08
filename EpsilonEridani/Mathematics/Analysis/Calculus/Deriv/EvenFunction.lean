/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Derivatives of even functions

The derivative of an even function is odd (`EpsilonEridani.odd_deriv_of_even`). In particular it
vanishes at the origin, by Mathlib's `Function.Odd.map_zero`. This is used in the spherical
Bessel construction: each iterate `G l` of `f ↦ -dslope (deriv f) 0` applied to `sinc` is even
(`reduced_neg`), hence `deriv (G l) 0 = 0`, which makes the iterated operator analytic across the
origin.
-/

public section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

namespace EpsilonEridani

/-- The derivative of an even function is odd. -/
theorem odd_deriv_of_even {f : 𝕜 → F} (hf : Function.Even f) : Function.Odd (deriv f) := by
  intro x
  have h : (fun y => f (-y)) = f := funext hf
  rw [← h, deriv_comp_neg, neg_neg, h]

end EpsilonEridani
