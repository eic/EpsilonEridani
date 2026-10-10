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

The derivative of an even function is odd (`Function.Even.deriv`). In particular it
vanishes at the origin, by Mathlib's `Function.Odd.map_zero`. This is used in the construction of
the spherical Bessel functions
(`EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`): the iterates of
`f ↦ -dslope (deriv f) 0` applied to `Real.sinc` are even, so their derivatives vanish at the
origin, which is what identifies that operator with the Rayleigh operator `-(1 / x) d/dx` away from
the origin.
-/

public section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of an even function is odd. -/
theorem Function.Even.deriv {f : 𝕜 → F} (hf : Function.Even f) : Function.Odd (deriv f) := by
  intro x
  have h : (fun y => f (-y)) = f := funext hf
  rw [← h, deriv_comp_neg, neg_neg, h]
