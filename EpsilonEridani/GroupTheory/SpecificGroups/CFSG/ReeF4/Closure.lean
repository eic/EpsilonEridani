/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.Closure
public import EpsilonEridani.GroupTheory.SpecificGroups.CFSG.ReeF4.Index

/-!
# The algebraic closure for the Ree family of type `F₄`

This file records that the algebraic closure attached to a validated Ree index of type `F₄` has
characteristic two, and equips it with the resulting structure of an algebra over the field of two
elements. That is the form in which the characteristic reaches a construction on the family's
carrier, whose defining equations live in characteristic two and whose base ring is `ZMod 2`
itself.

## Main results

* `EpsilonEridani.ReeF4LieIndex.charP_closure_two`: the algebraic closure attached to a Ree index of
  type `F₄` has characteristic two.
* `EpsilonEridani.ReeF4LieIndex.algebraZModTwo`: the resulting `ZMod 2`-algebra structure on it.
-/

-- Adapted from `EpsilonEridani.GroupTheory.SpecificGroups.CFSG.ReeG2.Closure`.

public section

namespace EpsilonEridani.ReeF4LieIndex

/-- The algebraic closure attached to a Ree index of type `F₄` has characteristic two. -/
instance charP_closure_two (d : ReeF4LieIndex) : CharP d.1.Closure 2 := by
  rw [← d.characteristic_eq_two]
  infer_instance

/-- The algebraic closure attached to a Ree index of type `F₄` is an algebra over the field of two
elements, this being the base ring over which its carrier is defined. Characteristic two forces
the structure: any two `ZMod 2`-algebra structures on a ring agree. -/
noncomputable instance algebraZModTwo (d : ReeF4LieIndex) : Algebra (ZMod 2) d.1.Closure :=
  ZMod.algebra d.1.Closure 2

end EpsilonEridani.ReeF4LieIndex
