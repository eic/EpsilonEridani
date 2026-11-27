/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Real.Basic

/-!
# The light quark flavours

The three light quark flavours — up, down and strange — as the type `LightFlavor`, together with
the electric charge of each in units of the positron charge, `LightFlavor.charge`: `2/3` for the
up quark and `-1/3` for the down and strange quarks. Flavour sums over the light quarks, such as
the charge-weighted sum of parton densities in the leading-order structure function
`F₂ = x ∑_f e_f² (f + fbar)`, run over this type and are evaluated one flavour at a time by
`LightFlavor.sum_univ`.

## Main definitions

* `LightFlavor`: the up, down and strange quark flavours.
* `LightFlavor.charge`: the electric charge of the quark of each light flavour, in units of the
  positron charge.

## Main results

* `LightFlavor.sum_univ`: a sum over the light flavours is the sum of its values on `u`, `d`
  and `s`.
* `LightFlavor.charge_u`, `LightFlavor.charge_d`, `LightFlavor.charge_s`: the light-quark
  charges as rewrite rules.

## References

* S. Navas et al. (Particle Data Group), *Review of Particle Physics*, Phys. Rev. D 110 (2024)
  030001: the electric charges of the quarks, in units of the positron charge.
-/

public section

namespace EpsilonEridani
namespace Particles
namespace Parton

/-- The three light quark flavours: up, down and strange. -/
inductive LightFlavor where
  /-- The up quark. -/
  | u
  /-- The down quark. -/
  | d
  /-- The strange quark. -/
  | s
  deriving DecidableEq, Repr

namespace LightFlavor

instance : Fintype LightFlavor where
  elems := {u, d, s}
  complete x := by cases x <;> simp

/-- The sum of a function over the light flavours is the sum of its values on `u`, `d` and `s`,
so that sums over `LightFlavor` can be evaluated flavour by flavour. -/
@[simp]
theorem sum_univ {M : Type*} [AddCommMonoid M] (f : LightFlavor → M) :
    ∑ a, f a = f u + f d + f s := by
  rw [← Finset.eq_univ_of_forall (s := {u, d, s}) fun a => by cases a <;> simp]
  simp [Finset.sum_insert, add_assoc]

/-- The electric charge of the quark of each light flavour, in units of the positron charge. -/
noncomputable def charge : LightFlavor → ℝ
  | u => 2 / 3
  | d => -1 / 3
  | s => -1 / 3

@[simp] theorem charge_u : charge u = 2 / 3 := (rfl)

@[simp] theorem charge_d : charge d = -1 / 3 := (rfl)

@[simp] theorem charge_s : charge s = -1 / 3 := (rfl)

end LightFlavor

end Parton
end Particles
end EpsilonEridani
