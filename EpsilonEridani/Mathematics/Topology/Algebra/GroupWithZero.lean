/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Functions killed by multiplication with the identity

In a Hausdorff topological space `R` with a multiplication without zero divisors, in which the
origin is not isolated (`(𝓝[≠] 0).NeBot`), a function `f : R → R` with `x * f x = 0` for every `x`
vanishes off the origin, and hence everywhere as soon as it is continuous at the origin. This is
`ContinuousAt.eq_zero_of_forall_id_mul_eq_zero`. It is used to cancel a factor `x` from
identities that hold on the whole real line, such as the recurrences of the spherical Bessel
functions (`EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`).
-/

@[expose] public section

open Filter Topology

/-- A function `f : R → R` that is continuous at the origin, with `x * f x = 0` for every `x`, is
zero: it vanishes off the origin since `R` has no zero divisors, and so also at the origin by
continuity there, the origin not being isolated. -/
theorem ContinuousAt.eq_zero_of_forall_id_mul_eq_zero {R : Type*} [MulZeroClass R]
    [NoZeroDivisors R] [TopologicalSpace R] [T2Space R] [(𝓝[≠] (0 : R)).NeBot] {f : R → R}
    (hf : ContinuousAt f 0) (h : ∀ x, x * f x = 0) (x : R) : f x = 0 := by
  have hne : ∀ y, y ≠ 0 → f y = 0 := fun y hy => (mul_eq_zero.mp (h y)).resolve_left hy
  rcases eq_or_ne x 0 with rfl | hx
  · exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall (s := {0}ᶜ) fun y hy =>
        (hne y (Set.mem_compl_singleton_iff.mp hy)).symm))
  · exact hne x hx
