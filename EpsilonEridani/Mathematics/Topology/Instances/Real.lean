/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Continuous real functions killed by multiplication with the identity

A continuous function `f : ℝ → ℝ` with `x * f x = 0` for every `x` vanishes off the origin, and
hence everywhere by continuity, as the complement of the origin is dense
(`dense_compl_singleton`). This is `Continuous.eq_zero_of_id_mul_eq_zero`. It is used to cancel
a factor `x` from identities that hold on the whole line, such as the recurrences of the spherical
Bessel functions (`EpsilonEridani.Mathematics.SpecialFunctions.SphericalBessel.Basic`).
-/

@[expose] public section

/-- A continuous function `f : ℝ → ℝ` with `id * f = 0`, that is `x * f x = 0` for every `x`,
is zero: it vanishes off the origin, and so everywhere by continuity. -/
theorem Continuous.eq_zero_of_id_mul_eq_zero {f : ℝ → ℝ} (hf : Continuous f) (h : id * f = 0) :
    f = 0 :=
  Continuous.ext_on (dense_compl_singleton 0) hf continuous_const fun y hy =>
    (mul_eq_zero.mp (congrFun h y)).resolve_left (Set.mem_compl_singleton_iff.mp hy)
