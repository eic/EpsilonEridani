/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Algebra.Star.Module
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Dimensions of the self-adjoint and skew-adjoint parts of a star module

Every element of a star module over a ring with trivial star in which `2` is invertible is uniquely
the sum of a self-adjoint and a skew-adjoint element (`StarModule.decomposeProdAdjoint`), so over
such a field the two parts have complementary dimensions. The trivial star on the scalars is what
makes the two parts submodules; a complex star module is therefore treated over `ℝ`.

## Main results

* `finrank_selfAdjoint_add_finrank_skewAdjoint`: over any field with trivial star in which `2` is
  invertible, the `R`-dimensions of the self-adjoint and skew-adjoint parts add up to that of the
  space.
-/

public section

open Module

variable (R : Type*) {A : Type*} [Field R] [StarMul R] [TrivialStar R]
  [AddCommGroup A] [Module R A] [StarAddMonoid A] [StarModule R A] [FiniteDimensional R A]

/-- The self-adjoint part of a finite-dimensional star module is finite-dimensional. -/
instance : FiniteDimensional R (selfAdjoint A) :=
  .of_injective (selfAdjoint.submodule R A).subtype Subtype.val_injective

/-- The skew-adjoint part of a finite-dimensional star module is finite-dimensional. -/
instance : FiniteDimensional R (skewAdjoint A) :=
  .of_injective (skewAdjoint.submodule R A).subtype Subtype.val_injective

variable [Invertible (2 : R)]

/-- The dimensions of the self-adjoint and skew-adjoint parts of a finite-dimensional star module
add up to the dimension of the module. -/
theorem finrank_selfAdjoint_add_finrank_skewAdjoint :
    finrank R (selfAdjoint A) + finrank R (skewAdjoint A) = finrank R A := by
  rw [← Module.finrank_prod, (StarModule.decomposeProdAdjoint R A).finrank_eq]
