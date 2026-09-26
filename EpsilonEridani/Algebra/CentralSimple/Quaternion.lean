/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `EpsilonEridani.Algebra.CentralSimple.Opposite` is imported publicly: it supplies
-- `EpsilonEridani.Algebra.tensorOpAlgEquivMatrix`, of which everything below is an instance, and it
-- re-exports `EpsilonEridani.Algebra.CentralSimple.Degree` (hence `EpsilonEridani.Algebra.deg`) together with
-- the `⊗[ℝ]` notation and the matrix algebras, which is why none of those is imported again here.
public import EpsilonEridani.Algebra.CentralSimple.Opposite
-- `EpsilonEridani.Algebra.Central.Quaternion` is imported publicly for two reasons: `ℍ[ℝ]` occurs in every
-- statement below, and it is the instance `EpsilonEridani.Quaternion.instIsCentral` proved there that puts
-- `ℍ[ℝ]` in the scope of the opposite isomorphism at all. It re-exports
-- `Mathlib.Algebra.Quaternion`, hence the `ℍ[·]` notation, quaternion conjugation
-- `Quaternion.starAe`, and `Quaternion.finrank_eq_four`.
public import EpsilonEridani.Algebra.Central.Quaternion
-- `Mathlib.Data.Real.Basic` is imported publicly because the field structure on `ℝ` is what makes
-- the statements below typecheck: the public imports above reach `Mathlib.Algebra.Quaternion`,
-- which supplies `ℍ[·]` over an arbitrary base but not `ℝ` itself, so without this import `ℝ` is
-- not even in scope as a name.
public import Mathlib.Basic.Real.Basic

/-!
# The tensor square of the real quaternions is `M₄(ℝ)`

The real quaternions `ℍ[ℝ]` are a central division algebra of dimension `4` over `ℝ`, hence a
central simple `ℝ`-algebra of degree `2`. This file runs the opposite isomorphism of
`EpsilonEridani/Algebra/CentralSimple/Opposite.lean` on them, in the two forms

`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`  and
`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`.

The second follows from the first because quaternion conjugation is an `ℝ`-algebra isomorphism
`ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]ᵐᵒᵖ` (Mathlib's `Quaternion.starAe`): the quaternions are their own opposite.

Nothing below is a statement about `BrauerGroup ℝ`: the two main results are isomorphisms of
`ℝ`-algebras, and the two examples closing the file are a degree computation and a nonexistence
statement. Informally, the isomorphisms exhibit the Brauer class of `ℍ[ℝ]` as **self-inverse**; that
the class is moreover not the identity, so that its order is exactly `2`, is
`EpsilonEridani.Quaternion.orderOf_mk_eq_two` in `EpsilonEridani/Algebra/BrauerGroup/Quaternion.lean`. Saying that
`BrauerGroup ℝ ≃ ℤ/2` is a further and independent matter, needing the classification of real
division algebras to know the class generates; that is
`EpsilonEridani.Quaternion.brauerGroupMulEquiv` in `EpsilonEridani/Algebra/BrauerGroup/Real.lean`.

The matrix size is `4` and not `2`: it is the **dimension** `Module.finrank ℝ ℍ[ℝ] = 4` of the
algebra, not its degree `EpsilonEridani.Algebra.deg ℝ ℍ[ℝ] = 2`. Squaring the degree is exactly what taking
the tensor product with the opposite algebra does, and the degree example at the end of the file
checks it.

## Main results

* `EpsilonEridani.Quaternion.tensorOpAlgEquivMatrix`:
  `ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`.
* `EpsilonEridani.Quaternion.tensorSelfAlgEquivMatrix`: `ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`,
  the roadmap's worked example.

## References

This is the `ℍ[ℝ] ⊗_ℝ ℍ[ℝ] ≃ M₄(ℝ)` half of the Hamilton-quaternion worked example of the
[semisimple algebras roadmap](https://github.com/EpsilonEridaniProject/EpsilonEridaniRoadmap/blob/main/EpsilonEridaniRoadmap/RepresentationTheory/SemisimpleAlgebras/README.md),
pinned there as `quaternion_tensor_self`; the centrality half is
`EpsilonEridani/Algebra/Central/Quaternion.lean`. See P. Gille, T. Szamuely, *Central Simple Algebras and
Galois Cohomology*, CUP (2006), §1.1 and §2.1.
-/

public section

open scoped Quaternion TensorProduct

namespace EpsilonEridani

namespace Quaternion

/-- **`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`**: the opposite isomorphism at the real
quaternions. `EpsilonEridani.Algebra.tensorOpAlgEquivMatrix` asks for `IsAzumaya ℝ ℍ[ℝ]`, which
`EpsilonEridani.IsSimpleRing.isAzumaya` supplies and which is not an instance, so it is installed by hand;
its own three hypotheses are found by instance search -- `Algebra.IsCentral ℝ ℍ[ℝ]` from
`EpsilonEridani.Quaternion.instIsCentral`, `IsSimpleRing ℍ[ℝ]` because a division ring is simple, and
`FiniteDimensional ℝ ℍ[ℝ]` -- so beyond it only the dimension `Quaternion.finrank_eq_four` has to be
supplied. -/
noncomputable def tensorOpAlgEquivMatrix :
    ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]ᵐᵒᵖ ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  haveI := IsSimpleRing.isAzumaya ℝ ℍ[ℝ]
  Algebra.tensorOpAlgEquivMatrix ℝ ℍ[ℝ] _root_.Quaternion.finrank_eq_four

/-- **`ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ`.** Quaternion conjugation is an `ℝ`-algebra
isomorphism `ℍ[ℝ] ≃ₐ[ℝ] ℍ[ℝ]ᵐᵒᵖ` (`Quaternion.starAe`), so the tensor square of `ℍ[ℝ]` is its tensor
product with its own opposite, which `EpsilonEridani.Quaternion.tensorOpAlgEquivMatrix` splits.

In Brauer-group language this exhibits the class of `ℍ[ℝ]` as its own inverse. Whether that class is
the identity is a separate question, not settled by this isomorphism; see the module docstring. -/
noncomputable def tensorSelfAlgEquivMatrix :
    ℍ[ℝ] ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 4) (Fin 4) ℝ :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl (A₁ := ℍ[ℝ])) _root_.Quaternion.starAe).trans
    tensorOpAlgEquivMatrix

/-- The tensor square of the real quaternions has degree `4`, by the multiplicativity of the degree
and `EpsilonEridani.Algebra.deg ℝ ℍ[ℝ] = 2`. This is an independent check on the matrix size in
`EpsilonEridani.Quaternion.tensorSelfAlgEquivMatrix`: `4` really is `2 · 2`, and not the degree `2` of
either factor. A caller wanting the numeral gets it the same way, from
`EpsilonEridani.Algebra.deg_tensorProduct`, so this is an example rather than a lemma. -/
example : Algebra.deg ℝ (ℍ[ℝ] ⊗[ℝ] ℍ[ℝ]) = 4 := by
  have h : Algebra.deg ℝ ℍ[ℝ] = 2 :=
    Algebra.deg_eq_of_finrank_eq_sq (by rw [_root_.Quaternion.finrank_eq_four]; norm_num)
  rw [Algebra.deg_tensorProduct, h]

/-- The tensor square is split, but `ℍ[ℝ]` itself is not: the only matrix algebra over `ℝ` of
dimension `4` is `Matrix (Fin 2) (Fin 2) ℝ`, and `ℍ[ℝ]` is a division algebra, so no isomorphism
exists. It is this nonsplitting that makes the self-inverse class of `ℍ[ℝ]` different from the
identity, and so of order exactly `2` (`EpsilonEridani.Quaternion.orderOf_mk_eq_two`). -/
example : IsEmpty (ℍ[ℝ] ≃ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ) :=
  isEmpty_algEquiv_matrix ℝ (Fin 2)

end Quaternion

end EpsilonEridani
