/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.Algebra.AlgebraicGroup.DiagonalizableGroup.Semisimple

/-!
# Points of the multiplicative group are semisimple

Transporting semisimplicity of points of the diagonalizable group `D(ℤ)` across the standard
bialgebra isomorphism proves that every point of the multiplicative group `𝔾ₘ` is semisimple.

## Main declarations

* `EpsilonEridani.MultiplicativeGroup.isSemisimplePoint`: every point of `𝔾ₘ` is semisimple.

This is the `𝔾ₘ = D(ℤ)` example from Layer 4 of the ReductiveGroups roadmap.
-/

public section

open CategoryTheory WithConv

namespace EpsilonEridani

universe u x

namespace MultiplicativeGroup

variable {R : Type u} {K : Type x} [CommSemiring R] [Field K] [Algebra R K]

/-- **Every point of the multiplicative group `𝔾ₘ` is a semisimple point.** -/
theorem isSemisimplePoint
    (g : WithConv (LaurentPolynomial R →ₐ[R] K)) :
    HopfAlgebra.IsSemisimplePoint g := by
  let e := AddMonoidAlgebra.toMultiplicativeBialgEquiv R R ℤ
  have h := DiagonalizableGroup.isSemisimplePoint
    (AlgHom.mapDomain (e.symm : MonoidAlgebra R (Multiplicative ℤ) →ₐc[R] LaurentPolynomial R) g)
  exact (HopfAlgebra.isSemisimplePoint_mapDomain_iff e.symm g).mp h

end MultiplicativeGroup

end EpsilonEridani
