/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.Algebra.Homology.AInfinity.Algebra
public import EpsilonEridani.LinearAlgebra.TensorCoalgebra.Coaugmented.Extension

/-!
# The bar coderivation of the coaugmented tensor coalgebra

`EpsilonEridani.AInfinityAlgebra.barDifferential` is the square-zero coderivation of the *reduced* tensor
coalgebra, and the Stasheff identities are read off from it.  The module and bimodule theories
need one step more: a right module is a coderivation over `b` on the cofree right bar comodule, and
a bimodule a bicomodule coderivation, so in both cases `b` has to be available as a coderivation
of the *coaugmented* tensor coalgebra, which also carries the empty word.

This file supplies that extension, for the bar differential of an `A∞` algebra.  The empty word is
annihilated, and on the coaugmented tensor coalgebra the extension is a
`EpsilonEridani.TensorWords.IsGradedCoderivation` of twist parameter one whose square is zero and which
raises the total letter degree by one.

The extension itself is not specific to bar constructions: an endomorphism of the reduced words is
extended to all tensor words by
`EpsilonEridani.TensorWords.extendReduced`, and the module
`EpsilonEridani.LinearAlgebra.TensorCoalgebra.Coaugmented.Extension` proves there that the extension
preserves the square-zero law, the homogeneity in the total letter degree, and the `q`-twisted
co-Leibniz identity.  The results of this file are the applications of those three lemmas to
`EpsilonEridani.AInfinityAlgebra.barDifferential`, together with the empty-word case; the coaugmented
co-Leibniz identity itself, the letterwise maps, and the total-letter-degree pieces are in
`EpsilonEridani.LinearAlgebra.TensorCoalgebra.Coaugmented.GradedCoderivation` and
`EpsilonEridani.LinearAlgebra.TensorCoalgebra.Coaugmented.Basic`.

## Main definitions

* `EpsilonEridani.AInfinityAlgebra.coaugmentedBarDifferential`: the bar coderivation extended to all
  tensor words by zero on the empty word.

## Main results

* `EpsilonEridani.AInfinityAlgebra.coaugmentedBarDifferential_one`: the extension annihilates the empty
  word.
* `EpsilonEridani.AInfinityAlgebra.coaugmentedBarDifferential_comp_reducedInclusion`: the extension
  restricts to the bar differential on the words of positive length.
* `EpsilonEridani.AInfinityAlgebra.coaugmentedBarDifferential_sq`: its square is zero.
* `EpsilonEridani.AInfinityAlgebra.isHomogeneous_coaugmentedBarDifferential`: it raises the total letter
  degree by one.
* `EpsilonEridani.AInfinityAlgebra.isGradedCoderivation_coaugmentedBarDifferential`: it is a
  twist-parameter-one graded coderivation of the coaugmented tensor coalgebra.

## References

* E. Getzler and J. D. S. Jones, *A-infinity algebras and the cyclic bar complex*, Sections 1--2.
* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.1 and 3.6.
-/

public section

open scoped BigOperators DirectSum TensorProduct

universe uR uA

namespace EpsilonEridani

open TensorWords

namespace AInfinityAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [AddCommGroup A] [Module R A]

/-- The bar differential extended to the coaugmented tensor words: the square-zero coderivation
`EpsilonEridani.AInfinityAlgebra.barDifferential` of the reduced tensor coalgebra, sent along
`EpsilonEridani.TensorWords.extendReduced`, so that the empty word is annihilated. -/
noncomputable def coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    TensorWords R A →ₗ[R] TensorWords R A :=
  extendReduced 𝒜.barDifferential

/-- The bar coderivation of the coaugmented words is the extension of the bar differential of the
reduced words by zero on the empty word. -/
theorem coaugmentedBarDifferential_def (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential = extendReduced 𝒜.barDifferential := by
  rw [coaugmentedBarDifferential]

/-- The extension annihilates the empty word. -/
@[simp]
theorem coaugmentedBarDifferential_one (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential (1 : TensorWords R A) = 0 := by
  rw [coaugmentedBarDifferential_def, extendReduced_one]

/-- The extension agrees with the bar differential on the words of positive length. -/
theorem coaugmentedBarDifferential_comp_reducedInclusion (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential ∘ₗ reducedInclusion R A
      = reducedInclusion R A ∘ₗ 𝒜.barDifferential :=
  extendReduced_comp_reducedInclusion 𝒜.barDifferential

/-- The extension squares to zero. -/
@[simp]
theorem coaugmentedBarDifferential_sq (𝒜 : AInfinityAlgebra R A) :
    𝒜.coaugmentedBarDifferential ∘ₗ 𝒜.coaugmentedBarDifferential = 0 :=
  extendReduced_sq 𝒜.barDifferential (barDifferential_sq 𝒜)

/-- The extension raises the total letter degree by one. -/
theorem isHomogeneous_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    LinearMap.IsHomogeneous 𝒜.coaugmentedBarDifferential
      (gradedPiece (𝒜.grading.shift 1)) (gradedPiece (𝒜.grading.shift 1)) 1 :=
  isHomogeneous_extendReduced 𝒜.isHomogeneous_barDifferential

/-- The extension satisfies the graded co-Leibniz identity of the coaugmented tensor coalgebra. -/
theorem isGradedCoderivation_coaugmentedBarDifferential (𝒜 : AInfinityAlgebra R A) :
    TensorWords.IsGradedCoderivation (𝒜.grading.shift 1) 1 𝒜.coaugmentedBarDifferential :=
  isGradedCoderivation_extendReduced 𝒜.isGradedCoderivation_barDifferential

end AInfinityAlgebra

end EpsilonEridani
