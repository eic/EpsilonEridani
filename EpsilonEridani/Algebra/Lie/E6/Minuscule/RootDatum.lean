/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.Algebra.Lie.E6.Minuscule.GroupScheme
public import EpsilonEridani.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.Assembly

/-!
# Torus characters of the type E6 minuscule carrier in its named root datum

`EpsilonEridani.E6Minuscule.groupScheme` is the full-weight Chevalley carrier obtained from the
twenty-seven-dimensional minuscule representation of the type-`E₆` Serre presentation. Its
numbered raising and lowering subgroups and its rank-six split weight torus are explicit, and
their conjugation equation is stated in terms of the corresponding row of `CartanMatrix.E 6`.

This file identifies that table with the uniform simply connected root datum used by downstream
consumers.
For a validity proof `ht : EpsilonEridani.DynkinType.E6.Valid`, the root character of the `i`-th raising
subgroup is

```text
(E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i),
```

and the character of the matching lowering subgroup is its negative. Rewriting the carrier's
conjugation equation by these identifications gives the two torus conjugation equations against
the named positive and negative simple roots.

The distinction from the equations already in `GroupScheme.lean` is the dispatcher in the target:
`DynkinType.simplyConnectedRootDatum` is the root datum reached from a validated Lie-type index,
whereas the carrier was constructed directly from the concrete tables
`EpsilonEridani.DynkinType.e6Root` and `EpsilonEridani.DynkinType.e6SimpleIndex`. These results certify that the
two routes use the same Bourbaki numbering and the same character lattice.

This file does not assert reductivity, maximality of the weight torus, existence of all root
subgroups, or an identification of the carrier with an independently defined algebraic group.
It packages only the torus-character compatibility that the explicit construction already proves.

## Main results

* `EpsilonEridani.E6Minuscule.rootGeneratorWeight_inl_eq_root_simpleIndex`: the raising-subgroup
  character is the corresponding simple root of the uniform simply connected datum.
* `EpsilonEridani.E6Minuscule.rootGeneratorWeight_inr_eq_neg_root_simpleIndex`: the lowering-subgroup
  character is the negative of that simple root.
* `EpsilonEridani.E6Minuscule.weightTorus_conj_rootSubgroup_root_simpleIndex` and
  `EpsilonEridani.E6Minuscule.weightTorus_conj_rootSubgroup_neg_root_simpleIndex`: the positive and
  negative simple-root torus conjugation equations.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Sections 4.4 and 7.1.
* J. E. Humphreys, *Linear Algebraic Groups*, Sections 26--27.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate V.

The root-identification proofs and torus-conjugation wrapper patterns are adapted from
`EpsilonEridani/Algebra/Lie/SpecialLinear/StandardCarrier/RootDatum.lean`, added in
[EpsilonEridaniProject/EpsilonEridani#5198](https://github.com/EpsilonEridaniProject/EpsilonEridani/pull/5198), and
`EpsilonEridani/Algebra/Lie/Symplectic/StandardCarrier/RootDatum.lean`, developed in
[EpsilonEridaniProject/EpsilonEridani#5203](https://github.com/EpsilonEridaniProject/EpsilonEridani/pull/5203).

This advances the "Pinnings" and "Root subgroup maps" targets of Layer 9 of
`EpsilonEridaniRoadmap/ReductiveGroups/README.md`. Its consumer is milestone L0 of
`EpsilonEridaniRoadmap/CFSGStatement/README.md`: `ValidLieTypeIndex.AmbientGroup` must be traceable through
`ValidLieTypeIndex.dynkinType` to `DynkinType.simplyConnectedRootDatum`, with its root subgroups
identified by characters of that same datum.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

namespace EpsilonEridani.E6Minuscule

open EpsilonEridani.E6

open DynkinType

/-! ## The numbered subgroups sit at the named simple roots -/

/-- **The `i`-th raising subgroup sits at the `i`-th simple root of the uniform type-`E₆`
datum.** Its character for the action of the carrier's split weight torus is the root selected by
the uniform Bourbaki simple-root index. -/
theorem rootGeneratorWeight_inl_eq_root_simpleIndex (ht : E6.Valid) (i : Fin 6) :
    rootGeneratorWeight (.inl i) =
      (E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i) := by
  -- The dependent root index blocks rewriting the dispatcher equation directly, so both sides
  -- are identified with the Cartan-matrix row through the carrier's concrete-table lemma.
  refine Eq.trans ?_ (root_simpleIndex E6 ht i).symm
  rw [cartanMatrix_E6, rootGeneratorWeight_inl_eq_e6Root_e6SimpleIndex, root_e6SimpleIndex]

/-- **The `i`-th lowering subgroup sits at the negative of the `i`-th simple root of the uniform
type-`E₆` datum.** -/
theorem rootGeneratorWeight_inr_eq_neg_root_simpleIndex (ht : E6.Valid) (i : Fin 6) :
    rootGeneratorWeight (.inr i) =
      -(E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i) :=
  (rootGeneratorWeight_inr_eq_neg_e6Root_e6SimpleIndex i).trans
    (congrArg Neg.neg ((rootGeneratorWeight_inl_eq_e6Root_e6SimpleIndex i).symm.trans
      (rootGeneratorWeight_inl_eq_root_simpleIndex ht i)))

/-! ## Torus conjugation equations against the named simple roots -/

/-- **The torus conjugation equation at a named positive simple root.** A point of
the split weight torus conjugates the raising-subgroup element of parameter `u` at node `i` to the
same subgroup with parameter `α_i(s)u`, where `α_i` is the corresponding root of the uniform
simply connected type-`E₆` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (ht : E6.Valid) (i : Fin 6)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 6)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inl i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((EpsilonEridani.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                ((E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inl i)).hom.hom := by
  rw [← rootGeneratorWeight_inl_eq_root_simpleIndex]
  exact weightTorus_conj_rootSubgroup (.inl i) A s u

/-- **The torus conjugation equation at a named negative simple root.** A point of
the split weight torus conjugates the lowering-subgroup element of parameter `u` at node `i` to
the same subgroup with parameter `(-α_i)(s)u`. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (ht : E6.Valid) (i : Fin 6)
    (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin 6)).X)
    (u : A) :
    (s ≫ weightTorus.hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup (.inr i)).hom.hom) *
        (s ≫ weightTorus.hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((EpsilonEridani.torusCharacter
                (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
                (-(E6.simplyConnectedRootDatum ht).root (E6.simpleIndex ht i)) : A) * u)) ≫
        (rootSubgroup (.inr i)).hom.hom := by
  rw [← rootGeneratorWeight_inr_eq_neg_root_simpleIndex]
  exact weightTorus_conj_rootSubgroup (.inr i) A s u

end EpsilonEridani.E6Minuscule
