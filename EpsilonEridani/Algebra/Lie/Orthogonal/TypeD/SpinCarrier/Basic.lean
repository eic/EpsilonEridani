/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Sl2
public import EpsilonEridani.Algebra.Lie.Orthogonal.TypeD.Serre.RootGenerator
public import EpsilonEridani.RepresentationTheory.Spin.Polarization.Split.Even
public import EpsilonEridani.RepresentationTheory.Spin.Polarization.TypeD.KostantLattice
public import
  EpsilonEridani.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Points
import EpsilonEridani.Algebra.Lie.Sl2.Basic
import EpsilonEridani.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Relations
import EpsilonEridani.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Rigidity
import EpsilonEridani.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.Torus

/-!
# The full-weight type-D spin carrier

For `4 ≤ n`, this file specializes the type-`Dₙ` spin representation to the canonical split
quadratic space `M* × M`, where `M = Fin n → ℚ`. Its exterior coordinate lattice has basis
indexed by the sign sets `Finset (Fin n)` and is stable under the type-`D` Serre Kostant form.
The corresponding spin weights span the full simply connected character lattice.

These data are fed into the Kostant toral-closure construction. The result is an explicit affine
group scheme over `ℤ`, cut out inside `GL_(2^n)` by the largest Hopf ideal killed by the numbered
simple-root subgroups and the represented rank-`n` split torus. In particular, the construction
uses the full spin module rather than one half-spin summand, so its weights see both spinor cosets
of the type-`D` root lattice.

Those data are then carried onto matrix-valued points: the numbered root subgroups and the weight
torus become homomorphisms into `EpsilonEridani.TypeDSpinCarrier.points`, and conjugating one by the
other rescales its parameter through a character. That character is named: it is the positive or
negative `i`-th simple root of `EpsilonEridani.DynkinType.simplyConnectedRootDatum` at
`EpsilonEridani.DynkinType.D n`, the uniform pinned datum a consumer reaches holding only a Dynkin type.
That naming is what makes the carrier's pinning conventions statable without reference to its
`2 ^ n`-dimensional spin realization.

No smoothness, reductivity, maximality of the torus, or identification of the carrier's whole root
datum is asserted here: the equations below concern the simple root characters alone, and exhibit
neither a Borel subgroup nor a root subgroup for a non-simple root. Those are subsequent steps in
the pinned Chevalley--Demazure construction.

## Main declarations

* `EpsilonEridani.TypeDSpinCarrier.groupScheme`: the full-weight spin carrier over `ℤ`.
* `EpsilonEridani.TypeDSpinCarrier.rootSubgroup`: its numbered simple-root subgroup morphisms.
* `EpsilonEridani.TypeDSpinCarrier.weightTorus`: its closed rank-`n` split torus.
* `EpsilonEridani.TypeDSpinCarrier.points`: its matrix-valued points over a commutative ring.
* `EpsilonEridani.TypeDSpinCarrier.rootSubgroupPoints` and
  `EpsilonEridani.TypeDSpinCarrier.weightTorusPoints`: the numbered root subgroups and the weight torus
  on those matrix-valued points.

## Main results

* `EpsilonEridani.TypeDSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints` and
  `EpsilonEridani.TypeDSpinCarrier.weightTorus_conj_rootSubgroup`: conjugation by the weight torus
  rescales the parameter of each numbered root subgroup through that character, on matrix-valued
  points and on scheme points respectively.
* `EpsilonEridani.TypeDSpinCarrier.weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex`,
  `EpsilonEridani.TypeDSpinCarrier.weightTorus_conj_rootSubgroup_root_simpleIndex`, and their
  negative-root counterparts: the same equations with the named simple root of
  `EpsilonEridani.DynkinType.simplyConnectedRootDatum` as their exponent.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1--2.

The carrier API follows the formal template of
`EpsilonEridani.Algebra.Lie.E6.Minuscule.GroupScheme` and
`EpsilonEridani.Algebra.Lie.Symplectic.StandardCarrier.Scheme`, and the pinning equations below follow
that of `EpsilonEridani.Algebra.Lie.Symplectic.StandardCarrier.RootDatum`; the split spin representation,
exterior lattice, and type-`D` weights are specific to this construction. This advances Layer 9,
"The Chevalley--Demazure construction", of the ReductiveGroups roadmap and supplies the type-`D`
carrier required by milestone L0 of the CFSGStatement roadmap.
-/

public section

open scoped Matrix

universe v

namespace EpsilonEridani.TypeDSpinCarrier

open AlgebraicGeometry CategoryTheory
open EpsilonEridani.UniversalEnvelopingAlgebra
open scoped CategoryTheory.MonObj TensorProduct

attribute [local instance] EpsilonEridani.moduleNNRat
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance high] Algebra.toModule

variable (n : ℕ) (hn : 4 ≤ n)

/-! ## The split spin representation and its lattice -/

/-- The canonical split polarization used by the type-`Dₙ` spin carrier. -/
noncomputable abbrev polarization := EpsilonEridani.splitEvenPolarization ℚ n

/-- The coordinate basis of the first isotropic summand in the split polarization. -/
noncomputable abbrev polarizationBasis := EpsilonEridani.splitEvenBasis ℚ n

/-- The rational spin representation of the type-`Dₙ` Serre presentation, extended to its
universal enveloping algebra. -/
noncomputable abbrev rep :=
  (polarization n).typeDSpinRep (polarizationBasis n) hn

/-- The integral exterior coordinate lattice in the split spin module. -/
noncomputable abbrev lattice :=
  EpsilonEridani.ExteriorAlgebra.integralLattice (polarizationBasis n)

/-- The dimension of the full spin module, expressed as the cardinality of its exterior basis. -/
abbrev dimension := Fintype.card (Finset (Fin n))

/-- The exterior coordinate basis, reindexed by a finite ordinal for the general-linear carrier. -/
noncomputable def latticeBasis :
    Module.Basis (Fin (dimension n)) ℤ (lattice n).toAddSubgroup :=
  (EpsilonEridani.ExteriorAlgebra.integralLatticeBasis (polarizationBasis n)).reindex
    (Fintype.equivFin (Finset (Fin n)))

/-- The sign set represented by a finite-ordinal spin-basis index. -/
noncomputable abbrev signSet (i : Fin (dimension n)) : Finset (Fin n) :=
  (Fintype.equivFin (Finset (Fin n))).symm i

/-- The simply connected type-`Dₙ` weight of a finite-ordinal spin-basis vector. -/
noncomputable abbrev basisWeight (i : Fin (dimension n)) : Fin n → ℤ :=
  EpsilonEridani.DynkinType.typeDSpinWeight (signSet n i)

/-- A reindexed lattice-basis vector is the exterior basis vector of its sign set. -/
@[simp]
theorem coe_latticeBasis (i : Fin (dimension n)) :
    ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) =
      (polarizationBasis n).ExteriorAlgebra (signSet n i) := by
  rw [latticeBasis, Module.Basis.reindex_apply, signSet]
  exact EpsilonEridani.ExteriorAlgebra.coe_integralLatticeBasis _ _

/-- Every represented numbered root generator is nilpotent. -/
theorem isNilpotent_rep_rootGenerator (k : Fin n ⊕ Fin n) :
    IsNilpotent (rep n hn
      (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (EpsilonEridani.serreRootGenerator (CartanMatrix.D n) k))) :=
  (polarization n).isNilpotent_typeDSpinRep_rootGenerator (polarizationBasis n) hn k

private theorem rep_serreH_ne_zero (i : Fin n) :
    rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n) i)) ≠ 0 := by
  intro hzero
  by_cases hnext : (i : ℕ) + 1 < n
  · have hweight :=
      (isCartanWeightVector_iff
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn)).1
        ((polarization n).isCartanWeightVector_typeDSpinRep_exteriorBasis
          (polarizationBasis n) hn {i}) i
    rw [hzero, LinearMap.zero_apply] at hweight
    simp only [EpsilonEridani.DynkinType.typeDSpinWeight_apply, dite_eq_left hnext,
      Finset.mem_singleton, ↓reduceIte] at hweight
    have hne : (⟨(i : ℕ) + 1, hnext⟩ : Fin n) ≠ i := by
      intro h
      have hval : (i : ℕ) + 1 = i := congrArg Fin.val h
      omega
    rw [ite_eq_right hne] at hweight
    simp only [sub_zero, Int.cast_one, one_smul] at hweight
    exact (polarizationBasis n).ExteriorAlgebra.ne_zero {i} hweight.symm
  · have hweight :=
      (isCartanWeightVector_iff
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn)).1
        ((polarization n).isCartanWeightVector_typeDSpinRep_exteriorBasis
          (polarizationBasis n) hn ∅) i
    rw [hzero, LinearMap.zero_apply] at hweight
    simp only [EpsilonEridani.DynkinType.typeDSpinWeight_apply, dite_eq_right hnext,
      Finset.notMem_empty, ↓reduceIte, zero_add, zero_sub, Int.cast_neg, Int.cast_one,
      neg_smul, one_smul] at hweight
    exact (polarizationBasis n).ExteriorAlgebra.ne_zero ∅ (neg_eq_zero.mp hweight.symm)

/-- The represented positive and negative simple generators at a common type-`D` node, together
with the represented Cartan generator, form an `sl_2` triple. -/
theorem isSl2Triple_rep_rootGenerator (i : Fin n) :
    _root_.IsSl2Triple
      (rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n) i)))
      (rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (EpsilonEridani.serreRootGenerator (CartanMatrix.D n) (.inl i))))
      (rep n hn (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (EpsilonEridani.serreRootGenerator (CartanMatrix.D n) (.inr i)))) := by
  let φ := (polarization n).typeDSpinSerreRepresentation (polarizationBasis n) hn
  have hh : φ (EpsilonEridani.serreH ℚ (CartanMatrix.D n) i) ≠ 0 := by
    simpa only [φ, rep,
      (polarization n).typeDSpinRep_ι (polarizationBasis n) hn] using
      rep_serreH_ne_zero n hn i
  have hsource :
      _root_.IsSl2Triple
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n) i)
        (EpsilonEridani.serreE ℚ (CartanMatrix.D n) i)
        (EpsilonEridani.serreF ℚ (CartanMatrix.D n) i) := {
    h_ne_zero := fun hzero ↦ hh (by simp [hzero])
    lie_e_f := EpsilonEridani.lie_serreE_serreF_self ℚ (CartanMatrix.D n) i
    lie_h_e_nsmul := by
      rw [EpsilonEridani.lie_serreH_serreE, CartanMatrix.D_diag]
      rfl
    lie_h_f_nsmul := by
      rw [EpsilonEridani.lie_serreH_serreF, CartanMatrix.D_diag]
      rfl
  }
  have htriple := hsource.map φ hh
  simpa only [φ, rep, EpsilonEridani.serreRootGenerator_inl,
    EpsilonEridani.serreRootGenerator_inr,
    (polarization n).typeDSpinRep_ι (polarizationBasis n) hn] using htriple

/-- The type-`D` Serre Kostant form preserves the split exterior coordinate lattice. -/
theorem rep_serreKostantForm_mem_lattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n))}
    (hu : u ∈ EpsilonEridani.serreKostantForm (CartanMatrix.D n))
    {v : ExteriorAlgebra ℚ (polarization n).W} (hv : v ∈ lattice n) :
    rep n hn u v ∈ lattice n :=
  (polarization n).typeDSpinRep_serreKostantForm_apply_mem_integralLattice
    (polarizationBasis n) hn hu hv

/-- The generic Kostant form for the numbered type-`D` generators preserves the split exterior
coordinate lattice. -/
theorem rep_kostantForm_mem_lattice
    (u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n)))
    (hu : u ∈ kostantForm (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)))
    (v : ExteriorAlgebra ℚ (polarization n).W) (hv : v ∈ lattice n) :
    rep n hn u v ∈ lattice n :=
  rep_serreKostantForm_mem_lattice n hn (by
    rw [EpsilonEridani.serreKostantForm_def]
    exact hu) hv

/-- Every finite-ordinal exterior basis vector has its named integral type-`D` spin weight. -/
theorem isCartanWeightVector_latticeBasis (i : Fin (dimension n)) :
    IsCartanWeightVector (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn)
      (basisWeight n i)
      ((latticeBasis n i : (lattice n).toAddSubgroup) :
        ExteriorAlgebra ℚ (polarization n).W) := by
  rw [coe_latticeBasis]
  exact (polarization n).isCartanWeightVector_typeDSpinRep_exteriorBasis
    (polarizationBasis n) hn (signSet n i)

/-- The weights of the full spin basis span the simply connected type-`D` character lattice. -/
theorem span_range_basisWeight_eq_top :
    Submodule.span ℤ (Set.range (basisWeight n)) = ⊤ := by
  have hrange :
      Set.range (fun i : Fin (dimension n) ↦
        EpsilonEridani.DynkinType.typeDSpinWeight (signSet n i)) =
        Set.range (EpsilonEridani.DynkinType.typeDSpinWeight (n := n)) := by
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨signSet n i, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨Fintype.equivFin (Finset (Fin n)) s, by simp [signSet]⟩
  rw [hrange, EpsilonEridani.DynkinType.span_range_typeDSpinWeight_eq_top]

/-! ## The closed carrier and its pinned generators -/

/-- The Hopf ideal cutting out the full-weight type-`Dₙ` spin carrier inside `GL_(2^n)`. -/
noncomputable def definingIdeal (hn : 4 ≤ n) :
    HopfIdeal ℤ (EpsilonEridani.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) :=
  kostantToralDefiningIdeal
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)

/-- The defining ideal is the one supplied by the generic Kostant toral-closure construction. -/
theorem definingIdeal_def :
    definingIdeal n hn =
      kostantToralDefiningIdeal
        (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn)
        (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) := by
  rw [definingIdeal]

/-- The full-weight type-`Dₙ` spin carrier over `ℤ`, obtained as the smallest closed subgroup
scheme containing the represented numbered root subgroups and weight torus. -/
noncomputable def groupScheme (hn : 4 ≤ n) : Grp (Over (Spec (CommRingCat.of ℤ))) :=
  kostantToralGroupScheme
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)

/-- The quotient-spectrum presentation of the type-`Dₙ` spin carrier. -/
theorem groupScheme_def :
    groupScheme n hn = CommHopfAlgCat.quotientSpec
      (EpsilonEridani.GeneralLinear.coordinateHopfAlgebra ℤ (dimension n)) (definingIdeal n hn) := by
  rw [groupScheme, definingIdeal]

/-- The type-`Dₙ` carrier is the generic Kostant toral closure for its spin representation. -/
theorem groupScheme_eq_kostantToralGroupScheme :
    groupScheme n hn = kostantToralGroupScheme
      (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) := by
  rw [groupScheme]

/-- The canonical inclusion of the type-`Dₙ` spin carrier into `GL_(2^n)`. -/
noncomputable def carrierι (hn : 4 ≤ n) :
    groupScheme n hn ⟶ EpsilonEridani.GeneralLinear.groupScheme ℤ (dimension n) :=
  eqToHom (by rfl : groupScheme n hn = kostantToralGroupScheme
      (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)) ≫
    kostantToralGroupSchemeι
      (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n)

/-- The canonical inclusion is the generic Kostant toral-closure inclusion, read across the
carrier's presentation as that closure. -/
theorem carrierι_def :
    carrierι n hn =
      eqToHom (groupScheme_eq_kostantToralGroupScheme n hn) ≫
        kostantToralGroupSchemeι
          (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
          (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
          (rep_kostantForm_mem_lattice n hn)
          (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) := by
  rw [carrierι]

/-- The type-`Dₙ` spin carrier is a closed subgroup scheme of its ambient general linear group. -/
instance isClosedImmersion_carrierι : IsClosedImmersion (carrierι n hn).hom.hom.left := by
  rw [carrierι]
  exact isClosedImmersion_kostantToralGroupSchemeι _ _ _ _ _ _ _ _

/-- A positive or negative numbered simple-root subgroup of the type-`Dₙ` spin carrier. -/
noncomputable def rootSubgroup (hn : 4 ≤ n) (k : Fin n ⊕ Fin n) :
    AdditiveGroup.groupScheme ℤ ⟶ groupScheme n hn :=
  kostantRootSubgroupToToral
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) k ≫
  eqToHom (by rfl : kostantToralGroupScheme
      (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) =
        groupScheme n hn)

/-- The root subgroup is the generic Kostant root subgroup, transported across the carrier's
quotient-spectrum presentation. -/
theorem rootSubgroup_def (k : Fin n ⊕ Fin n) :
    rootSubgroup n hn k =
      kostantRootSubgroupToToral
          (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
          (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
          (rep_kostantForm_mem_lattice n hn)
          (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) k ≫
        eqToHom (groupScheme_eq_kostantToralGroupScheme n hn).symm := by
  rw [rootSubgroup]

/-- Including a numbered root subgroup into the ambient general linear group recovers its
represented Kostant root subgroup. -/
@[simp]
theorem rootSubgroup_comp_carrierι (k : Fin n ⊕ Fin n) :
    rootSubgroup n hn k ≫ carrierι n hn =
      kostantRootSubgroup
        (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) k
        (isNilpotent_rep_rootGenerator n hn k) (latticeBasis n) := by
  rw [rootSubgroup, carrierι]
  exact kostantRootSubgroupToToral_comp_ι _ _ _ _ _ _ _ _ k

/-- The represented rank-`n` split weight torus in the type-`Dₙ` spin carrier. -/
noncomputable def weightTorus (hn : 4 ≤ n) :
    SplitTorus.groupScheme ℤ (Fin n) ⟶ groupScheme n hn :=
  kostantWeightTorusToToral
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) ≫
  eqToHom (by rfl : kostantToralGroupScheme
      (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
      (rep_kostantForm_mem_lattice n hn)
      (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) =
        groupScheme n hn)

/-- The represented weight torus is the generic factored Kostant torus at the type-`Dₙ` spin
data. -/
theorem weightTorus_def :
    weightTorus n hn =
      kostantWeightTorusToToral
          (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
          (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
          (rep_kostantForm_mem_lattice n hn)
          (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) ≫
        eqToHom (by rfl : kostantToralGroupScheme
          (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
          (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
          (rep_kostantForm_mem_lattice n hn)
          (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) =
            groupScheme n hn) := by
  rw [weightTorus]

/-- Including the weight torus into the ambient general linear group recovers the diagonal torus
of the spin weights. -/
@[simp]
theorem weightTorus_comp_carrierι :
    weightTorus n hn ≫ carrierι n hn =
      EpsilonEridani.GeneralLinear.weightTorus (R := ℤ) (basisWeight n) := by
  rw [weightTorus, carrierι]
  exact kostantWeightTorusToToral_comp_ι _ _ _ _ _ _ _ _

/-- The full spin weights make the represented split torus a closed subgroup scheme of the
carrier. -/
instance isClosedImmersion_weightTorus :
    IsClosedImmersion (weightTorus n hn).hom.hom.left :=
  isClosedImmersion_kostantWeightTorusToToral _ _ _ _ _ _ _ _
    (span_range_basisWeight_eq_top n)

/-- Two morphisms out of the type-`Dₙ` spin carrier agree when they agree on its numbered root
subgroups and represented split torus. -/
@[ext]
theorem groupScheme_hom_ext {Y : _root_.CommHopfAlgCat.{0} ℤ}
    (f g : groupScheme n hn ⟶
      (AlgebraicGeometry.hopfSpec (CommRingCat.of ℤ)).obj (Opposite.op Y))
    (hroot : ∀ k, rootSubgroup n hn k ≫ f = rootSubgroup n hn k ≫ g)
    (htorus : weightTorus n hn ≫ f = weightTorus n hn ≫ g) : f = g := by
  exact kostantToralGroupScheme_hom_ext _ _ _ _ _ _ _ _ f g hroot htorus

/-! ## Matrix-valued points -/

/-- The matrix-valued points of the type-`Dₙ` spin carrier. -/
noncomputable def points (hn : 4 ≤ n) (A : Type v) [CommRing A] :
    Subgroup (_root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :=
  kostantToralPointsSubgroup
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn)
    (isNilpotent_rep_rootGenerator n hn) (latticeBasis n) (basisWeight n) A

/-- The carrier points are exactly the invertible matrices cut out by the defining Hopf ideal. -/
theorem points_def (A : Type v) [CommRing A] :
    points n hn A =
      EpsilonEridani.GeneralLinear.hopfIdealPointsSubgroup (dimension n) (definingIdeal n hn) A := by
  rw [points, definingIdeal]
  exact kostantToralPointsSubgroup_def _ _ _ _ _ _ _ _ A

/-- A matrix is a carrier point exactly when its associated convolution point kills the
defining Hopf ideal. -/
@[simp]
theorem mem_points_iff (A : Type v) [CommRing A]
    (g : _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
    g ∈ points n hn A ↔
      ∀ x ∈ definingIdeal n hn,
        ((EpsilonEridani.GeneralLinear.pointsMulEquiv (R := ℤ) (dimension n)).symm g).ofConv x = 0 := by
  rw [points, definingIdeal]
  exact mem_kostantToralPointsSubgroup_iff _ _ _ _ _ _ _ _ A g

/-- **The parametrized numbered root subgroup inside the type-`Dₙ` spin carrier points.** The
parameter is read through the canonical multiplicative copy of the additive group of `A`. -/
noncomputable def rootSubgroupPoints (hn : 4 ≤ n) (k : Fin n ⊕ Fin n) (A : Type v) [CommRing A] :
    Multiplicative A →* points n hn A :=
  kostantToralRootSubgroupPoints
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) k A

/-- A numbered root-subgroup point is its represented divided-power exponential matrix. -/
@[simp]
theorem coe_rootSubgroupPoints (k : Fin n ⊕ Fin n) (A : Type v) [CommRing A]
    (u : Multiplicative A) :
    (rootSubgroupPoints n hn k A u :
        _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      kostantRootSubgroupMatrix
        (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
        (rep_kostantForm_mem_lattice n hn) k (isNilpotent_rep_rootGenerator n hn k)
        (latticeBasis n)
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
  exact coe_kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _ k A u

/-- **The split spin weight torus inside the type-`Dₙ` spin carrier points.** -/
noncomputable def weightTorusPoints (hn : 4 ≤ n) (A : Type v) [CommRing A] :
    (Fin n → Aˣ) →* points n hn A :=
  kostantToralWeightTorusPoints
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) A

/-- A weight-torus point is the diagonal matrix obtained by evaluating each spin weight. -/
@[simp]
theorem coe_weightTorusPoints (A : Type v) [CommRing A] (s : Fin n → Aˣ) :
    (weightTorusPoints n hn A s :
        _root_.Matrix.GeneralLinearGroup (Fin (dimension n)) A) =
      kostantTorusMatrix (lattice n).toAddSubgroup (latticeBasis n) (basisWeight n) s := by
  exact coe_kostantToralWeightTorusPoints _ _ _ _ _ _ _ _ A s

/-! ## The pinning equation -/

/-- **Conjugation by the spin weight torus acts on each numbered root subgroup through its
positive or negative simple-root character, on matrix-valued points.** A torus point `s` carries
the root-subgroup point of parameter `u` to the one of parameter `α_k(s) u`. -/
@[simp]
theorem weightTorusPoints_conj_rootSubgroupPoints (k : Fin n ⊕ Fin n) (A : Type v) [CommRing A]
    (s : Fin n → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n hn A s * rootSubgroupPoints n hn k A u *
        (weightTorusPoints n hn A s)⁻¹ =
      rootSubgroupPoints n hn k A
        (Multiplicative.ofAdd
          ((EpsilonEridani.torusCharacter s (TypeDStd.rootGeneratorWeight n k) : A) *
            Multiplicative.toAdd u)) := by
  exact kostantToralWeightTorusPoints_conj_rootSubgroupPoints
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (rep n hn) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n hn) (isNilpotent_rep_rootGenerator n hn)
    (latticeBasis n) (basisWeight n) (isCartanWeightVector_latticeBasis n hn)
    (TypeDStd.lie_serreH_serreRootGenerator n k) A s u

/-- **Conjugation by the spin weight torus acts on each numbered root subgroup through its
positive or negative simple-root character.** -/
@[simp]
theorem weightTorus_conj_rootSubgroup (k : Fin n ⊕ Fin n) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin n)).X)
    (u : A) :
    (s ≫ (weightTorus n hn).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n hn k).hom.hom) *
        (s ≫ (weightTorus n hn).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((EpsilonEridani.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (TypeDStd.rootGeneratorWeight n k) : A) * u)) ≫
        (rootSubgroup n hn k).hom.hom := by
  rw [weightTorus, rootSubgroup]
  exact kostantWeightTorusToToral_conj_kostantRootSubgroupToToralParam
    _ _ _ _ _ _ _ (isCartanWeightVector_latticeBasis n hn)
    (isNilpotent_rep_rootGenerator n hn) A (TypeDStd.lie_serreH_serreRootGenerator n k) s u

/-! ## The numbered root subgroups sit at the named simple roots

The two identifications the equations below rewrite with,
`EpsilonEridani.TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex` and its lowering counterpart, are
proved beside the weight they name, in
`EpsilonEridani/Algebra/Lie/Orthogonal/TypeD/Root/Generators.lean`.

None of the equations below is a `simp` lemma. Their right-hand sides name the character through
`EpsilonEridani.DynkinType.simplyConnectedRootDatum`, which `simp` unfolds at the `D n` branch, so they
are not `simp`-normal; the numbered equations above are, and these are explicit rewrite lemmas for
a consumer holding a Dynkin type, as in
`EpsilonEridani.SpStd.weightTorus_conj_rootSubgroup_root_simpleIndex`. -/

/-- On matrix-valued points, conjugation by the spin weight torus rescales the `i`-th raising root
subgroup through the `i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_root_simpleIndex (i : Fin n) (A : Type v)
    [CommRing A] (s : Fin n → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n hn A s * rootSubgroupPoints n hn (.inl i) A u *
        (weightTorusPoints n hn A s)⁻¹ =
      rootSubgroupPoints n hn (.inl i) A
        (Multiplicative.ofAdd
          ((EpsilonEridani.torusCharacter s
            (((EpsilonEridani.DynkinType.D n).simplyConnectedRootDatum
                (DynkinType.valid_D.mpr hn)).root
              ((EpsilonEridani.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex n hn i]
  exact weightTorusPoints_conj_rootSubgroupPoints n hn (.inl i) A s u

/-- On matrix-valued points, conjugation by the spin weight torus rescales the `i`-th lowering root
subgroup through the negative of the `i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorusPoints_conj_rootSubgroupPoints_neg_root_simpleIndex (i : Fin n) (A : Type v)
    [CommRing A] (s : Fin n → Aˣ) (u : Multiplicative A) :
    weightTorusPoints n hn A s * rootSubgroupPoints n hn (.inr i) A u *
        (weightTorusPoints n hn A s)⁻¹ =
      rootSubgroupPoints n hn (.inr i) A
        (Multiplicative.ofAdd
          ((EpsilonEridani.torusCharacter s
            (-((EpsilonEridani.DynkinType.D n).simplyConnectedRootDatum
                (DynkinType.valid_D.mpr hn)).root
              ((EpsilonEridani.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
            Multiplicative.toAdd u)) := by
  rw [← TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex n hn i]
  exact weightTorusPoints_conj_rootSubgroupPoints n hn (.inr i) A s u

/-- Conjugation by the spin weight torus rescales the `i`-th raising root subgroup through the
`i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorus_conj_rootSubgroup_root_simpleIndex (i : Fin n) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin n)).X)
    (u : A) :
    (s ≫ (weightTorus n hn).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n hn (.inl i)).hom.hom) *
        (s ≫ (weightTorus n hn).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((EpsilonEridani.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (((EpsilonEridani.DynkinType.D n).simplyConnectedRootDatum
                  (DynkinType.valid_D.mpr hn)).root
                ((EpsilonEridani.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
              u)) ≫
        (rootSubgroup n hn (.inl i)).hom.hom := by
  rw [← TypeDStd.rootGeneratorWeight_inl_eq_root_simpleIndex n hn i]
  exact weightTorus_conj_rootSubgroup n hn (.inl i) A s u

/-- Conjugation by the spin weight torus rescales the `i`-th lowering root subgroup through the
negative of the `i`-th simple root of the pinned type-`Dₙ` datum. -/
theorem weightTorus_conj_rootSubgroup_neg_root_simpleIndex (i : Fin n) (A : Type) [CommRing A]
    (s : (Spec (CommRingCat.of A)).asOver (Spec (CommRingCat.of ℤ)) ⟶
      (SplitTorus.groupScheme ℤ (Fin n)).X)
    (u : A) :
    (s ≫ (weightTorus n hn).hom.hom) *
        ((AdditiveGroup.groupSchemePointMulEquiv A)
            ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm
              (Multiplicative.ofAdd u)) ≫ (rootSubgroup n hn (.inr i)).hom.hom) *
        (s ≫ (weightTorus n hn).hom.hom)⁻¹ =
      (AdditiveGroup.schemePointsMulEquiv A).symm
          (Multiplicative.ofAdd
            ((EpsilonEridani.torusCharacter
              (SplitTorus.schemePointsMulEquiv (R := ℤ) (A := A) s)
              (-((EpsilonEridani.DynkinType.D n).simplyConnectedRootDatum
                  (DynkinType.valid_D.mpr hn)).root
                ((EpsilonEridani.DynkinType.D n).simpleIndex (DynkinType.valid_D.mpr hn) i)) : A) *
              u)) ≫
        (rootSubgroup n hn (.inr i)).hom.hom := by
  rw [← TypeDStd.rootGeneratorWeight_inr_eq_neg_root_simpleIndex n hn i]
  exact weightTorus_conj_rootSubgroup n hn (.inr i) A s u

end EpsilonEridani.TypeDSpinCarrier
