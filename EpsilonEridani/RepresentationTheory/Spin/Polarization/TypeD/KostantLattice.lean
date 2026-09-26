/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.Algebra.Lie.UniversalEnveloping.Kostant.Serre
public import EpsilonEridani.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
public import EpsilonEridani.RepresentationTheory.Spin.Polarization.TypeD.CartanWeights
public import EpsilonEridani.RepresentationTheory.Spin.Polarization.TypeD.Serre.Relations

import EpsilonEridani.LinearAlgebra.Eigenspace.Binomial
import EpsilonEridani.RingTheory.DividedPowers.Associative

/-!
# The type-D spinor lattice is Kostant-stable

This file turns the type-`Dₙ` Clifford Serre system into a rational representation of the
type-`D` Serre presentation and proves that its coordinate spinor lattice is stable under the
Serre Kostant form.

The positive and negative simple-root representatives act by square-zero endomorphisms and
preserve the exterior coordinate lattice. The simple-coroot representatives act diagonally on
the exterior basis with the integral weights `EpsilonEridani.DynkinType.typeDSpinWeight`; consequently
all of their binomial coefficients preserve the same lattice. These two facts give stability
under every generator of the Serre Kostant form.

The full exterior algebra, rather than either parity summand alone, is used because its weights
span the full simply connected type-`D` character lattice. Thus this is the admissible-lattice
input for the full-weight type-`D` Chevalley--Demazure carrier in Layer 9 of the ReductiveGroups
roadmap. That carrier is consumed by the `Dₙ(q)` and `²Dₙ(q)` branches of milestone L0 in the
CFSGStatement roadmap.

## Main declarations

* `EpsilonEridani.SpinPolarizationData.typeDSpinSerreRepresentation`: the type-`D` Serre presentation
  acting on the spinor module.
* `EpsilonEridani.SpinPolarizationData.typeDSpinRep`: its extension to the universal enveloping algebra.
* `EpsilonEridani.SpinPolarizationData.typeDSpinRep_rootGenerator_sq`: the represented root operators
  are square-zero.
* `EpsilonEridani.SpinPolarizationData.isCartanWeightVector_typeDSpinRep_integralLatticeBasis`: the
  integral exterior basis is a weight basis with weights `typeDSpinWeight`.
* `EpsilonEridani.SpinPolarizationData.typeDSpinRep_serreKostantForm_apply_mem_integralLattice`: the
  Serre Kostant form preserves the coordinate spinor lattice.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
* N. Bourbaki, *Groupes et algèbres de Lie*, Chapters 4--6, Plate IV.

The organization parallels the type-`B` spinor-lattice construction in Tau Ceti PR #5269; the
fork coroot and the need for both half-spin parities are the type-`D` features.
-/

public section

open CliffordAlgebra

namespace EpsilonEridani.SpinPolarizationData

universe u

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] EpsilonEridani.moduleNNRat

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) {n : ℕ} (b : Module.Basis (Fin n) ℚ P.W)
  (hn : 4 ≤ n)

/-! ## The rational spin representation -/

/-- The rational type-`D` Serre presentation acting on the spinor module through its canonical
Clifford Serre system. -/
noncomputable def typeDSpinSerreRepresentation :
    Matrix.ToLieAlgebra ℚ (CartanMatrix.D n) →ₗ⁅ℚ⁆
      Module.End ℚ (ExteriorAlgebra ℚ P.W) :=
  (spinAction Q P).toLieHom.comp
    (EpsilonEridani.serreLift (P.isSerreSystem_typeDSimpleRootBivector b hn))

/-- A Cartan generator acts through the corresponding type-`D` simple-coroot Clifford element. -/
@[simp]
theorem typeDSpinSerreRepresentation_serreH (i : Fin n) :
    P.typeDSpinSerreRepresentation b hn (EpsilonEridani.serreH ℚ (CartanMatrix.D n) i) =
      spinAction Q P (P.typeDSimpleCorootBivector b (by omega) i) := by
  simp [typeDSpinSerreRepresentation]

/-- A positive Serre generator acts through the corresponding type-`D` root Clifford element. -/
@[simp]
theorem typeDSpinSerreRepresentation_serreE (i : Fin n) :
    P.typeDSpinSerreRepresentation b hn (EpsilonEridani.serreE ℚ (CartanMatrix.D n) i) =
      spinAction Q P (P.typeDSimpleRootBivector b (by omega) i) := by
  simp [typeDSpinSerreRepresentation]

/-- A negative Serre generator acts through the corresponding negative-root Clifford element. -/
@[simp]
theorem typeDSpinSerreRepresentation_serreF (i : Fin n) :
    P.typeDSpinSerreRepresentation b hn (EpsilonEridani.serreF ℚ (CartanMatrix.D n) i) =
      spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) i) := by
  simp [typeDSpinSerreRepresentation]

/-- The type-`D` spin representation extended to the universal enveloping algebra. -/
noncomputable def typeDSpinRep :
    _root_.UniversalEnvelopingAlgebra ℚ
        (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n)) →ₐ[ℚ]
      Module.End ℚ (ExteriorAlgebra ℚ P.W) :=
  _root_.UniversalEnvelopingAlgebra.lift ℚ (P.typeDSpinSerreRepresentation b hn)

/-- An included Lie element acts through the rational Serre representation. -/
theorem typeDSpinRep_ι (x : Matrix.ToLieAlgebra ℚ (CartanMatrix.D n)) :
    P.typeDSpinRep b hn (_root_.UniversalEnvelopingAlgebra.ι ℚ x) =
      P.typeDSpinSerreRepresentation b hn x := by
  rw [typeDSpinRep, _root_.UniversalEnvelopingAlgebra.lift_ι_apply]

/-! ## Root operators -/

/-- Every represented positive or negative simple-root generator is square-zero. -/
theorem typeDSpinRep_rootGenerator_sq (k : Fin n ⊕ Fin n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (EpsilonEridani.serreRootGenerator (CartanMatrix.D n) k)) ^ 2 = 0 := by
  cases k with
  | inl i =>
      simp only [EpsilonEridani.serreRootGenerator_inl, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreE b hn, pow_two]
      exact P.spinAction_typeDSimpleRootBivector_sq b (by omega) i
  | inr i =>
      simp only [EpsilonEridani.serreRootGenerator_inr, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreF b hn, pow_two]
      exact P.spinAction_typeDSimpleNegativeRootBivector_sq b (by omega) i

/-- Every represented positive or negative simple-root generator acts nilpotently. -/
theorem isNilpotent_typeDSpinRep_rootGenerator (k : Fin n ⊕ Fin n) :
    IsNilpotent (P.typeDSpinRep b hn
      (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (EpsilonEridani.serreRootGenerator (CartanMatrix.D n) k))) :=
  ⟨2, P.typeDSpinRep_rootGenerator_sq b hn k⟩

/-- The represented positive Serre generator acts through its simple-root Clifford bivector. -/
theorem typeDSpinRep_serreE_eq_spinAction (i : Fin n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (EpsilonEridani.serreE ℚ (CartanMatrix.D n) i)) =
      spinAction Q P (P.typeDSimpleRootBivector b (by omega) i) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinSerreRepresentation_serreE b hn]

/-- The represented negative Serre generator acts through its negative simple-root Clifford
bivector. -/
theorem typeDSpinRep_serreF_eq_spinAction (i : Fin n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (EpsilonEridani.serreF ℚ (CartanMatrix.D n) i)) =
      spinAction Q P (P.typeDSimpleNegativeRootBivector b (by omega) i) := by
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinSerreRepresentation_serreF b hn]

/-- At a chain node, the positive type-`D` root generator moves the singleton exterior-basis
vector at `i + 1` to the singleton at `i`. -/
theorem typeDSpinRep_serreE_exteriorBasis_singleton {i : Fin n}
    (hnext : (i : ℕ) + 1 < n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (EpsilonEridani.serreE ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra {⟨(i : ℕ) + 1, hnext⟩}) =
      b.ExteriorAlgebra {i} := by
  rw [P.typeDSpinRep_serreE_eq_spinAction b hn,
    P.typeDSimpleRootBivector_def b, dite_eq_left hnext, map_mul, Module.End.mul_apply,
    EpsilonEridani.spinAction_ι_wedge, EpsilonEridani.spinAction_ι_contract, P.pairingEquiv_dualVector,
    EpsilonEridani.ExteriorAlgebra.basis_singleton, CliffordAlgebra.contractLeft_ι]
  simp [EpsilonEridani.ExteriorAlgebra.basis_singleton]

/-- At a chain node, the negative type-`D` root generator moves the singleton exterior-basis
vector at `i` to the singleton at `i + 1`. -/
theorem typeDSpinRep_serreF_exteriorBasis_singleton {i : Fin n}
    (hnext : (i : ℕ) + 1 < n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (EpsilonEridani.serreF ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra {i}) =
      b.ExteriorAlgebra {⟨(i : ℕ) + 1, hnext⟩} := by
  rw [P.typeDSpinRep_serreF_eq_spinAction b hn,
    P.typeDSimpleNegativeRootBivector_def b, dite_eq_left hnext, map_mul,
    Module.End.mul_apply, EpsilonEridani.spinAction_ι_wedge, EpsilonEridani.spinAction_ι_contract,
    P.pairingEquiv_dualVector, EpsilonEridani.ExteriorAlgebra.basis_singleton,
    CliffordAlgebra.contractLeft_ι]
  simp [EpsilonEridani.ExteriorAlgebra.basis_singleton]

/-- At the fork node, the positive type-`D` root generator creates the last two coordinates from
the exterior vacuum. -/
theorem typeDSpinRep_serreE_exteriorBasis_empty {i : Fin n}
    (hlast : ¬(i : ℕ) + 1 < n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (EpsilonEridani.serreE ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra ∅) =
      EpsilonEridani.ExteriorAlgebra.basisEraseSign (⟨n - 2, by omega⟩ : Fin n)
          {(⟨n - 2, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)} •
        b.ExteriorAlgebra {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} := by
  rw [P.typeDSpinRep_serreE_eq_spinAction b hn,
    P.typeDSimpleRootBivector_def b, dite_eq_right hlast, map_mul, Module.End.mul_apply,
    EpsilonEridani.spinAction_ι_wedge, EpsilonEridani.spinAction_ι_wedge]
  have hEmpty : b.ExteriorAlgebra (∅ : Finset (Fin n)) = 1 := by
    rw [ExteriorAlgebra.basis_apply]
    simp
  rw [hEmpty, mul_one]
  rw [← EpsilonEridani.ExteriorAlgebra.basis_singleton,
    ← EpsilonEridani.ExteriorAlgebra.basis_singleton]
  have h := EpsilonEridani.ExteriorAlgebra.basis_singleton_mul_basis_erase b
    ⟨n - 2, by omega⟩ {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩} (by simp)
  rw [Finset.erase_insert (by
    simp only [Finset.mem_singleton]
    intro hEq
    have := congrArg Fin.val hEq
    dsimp only at this
    omega)] at h
  exact h

/-- At the fork node, the negative type-`D` root generator annihilates the last two coordinates
to the exterior vacuum. -/
theorem typeDSpinRep_serreF_exteriorBasis_pair {i : Fin n}
    (hlast : ¬(i : ℕ) + 1 < n) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ (EpsilonEridani.serreF ℚ (CartanMatrix.D n) i))
        (b.ExteriorAlgebra {⟨n - 2, by omega⟩, ⟨n - 1, by omega⟩}) =
      (EpsilonEridani.ExteriorAlgebra.basisEraseSign (⟨n - 2, by omega⟩ : Fin n)
          {(⟨n - 2, by omega⟩ : Fin n), (⟨n - 1, by omega⟩ : Fin n)} *
        EpsilonEridani.ExteriorAlgebra.basisEraseSign (⟨n - 1, by omega⟩ : Fin n)
          {(⟨n - 1, by omega⟩ : Fin n)}) • b.ExteriorAlgebra ∅ := by
  rw [P.typeDSpinRep_serreF_eq_spinAction b hn,
    P.typeDSimpleNegativeRootBivector_def b, dite_eq_right hlast, map_mul,
    Module.End.mul_apply, EpsilonEridani.spinAction_ι_contract, P.pairingEquiv_dualVector,
    EpsilonEridani.spinAction_ι_contract, P.pairingEquiv_dualVector,
    EpsilonEridani.ExteriorAlgebra.contractLeft_coord_basis]
  rw [ite_eq_left (by simp), Finset.erase_insert (by
    simp only [Finset.mem_singleton]
    intro hEq
    have := congrArg Fin.val hEq
    dsimp only at this
    omega), Units.smul_def,
    ← Int.cast_smul_eq_zsmul ℚ, map_smul]
  rw [EpsilonEridani.ExteriorAlgebra.contractLeft_coord_basis]
  simp only [Finset.mem_singleton, ↓reduceIte, Finset.erase_singleton, Units.smul_def,
    Units.val_mul]
  simp_rw [← Int.cast_smul_eq_zsmul ℚ]
  rw [smul_smul, Int.cast_mul]

/-- Every represented positive or negative simple-root generator preserves the coordinate spinor
lattice. -/
theorem typeDSpinRep_rootGenerator_apply_mem_integralLattice
    (k : Fin n ⊕ Fin n) {v : ExteriorAlgebra ℚ P.W}
    (hv : v ∈ EpsilonEridani.ExteriorAlgebra.integralLattice b) :
    P.typeDSpinRep b hn
        (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (EpsilonEridani.serreRootGenerator (CartanMatrix.D n) k)) v ∈
      EpsilonEridani.ExteriorAlgebra.integralLattice b := by
  cases k with
  | inl i =>
      rw [EpsilonEridani.serreRootGenerator_inl, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreE b hn]
      exact (P.mem_integralSpinActionSubring b).mp
        (P.typeDSimpleRootBivector_mem_integralSpinActionSubring b (by omega) i) hv
  | inr i =>
      rw [EpsilonEridani.serreRootGenerator_inr, P.typeDSpinRep_ι b hn,
        P.typeDSpinSerreRepresentation_serreF b hn]
      exact (P.mem_integralSpinActionSubring b).mp
        (P.typeDSimpleNegativeRootBivector_mem_integralSpinActionSubring b (by omega) i) hv

/-! ## Cartan weights and binomial operators -/

/-- Every exterior-basis vector is a Cartan weight vector for the type-`D` spin representation,
with its integral simply connected spin weight. -/
theorem isCartanWeightVector_typeDSpinRep_exteriorBasis (s : Finset (Fin n)) :
    EpsilonEridani.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)
      (EpsilonEridani.DynkinType.typeDSpinWeight s) (b.ExteriorAlgebra s) := by
  refine (EpsilonEridani.UniversalEnvelopingAlgebra.isCartanWeightVector_iff
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)).mpr fun i ↦ ?_
  rw [P.typeDSpinRep_ι b hn, P.typeDSpinSerreRepresentation_serreH b hn]
  simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
    (P.spinAction_typeDSimpleCorootBivector_basis b (by omega) i s)

/-- The integral exterior basis is a Cartan weight basis for the type-`D` spin representation. -/
theorem isCartanWeightVector_typeDSpinRep_integralLatticeBasis (s : Finset (Fin n)) :
    EpsilonEridani.UniversalEnvelopingAlgebra.IsCartanWeightVector
      (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)
      (EpsilonEridani.DynkinType.typeDSpinWeight s)
      (((EpsilonEridani.ExteriorAlgebra.integralLatticeBasis b) s :
        EpsilonEridani.ExteriorAlgebra.integralLattice b) : ExteriorAlgebra ℚ P.W) := by
  rw [EpsilonEridani.ExteriorAlgebra.coe_integralLatticeBasis]
  exact P.isCartanWeightVector_typeDSpinRep_exteriorBasis b hn s

/-- Every binomial coefficient in a represented simple-coroot generator preserves the coordinate
spinor lattice. -/
theorem typeDSpinRep_ringChoose_serreH_apply_mem_integralLattice
    (i : Fin n) (m : ℕ) {v : ExteriorAlgebra ℚ P.W}
    (hv : v ∈ EpsilonEridani.ExteriorAlgebra.integralLattice b) :
    P.typeDSpinRep b hn
        (Ring.choose (_root_.UniversalEnvelopingAlgebra.ι ℚ
          (EpsilonEridani.serreH ℚ (CartanMatrix.D n) i)) m) v ∈
      EpsilonEridani.ExteriorAlgebra.integralLattice b := by
  rw [Ring.map_choose]
  refine EpsilonEridani.ExteriorAlgebra.map_mem_integralLattice b
    ((Ring.choose (P.typeDSpinRep b hn
      (_root_.UniversalEnvelopingAlgebra.ι ℚ
        (EpsilonEridani.serreH ℚ (CartanMatrix.D n) i))) m).restrictScalars ℤ)
    (fun s ↦ ?_) hv
  rw [LinearMap.restrictScalars_apply, P.typeDSpinRep_ι b hn,
    P.typeDSpinSerreRepresentation_serreH b hn]
  rw [EpsilonEridani.ringChoose_end_apply_of_apply_eq_smul
      (by
        simpa only [algebraMap_int_eq, Int.coe_castRingHom] using
          (P.spinAction_typeDSimpleCorootBivector_basis b (by omega) i s)),
    Ring.choose_intCast, Int.cast_smul_eq_zsmul ℚ]
  exact Submodule.smul_mem _ _ (EpsilonEridani.ExteriorAlgebra.basis_mem_integralLattice b s)

/-! ## Stability under the Serre Kostant form -/

/-- **The coordinate spinor lattice is admissible for the type-`D` Serre Kostant form.** -/
theorem typeDSpinRep_serreKostantForm_apply_mem_integralLattice
    {u : _root_.UniversalEnvelopingAlgebra ℚ
      (Matrix.ToLieAlgebra ℚ (CartanMatrix.D n))}
    (hu : u ∈ EpsilonEridani.serreKostantForm (CartanMatrix.D n))
    {v : ExteriorAlgebra ℚ P.W}
    (hv : v ∈ EpsilonEridani.ExteriorAlgebra.integralLattice b) :
    P.typeDSpinRep b hn u v ∈ EpsilonEridani.ExteriorAlgebra.integralLattice b := by
  rw [EpsilonEridani.serreKostantForm_def] at hu
  exact EpsilonEridani.UniversalEnvelopingAlgebra.kostantForm_apply_mem
    (EpsilonEridani.serreRootGenerator (CartanMatrix.D n))
    (EpsilonEridani.serreH ℚ (CartanMatrix.D n)) (P.typeDSpinRep b hn)
    (EpsilonEridani.ExteriorAlgebra.integralLattice b)
    (fun k m _ hw ↦ by
      rw [Associative.map_dividedPower]
      exact Associative.dividedPower_apply_mem_of_pow_two_eq_zero _
        (EpsilonEridani.ExteriorAlgebra.integralLattice b).toAddSubgroup
        (P.typeDSpinRep_rootGenerator_sq b hn k)
        (fun hw' ↦ P.typeDSpinRep_rootGenerator_apply_mem_integralLattice b hn k hw') m hw)
    (fun i m _ hw ↦
      P.typeDSpinRep_ringChoose_serreH_apply_mem_integralLattice b hn i m hw) u hu hv

end EpsilonEridani.SpinPolarizationData
