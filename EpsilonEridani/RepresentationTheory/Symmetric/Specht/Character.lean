/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.RepresentationTheory.CharacterTable.Values
public import EpsilonEridani.RepresentationTheory.Symmetric.Partitions
public import EpsilonEridani.RepresentationTheory.Symmetric.Specht.Module

/-!
# The integer character of a Specht module, and the character table of `Sₙ`

The Specht module `S^μ` is a representation of `Sₙ` over `ℚ`, so its character
`(spechtModule μ).character` takes values in `ℚ`. Those values are in fact **integers**: a
character value at an element of finite order is an algebraic integer, and a rational algebraic
integer is an integer. That refinement is what this file records, as
`EpsilonEridani.spechtChar μ : Equiv.Perm (Fin n) → ℤ`, together with the cast
`EpsilonEridani.spechtChar_cast` back to the rational character; integrality is a theorem, not part of
the definition.

A character is a class function, and the conjugacy classes of `Sₙ` are the partitions of `n`
(`EpsilonEridani.partitionEquivConjClasses`), so `spechtChar μ` descends to a function of a partition
`ν`, its **character value** `EpsilonEridani.spechtCharValue μ ν`. Both indices being partitions of `n`,
these values assemble into a square integer matrix, the **character table of the symmetric group**
`EpsilonEridani.symmetricCharacterTable n`. Its rows are indexed by the Specht modules, which are
precisely the irreducible rational representations of `Sₙ`
(`EpsilonEridani.partitionEquivSimpleModuleClasses`), and its columns by the conjugacy classes; the
column of the identity holds the degrees.

The general half of the argument is stated for an arbitrary rational representation of a finite
group, as `FDRep.intCharacter`, and is what this file specializes. Nothing here computes
an entry of the table: the recursion that does is the Murnaghan--Nakayama rule, which needs rim
hooks and is not proved here. The comparison with the library's general
`EpsilonEridani.characterTable k G`, which lives over an algebraically closed field and enumerates its
rows by `Fin (Nat.card (ConjClasses G))`, and the table properties that one carries — the
orthogonality relations and the specification `EpsilonEridani.IsCharacterTableSpec` — are in
`EpsilonEridani/RepresentationTheory/Symmetric/Specht/Orthogonality.lean`.

## Main definitions

* `EpsilonEridani.spechtChar`: the `ℤ`-valued character `χ^μ` of the Specht module `S^μ`.
* `EpsilonEridani.spechtCharConjClasses`: its descent to the conjugacy classes of `Sₙ`.
* `EpsilonEridani.spechtCharValue`: its value on the class of cycle type `ν`.
* `EpsilonEridani.symmetricCharacterTable`: the character table of `Sₙ`, a
  `Matrix (Nat.Partition n) (Nat.Partition n) ℤ`.

## Main results

* `EpsilonEridani.spechtChar_cast`: the integer character casts to the rational character of `S^μ`.
* `EpsilonEridani.spechtChar_eq_of_partition_eq`: it depends only on the cycle type.
* `EpsilonEridani.spechtChar_one`: the value at the identity is the degree `dim_ℚ S^μ`.
* `EpsilonEridani.spechtChar_one_pos`: that degree is positive.
* `EpsilonEridani.spechtChar_eq_value`: the character is read off the character table.
* `EpsilonEridani.intCast_symmetricCharacterTable_apply`: conversely the table recovers the rational
  character, so no information is lost in passing to `ℤ`.
* `EpsilonEridani.symmetricCharacterTable_one`: the column of the identity class holds the degrees.

## References

* [G. D. James, *The Representation Theory of the Symmetric Groups*][james1978], Chapter 6.
* B. E. Sagan, *The Symmetric Group*, 2nd ed. (2001), Section 4.10.
* [Schur--Weyl roadmap](https://github.com/EpsilonEridaniProject/EpsilonEridaniRoadmap/blob/main/EpsilonEridaniRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 6, "The Specht character".
-/

public section

namespace EpsilonEridani

open Module

variable {n : ℕ}

/-! ## The integer character -/

/-- **The integer character `χ^μ` of the Specht module** `S^μ`. The character of `S^μ` takes
rational values, and those values are integers (`FDRep.intCharacter`); this is the
integer-valued refinement, related to the rational character by `EpsilonEridani.spechtChar_cast`. -/
noncomputable def spechtChar (μ : n.Partition) : Equiv.Perm (Fin n) → ℤ :=
  FDRep.intCharacter (spechtModule μ)

theorem spechtChar_def (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtChar μ σ = FDRep.intCharacter (spechtModule μ) σ := (rfl)

/-- **The integer character of `S^μ` casts to its rational character.** This is the whole content
of `EpsilonEridani.spechtChar`: the character of a Specht module is integer-valued. -/
@[simp]
theorem spechtChar_cast (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    (spechtChar μ σ : ℚ) = (spechtModule μ).character σ := by
  rw [spechtChar_def, FDRep.intCharacter_cast]

/-- **The integer character is a class function.** -/
@[simp]
theorem spechtChar_conj (μ : n.Partition) (σ τ : Equiv.Perm (Fin n)) :
    spechtChar μ (τ * σ * τ⁻¹) = spechtChar μ σ :=
  FDRep.intCharacter_conj (spechtModule μ) σ τ

/-- Conjugate permutations have the same integer character. -/
theorem spechtChar_eq_of_isConj (μ : n.Partition) {σ τ : Equiv.Perm (Fin n)} (h : IsConj σ τ) :
    spechtChar μ σ = spechtChar μ τ :=
  FDRep.intCharacter_eq_of_isConj (spechtModule μ) h

/-- **The integer character depends only on the cycle type**, two permutations of `Fin n` being
conjugate exactly when they have the same partition. -/
theorem spechtChar_eq_of_partition_eq (μ : n.Partition) {σ τ : Equiv.Perm (Fin n)}
    (h : σ.partition = τ.partition) : spechtChar μ σ = spechtChar μ τ :=
  spechtChar_eq_of_isConj μ (Equiv.Perm.partition_eq_of_isConj.mpr h)

/-- **The value at the identity is the degree** `dim_ℚ S^μ`. -/
@[simp]
theorem spechtChar_one (μ : n.Partition) : spechtChar μ 1 = finrank ℚ (spechtModule μ) :=
  FDRep.intCharacter_one (spechtModule μ)

/-- **The value at the identity is positive**, the Specht module `S^μ` being nonzero. -/
theorem spechtChar_one_pos (μ : n.Partition) : 0 < spechtChar μ 1 := by
  rw [spechtChar_one]
  exact_mod_cast finrank_spechtModule_pos μ

/-! ## Descent to the conjugacy classes -/

/-- **The integer character as a function of the conjugacy class**, the descent
(`EpsilonEridani.ClassFunction.toConjClasses`) of the class function `FDRep.intClassFunction` of
`S^μ`. -/
noncomputable def spechtCharConjClasses (μ : n.Partition) : ConjClasses (Equiv.Perm (Fin n)) → ℤ :=
  ClassFunction.toConjClasses (FDRep.intClassFunction (spechtModule μ))

theorem spechtCharConjClasses_def (μ : n.Partition) :
    spechtCharConjClasses μ =
      ClassFunction.toConjClasses (FDRep.intClassFunction (spechtModule μ)) := (rfl)

@[simp]
theorem spechtCharConjClasses_mk (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtCharConjClasses μ (ConjClasses.mk σ) = spechtChar μ σ := by
  rw [spechtCharConjClasses_def, ClassFunction.toConjClasses_mk, FDRep.intClassFunction_apply,
    spechtChar_def]

/-- **The character value of `S^μ` on the class of cycle type `ν`**, the entry `χ^μ(ν)` of the
character table. -/
noncomputable def spechtCharValue (μ ν : n.Partition) : ℤ :=
  spechtCharConjClasses μ (partitionEquivConjClasses n ν)

theorem spechtCharValue_def (μ ν : n.Partition) :
    spechtCharValue μ ν = spechtCharConjClasses μ (partitionEquivConjClasses n ν) := (rfl)

/-- The character value is computed at any permutation representing the class of `ν`. -/
theorem spechtCharValue_eq_spechtChar (μ ν : n.Partition) {σ : Equiv.Perm (Fin n)}
    (hσ : ConjClasses.mk σ = partitionEquivConjClasses n ν) :
    spechtCharValue μ ν = spechtChar μ σ := by
  rw [spechtCharValue_def, ← hσ, spechtCharConjClasses_mk]

/-- **The integer character is read off the character table**, at the partition indexing the class
of the permutation. -/
theorem spechtChar_eq_value (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    spechtChar μ σ =
      spechtCharValue μ ((partitionEquivConjClasses n).symm (ConjClasses.mk σ)) := by
  rw [spechtCharValue_def, Equiv.apply_symm_apply, spechtCharConjClasses_mk]

/-! ## The character table -/

/-- **The character table of the symmetric group `Sₙ`**: the integer matrix whose `(μ, ν)` entry is
the value `χ^μ(ν)` of the character of the Specht module `S^μ` on the conjugacy class of cycle
type `ν`. Both indices are partitions of `n`, which index the irreducible rational representations
(`EpsilonEridani.partitionEquivSimpleModuleClasses`) and the conjugacy classes
(`EpsilonEridani.partitionEquivConjClasses`) respectively.

Implementation note: this is not the library's general `EpsilonEridani.characterTable k G`, which is
defined over an algebraically closed field, takes values there, and enumerates its rows by
`Fin (Nat.card (ConjClasses G))` through an arbitrary choice of ordering of the irreducible
characters. This matrix is the `ℤ`-valued table of `Sₙ` re-indexed on both sides by the partitions
of `n`; the comparison with `EpsilonEridani.characterTable ℂ (Equiv.Perm (Fin n))` and the table
properties the general table carries — the orthogonality relations and the character-table
specification `EpsilonEridani.IsCharacterTableSpec` — are proved in
`EpsilonEridani/RepresentationTheory/Symmetric/Specht/Orthogonality.lean`. -/
noncomputable def symmetricCharacterTable (n : ℕ) : Matrix n.Partition n.Partition ℤ :=
  Matrix.of fun μ ν => spechtCharValue μ ν

@[simp]
theorem symmetricCharacterTable_apply (μ ν : n.Partition) :
    symmetricCharacterTable n μ ν = spechtCharValue μ ν := (rfl)

/-- **The character table recovers the rational characters of the Specht modules**, so passing from
`ℚ` to `ℤ` and from permutations to cycle types loses nothing. -/
theorem intCast_symmetricCharacterTable_apply (μ : n.Partition) (σ : Equiv.Perm (Fin n)) :
    ((symmetricCharacterTable n μ
        ((partitionEquivConjClasses n).symm (ConjClasses.mk σ)) : ℤ) : ℚ) =
      (spechtModule μ).character σ := by
  rw [symmetricCharacterTable_apply, ← spechtChar_eq_value, spechtChar_cast]

/-- **The column of the identity holds the degrees** `dim_ℚ S^μ`. -/
theorem symmetricCharacterTable_one (μ : n.Partition) :
    symmetricCharacterTable n μ ((partitionEquivConjClasses n).symm (ConjClasses.mk 1)) =
      finrank ℚ (spechtModule μ) := by
  rw [symmetricCharacterTable_apply, ← spechtChar_eq_value, spechtChar_one]

end EpsilonEridani
