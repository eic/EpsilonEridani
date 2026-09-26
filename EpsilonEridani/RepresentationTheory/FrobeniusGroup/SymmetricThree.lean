/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import EpsilonEridani.GroupTheory.Perm.FinThree
public import EpsilonEridani.RepresentationTheory.FrobeniusGroup.Basic

/-!
# A Frobenius group: `S₃` with complement a point stabilizer

`S₃` is the smallest Frobenius group.  It decomposes as `A₃ ⋊ ⟨(a+1 a+2)⟩`, with complement the
point stabilizer of `a` -- of order two -- and kernel the alternating subgroup, of order three;
the complement acts on the kernel without nonidentity fixed points because a transposition
inverts each of the two three-cycles, and a three-cycle is not its own inverse.

That makes `S₃` a place to run the character-theoretic construction of
`EpsilonEridani/RepresentationTheory/FrobeniusGroup/Basic.lean` against a group whose normal complement is
already known.  The Frobenius kernel is built as the common kernel of representations affording
the extended irreducible characters of the two-element subgroup `⟨(a+1 a+2)⟩`, with no reference
to `A₃` anywhere in the construction, and it comes out equal to `A₃`
(`EpsilonEridani.frobeniusKernelSubgroup_stabilizer_perm_fin_three`).

The group theory this consumes -- the complementarity, the fixed-point freeness, and the
trivial-intersection property `EpsilonEridani.isTISubgroup_stabilizer_perm_fin_three` they yield -- is
settled over the six permutations in `EpsilonEridani/GroupTheory/Perm/FinThree.lean`, as the rest of the
description of the two subgroups of `S₃` is.  All this file adds is the passage through the
character theory.

## Main statements

* `EpsilonEridani.frobeniusKernelSubgroup_stabilizer_perm_fin_three`: **the Frobenius kernel of a point
  stabilizer of `S₃` is `A₃`**, of order three by
  `EpsilonEridani.card_frobeniusKernelSubgroup_stabilizer_perm_fin_three`.
-/

public section

namespace EpsilonEridani

/-- **The Frobenius kernel of a point stabilizer of `S₃` is the alternating group `A₃`.**  The
kernel that the exceptional-character correspondence constructs -- as the common kernel of
representations affording the extended irreducible characters of the two-element subgroup
`⟨(a+1 a+2)⟩`, with no reference to `A₃` at all -- is the alternating subgroup that the semidirect
decomposition `S₃ = A₃ ⋊ ⟨(a+1 a+2)⟩` supplies directly. -/
@[simp]
theorem frobeniusKernelSubgroup_stabilizer_perm_fin_three (a : Fin 3) :
    frobeniusKernelSubgroup (isTISubgroup_stabilizer_perm_fin_three a)
      = alternatingGroup (Fin 3) :=
  frobeniusKernelSubgroup_eq_of_isComplement' _
    (isComplement'_alternatingGroup_stabilizer_perm_fin_three a)

/-- **The Frobenius kernel of a point stabilizer of `S₃` has order three.** -/
theorem card_frobeniusKernelSubgroup_stabilizer_perm_fin_three (a : Fin 3) :
    Nat.card (frobeniusKernelSubgroup (isTISubgroup_stabilizer_perm_fin_three a)) = 3 := by
  rw [frobeniusKernelSubgroup_stabilizer_perm_fin_three, card_alternatingGroup_fin_three]

end EpsilonEridani
