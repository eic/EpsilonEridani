/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib

/-!
# Parton species and their charge conjugation

For a hadron whose quarks come in the flavours of a type `Flavor`, the parton species are the
quark and the antiquark of each flavour and the gluon. This file names that index type,
`Species Flavor`, so that the quark, antiquark and gluon distributions of a hadron (collinear
densities, TMDs, fragmentation functions) are indexed by one type, and a species sum such as the
momentum sum rule `∑ₛ ∫₀¹ x fₛ(x) dx = 1` runs over all of them, the gluon included.

Charge conjugation exchanges the quark and the antiquark of each flavour and fixes the gluon
(`Species.conj`); it is an involution.

## Main definitions

* `EpsilonEridani.Particles.Parton.Species Flavor`: a quark or antiquark of a flavour, or the gluon.
* `EpsilonEridani.Particles.Parton.Species.equivSum`: `Species Flavor ≃ (Flavor ⊕ Flavor) ⊕ Unit`.
* `EpsilonEridani.Particles.Parton.Species.conj`: charge conjugation of species.

## Main statements

* `Species.card`: there are `2 * Fintype.card Flavor + 1` species.
* `Species.sum_univ`: a sum over all species is the quark sum, the antiquark sum and the gluon term.
* `Species.conj_involutive`: charge conjugation is an involution.

## References

* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), ch. 6.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton

/-- A parton species over the quark-flavour type `Flavor`: the quark of a flavour, the antiquark
of a flavour, or the gluon. -/
inductive Species (Flavor : Type) where
  /-- The quark of flavour `i`. -/
  | quark (i : Flavor)
  /-- The antiquark of flavour `i`. -/
  | antiquark (i : Flavor)
  /-- The gluon. -/
  | gluon
  deriving DecidableEq

namespace Species

variable {Flavor : Type}

/-- The species over `Flavor` are equivalent to `(Flavor ⊕ Flavor) ⊕ Unit`: the quark of flavour
`i` goes to `.inl (.inl i)`, the antiquark of flavour `i` to `.inl (.inr i)`, and the gluon to
`.inr ()`. It carries the `Fintype` instance on species and `sum_univ`. -/
def equivSum : Species Flavor ≃ (Flavor ⊕ Flavor) ⊕ Unit where
  toFun
    | quark i => .inl (.inl i)
    | antiquark i => .inl (.inr i)
    | gluon => .inr ()
  invFun
    | .inl (.inl i) => quark i
    | .inl (.inr i) => antiquark i
    | .inr _ => gluon
  left_inv s := by cases s <;> rfl
  right_inv s := by rcases s with (i | i) | _ <;> rfl

@[simp]
theorem equivSum_quark (i : Flavor) : equivSum (quark i) = .inl (.inl i) := (rfl)

@[simp]
theorem equivSum_antiquark (i : Flavor) : equivSum (antiquark i) = .inl (.inr i) := (rfl)

@[simp]
theorem equivSum_gluon : equivSum (gluon : Species Flavor) = .inr () := (rfl)

@[simp]
theorem equivSum_symm_inl_inl (i : Flavor) : equivSum.symm (.inl (.inl i)) = quark i := (rfl)

@[simp]
theorem equivSum_symm_inl_inr (i : Flavor) : equivSum.symm (.inl (.inr i)) = antiquark i := (rfl)

@[simp]
theorem equivSum_symm_inr (u : Unit) : (equivSum.symm (.inr u) : Species Flavor) = gluon := (rfl)

instance [Fintype Flavor] : Fintype (Species Flavor) := Fintype.ofEquiv _ equivSum.symm

/-- There are two species, a quark and an antiquark, for each flavour, and the gluon. -/
@[simp]
theorem card [Fintype Flavor] :
    Fintype.card (Species Flavor) = 2 * Fintype.card Flavor + 1 := by
  rw [Fintype.card_congr equivSum, Fintype.card_sum, Fintype.card_sum, Fintype.card_unit, two_mul]

/-- A sum over all parton species is the sum over the quarks, the sum over the antiquarks, and
the gluon term. -/
theorem sum_univ [Fintype Flavor] {M : Type*} [AddCommMonoid M] (g : Species Flavor → M) :
    ∑ s, g s = ∑ i, g (quark i) + ∑ i, g (antiquark i) + g gluon := by
  rw [← equivSum.symm.sum_comp]
  simp [Fintype.sum_sum_type]

/-- Charge conjugation of parton species: the quark and the antiquark of each flavour are
exchanged, and the gluon is its own antiparticle. -/
def conj : Species Flavor → Species Flavor
  | quark i => antiquark i
  | antiquark i => quark i
  | gluon => gluon

@[simp]
theorem conj_quark (i : Flavor) : (quark i).conj = antiquark i := (rfl)

@[simp]
theorem conj_antiquark (i : Flavor) : (antiquark i).conj = quark i := (rfl)

@[simp]
theorem conj_gluon : (gluon : Species Flavor).conj = gluon := (rfl)

@[simp]
theorem conj_conj (s : Species Flavor) : s.conj.conj = s := by
  cases s <;> simp

theorem conj_involutive : Function.Involutive (conj : Species Flavor → Species Flavor) :=
  conj_conj

end Species

end Parton
end Particles
end EpsilonEridani
