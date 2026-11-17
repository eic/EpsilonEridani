/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Data.Fintype.BigOperators

/-!
# Parton species and their charge conjugation

For a hadron whose quarks come in the flavours of a type `Flavor`, the parton species are the
quark and the antiquark of each flavour and the gluon. This file names that index type,
`Species Flavor`, so that the quark, antiquark and gluon distributions of a hadron (collinear
densities, TMDs, fragmentation functions) are indexed by one type, and a species sum such as the
momentum sum rule `∑ₛ ∫₀¹ x fₛ(x) dx = 1` runs over all of them, the gluon included.

Charge conjugation exchanges the quark and the antiquark of each flavour and fixes the gluon
(`Species.conj`); it is an involution. A map of flavours induces a map of species
(`Species.map`), which relabels the flavour of each quark and antiquark and fixes the gluon; it
commutes with charge conjugation, and the flavour exchanges of isospin and SU(3) symmetry act on
the species through it.

## Main definitions

* `EpsilonEridani.Particles.Parton.Species Flavor`: a quark or antiquark of a flavour, or the gluon.
* `EpsilonEridani.Particles.Parton.Species.equivSum`: `Species Flavor ≃ (Flavor ⊕ Flavor) ⊕ Unit`.
* `EpsilonEridani.Particles.Parton.Species.conj`: charge conjugation of species.
* `EpsilonEridani.Particles.Parton.Species.map`: the species map induced by a map of flavours.

## Main statements

* `Species.card`: there are `2 * Fintype.card Flavor + 1` species.
* `Species.sum_univ`: a sum over all species is the quark sum, the antiquark sum and the gluon term.
* `Species.conj_involutive`: charge conjugation is an involution.
* `Species.conj_map`: relabelling the flavours commutes with charge conjugation.

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
  simp [Fintype.sum_sum_type, one_nsmul]

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

/-! ### Relabelling the flavours -/

/-- The species map induced by a map of flavours: the quark and the antiquark of flavour `i` go to
the quark and the antiquark of flavour `σ i`, and the gluon is fixed. -/
def map {Flavor' : Type} (σ : Flavor → Flavor') : Species Flavor → Species Flavor'
  | quark i => quark (σ i)
  | antiquark i => antiquark (σ i)
  | gluon => gluon

section Map

variable {Flavor' Flavor'' : Type}

@[simp]
theorem map_quark (σ : Flavor → Flavor') (i : Flavor) : (quark i).map σ = quark (σ i) := (rfl)

@[simp]
theorem map_antiquark (σ : Flavor → Flavor') (i : Flavor) :
    (antiquark i).map σ = antiquark (σ i) := (rfl)

@[simp]
theorem map_gluon (σ : Flavor → Flavor') : (gluon : Species Flavor).map σ = gluon := (rfl)

@[simp]
theorem map_id (s : Species Flavor) : s.map id = s := by
  cases s <;> rfl

@[simp]
theorem map_map (σ : Flavor → Flavor') (τ : Flavor' → Flavor'') (s : Species Flavor) :
    (s.map σ).map τ = s.map (τ ∘ σ) := by
  cases s <;> rfl

/-- Relabelling the flavours commutes with charge conjugation. -/
@[simp]
theorem conj_map (σ : Flavor → Flavor') (s : Species Flavor) : (s.map σ).conj = s.conj.map σ := by
  cases s <;> rfl

/-- The species map of an involution of the flavours is an involution. -/
theorem map_involutive {σ : Flavor → Flavor} (hσ : Function.Involutive σ) :
    Function.Involutive (map σ) := fun s => by
  rw [map_map, hσ.comp_self, map_id]

end Map

end Species

end Parton
end Particles
end EpsilonEridani
