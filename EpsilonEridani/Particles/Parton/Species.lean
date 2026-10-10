/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.Basic

/-!
# Parton species, charge conjugation, and valence numbers

A collinear density `PDF.Pdf ι` is indexed by a type `ι` of parton species. For a hadron whose
quarks come in the flavours of a type `Flavor`, the species are the quark and the antiquark of
each flavour and the gluon. This file names that index type, `Species Flavor`, so that the quark,
antiquark and gluon densities of a hadron are members of one `PDF.Pdf`, and a flavour sum such as
the momentum sum rule `∑ₛ ∫₀¹ x fₛ(x) dx = 1` runs over all of them, the gluon included.

Charge conjugation exchanges the quark and the antiquark of each flavour and fixes the gluon
(`Species.conj`). On densities it acts by relabelling, `PDF.chargeConj f s = f s.conj`: the
densities of a hadron's antiparticle are the charge conjugates of the hadron's densities. The
operation is an involution, it preserves `PDF.Assumptions`, the momentum sum and the sum-rule
bundle `PDF.SumRuleAssumptions`.

On a density over `Species Flavor` the integral `∫₀¹ (q_i(x) - qbar_i(x)) dx` is the net number of
quarks of flavour `i`, the valence number `PDF.valenceNumber`. The valence sum rules of a hadron
prescribe it flavour by flavour. Charge conjugation negates every valence number, so a
charge-conjugation invariant density has no valence number in any flavour.

## Main definitions

* `EpsilonEridani.Particles.Parton.Species Flavor`: a quark or antiquark of a flavour, or the gluon.
* `EpsilonEridani.Particles.Parton.Species.conj`: charge conjugation of species.
* `EpsilonEridani.Particles.Parton.PDF.chargeConj`: the charge-conjugate density.
* `EpsilonEridani.Particles.Parton.PDF.valenceNumber`: `∫₀¹ (q_i - qbar_i)`.

## Main statements

* `Species.sum_univ`: a sum over all species is the quark sum, the antiquark sum and the gluon term.
* `PDF.Assumptions.chargeConj`, `PDF.SumRuleAssumptions.chargeConj`: charge conjugation preserves
  the density assumptions and the sum-rule bundle.
* `PDF.sum_mellinMoment_chargeConj`: it preserves every flavour-summed moment, in particular the
  momentum sum.
* `PDF.valenceNumber_chargeConj`: it negates the valence numbers.
* `PDF.valenceNumber_eq_zero_of_chargeConj_eq`: a charge-conjugation invariant density has
  vanishing valence numbers.
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

/-- The species over `Flavor` are a quark flavour, an antiquark flavour, or the gluon. -/
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
  simp [Fintype.sum_sum_type, equivSum]

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

namespace PDF

open Species

variable {Flavor : Type}

/-- The charge-conjugate density: the density of species `s` is the density of `s.conj` in `f`.
The densities of a hadron's antiparticle are the charge conjugates of the hadron's densities. -/
def chargeConj (f : Pdf (Species Flavor)) : Pdf (Species Flavor) :=
  fun s => f s.conj

@[simp]
theorem chargeConj_apply (f : Pdf (Species Flavor)) (s : Species Flavor) (x Q2 : ℝ) :
    chargeConj f s x Q2 = f s.conj x Q2 :=
  (rfl)

@[simp]
theorem chargeConj_chargeConj (f : Pdf (Species Flavor)) : chargeConj (chargeConj f) = f := by
  ext s x Q2
  simp

theorem chargeConj_involutive :
    Function.Involutive (chargeConj : Pdf (Species Flavor) → Pdf (Species Flavor)) :=
  chargeConj_chargeConj

@[simp]
theorem mellinMoment_chargeConj (f : Pdf (Species Flavor)) (n : ℕ) (s : Species Flavor)
    (Q2 : ℝ) : mellinMoment (chargeConj f) n s Q2 = mellinMoment f n s.conj Q2 :=
  (rfl)

/-- Charge conjugation preserves every moment summed over all species; for `n = 1` this is the
statement that the momentum sum of the conjugate density is that of the density. -/
theorem sum_mellinMoment_chargeConj [Fintype Flavor] (f : Pdf (Species Flavor)) (n : ℕ)
    (Q2 : ℝ) : ∑ s, mellinMoment (chargeConj f) n s Q2 = ∑ s, mellinMoment f n s Q2 := by
  simp only [mellinMoment_chargeConj]
  exact conj_involutive.bijective.sum_comp fun s => mellinMoment f n s Q2

/-- Charge conjugation preserves the density assumptions. -/
theorem Assumptions.chargeConj {f : Pdf (Species Flavor)} (h : Assumptions f) :
    Assumptions (chargeConj f) where
  support s x Q2 hx := h.support s.conj x Q2 hx
  nonneg s x Q2 hx₀ hx₁ := h.nonneg s.conj x Q2 hx₀ hx₁
  measurable s Q2 := h.measurable s.conj Q2
  momentIntegrable n s Q2 := h.momentIntegrable n s.conj Q2

/-- Charge conjugation preserves the sum-rule bundle, with the target values of each species
taken from its conjugate. -/
def SumRuleAssumptions.chargeConj [Fintype Flavor] {f : Pdf (Species Flavor)}
    (h : SumRuleAssumptions f) : SumRuleAssumptions (chargeConj f) where
  momentum Q2 := (sum_mellinMoment_chargeConj f 1 Q2).trans (h.momentum Q2)
  valenceTarget s := h.valenceTarget s.conj
  valence s Q2 := h.valence s.conj Q2

@[simp]
theorem SumRuleAssumptions.chargeConj_valenceTarget [Fintype Flavor] {f : Pdf (Species Flavor)}
    (h : SumRuleAssumptions f) (s : Species Flavor) :
    h.chargeConj.valenceTarget s = h.valenceTarget s.conj :=
  (rfl)

/-- The valence number `∫₀¹ (q_i(x, Q²) - qbar_i(x, Q²)) dx` of flavour `i` in the density `f`:
the net number of quarks of flavour `i` that the density carries at the scale `Q2`. It is the
zeroth power moment, `mellinMoment f 0`, of the quark density minus that of the antiquark
density. -/
def valenceNumber (f : Pdf (Species Flavor)) (i : Flavor) (Q2 : ℝ) : ℝ :=
  mellinMoment f 0 (.quark i) Q2 - mellinMoment f 0 (.antiquark i) Q2

theorem valenceNumber_def (f : Pdf (Species Flavor)) (i : Flavor) (Q2 : ℝ) :
    valenceNumber f i Q2 = mellinMoment f 0 (.quark i) Q2 - mellinMoment f 0 (.antiquark i) Q2 :=
  (rfl)

/-- Charge conjugation negates the valence number of every flavour. -/
@[simp]
theorem valenceNumber_chargeConj (f : Pdf (Species Flavor)) (i : Flavor) (Q2 : ℝ) :
    valenceNumber (chargeConj f) i Q2 = -valenceNumber f i Q2 := by
  simp [valenceNumber_def]

/-- A density invariant under charge conjugation has vanishing valence number in every
flavour. -/
theorem valenceNumber_eq_zero_of_chargeConj_eq {f : Pdf (Species Flavor)}
    (hf : chargeConj f = f) (i : Flavor) (Q2 : ℝ) : valenceNumber f i Q2 = 0 := by
  have h := valenceNumber_chargeConj f i Q2
  rw [hf] at h
  linarith

end PDF

end Parton
end Particles
end EpsilonEridani
