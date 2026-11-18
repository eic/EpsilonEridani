/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.ChargeConjugation

/-!
# The isospin conjugate of a collinear density

Exact isospin symmetry relates the neutron to the proton: the neutron's densities are the
proton's with the up and down flavours exchanged, `q^n_f = q^p_{τ f}`, where
`τ = Equiv.swap u d` is the isospin involution, which fixes every other flavour. This file names
that pullback, `PDF.isospinConj u d f = PDF.comap (Equiv.swap u d) f`, for a density `f` indexed
by quark flavour, with `u` and `d` the up and down flavours; whether the two nucleons are related
this way is the assumption of exact isospin symmetry, and its violation is not modelled here.

The index type `ι` is the quark-flavour index, such as `LightFlavor`, of a density whose component
`f i` is one density per flavour, for instance the quark-plus-antiquark combination `q_i + qbar_i`
that the leading-order structure function `DIS.f2LO` consumes. It is not the parton species
index `Species Flavor`: on a species-indexed density the isospin involution is the species map
induced by `Equiv.swap u d` (quark `i ↦ quark (swap u d i)`, antiquark `i ↦ antiquark
(swap u d i)`, gluon fixed), not a single `Equiv.swap` of two species, which would exchange the
up and down quarks but leave their antiquarks in place. That species-level operation is
`PDF.speciesIsospinConj u d f = PDF.comap (Species.map (Equiv.swap u d)) f`; it commutes with
charge conjugation (`PDF.chargeConj_speciesIsospinConj`), and their composite is the symmetry
that relates the quark and antiquark densities within a charged pion in the isospin limit.

The operation is an involution, and it preserves `PDF.IsPartonDensity`, `PDF.Regularity`,
`PDF.Assumptions`, every moment (relabelled) and every flavour-summed moment; these are instances
of the general results `PDF.Assumptions.comap` and its companions, as for charge conjugation
(`PDF.chargeConj`). For the flavour-indexed `PDF.isospinConj`, unlike charge conjugation, no
`PDF.SumRuleAssumptions` transport is provided: `ι` is a quark-flavour index rather than
`Species Flavor`, and the momentum sum rule holds only summed over all parton species, including
the gluon, so it is not available for such a density. The species-indexed
`PDF.speciesIsospinConj` does transport the sum-rule bundle
(`PDF.SumRuleAssumptions.speciesIsospinConj`), with the target of each species taken from its
isospin conjugate.

## Main definitions

* `EpsilonEridani.Particles.Parton.PDF.isospinConj`: the isospin-conjugate density.
* `EpsilonEridani.Particles.Parton.PDF.speciesIsospinConj`: the isospin-conjugate density over
  the parton species.

## Main statements

* `PDF.isospinConj_apply`: `isospinConj u d f i = f (swap u d i)`.
* `PDF.isospinConj_isospinConj`: isospin conjugation is an involution.
* `PDF.isospinConj_comm`, `PDF.isospinConj_self`: the order of the exchanged flavours does not
  matter, and exchanging a flavour with itself is the identity.
* `PDF.IsPartonDensity.isospinConj`, `PDF.Regularity.isospinConj`, `PDF.Assumptions.isospinConj`:
  it preserves the density assumptions.
* `PDF.mellinMoment_isospinConj`, `PDF.sum_mellinMoment_isospinConj`: it relabels every moment and
  preserves every flavour-summed moment.
* `PDF.chargeConj_speciesIsospinConj`: on species-indexed densities, isospin conjugation commutes
  with charge conjugation.
* `PDF.valenceNumber_speciesIsospinConj`: it relabels the valence numbers.
* `PDF.SumRuleAssumptions.speciesIsospinConj`: it transports the sum-rule bundle.

## References

* F. Halzen and A. D. Martin, *Quarks and Leptons*, Wiley (1984), ch. 9.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace PDF

variable {ι : Type} [DecidableEq ι]

/-- The isospin-conjugate density: the density of flavour `i` is the density of `swap u d i` in
`f`, so the up and down densities are exchanged and every other density is kept. Here `ι` is a
quark-flavour index, not the species index `Species Flavor`; with `f` the proton's per-flavour
densities and `u`, `d` the up and down flavours, this is the neutron's density under exact isospin
symmetry. -/
def isospinConj (u d : ι) (f : Pdf ι) : Pdf ι :=
  comap (Equiv.swap u d) f

theorem isospinConj_eq_comap (u d : ι) (f : Pdf ι) :
    isospinConj u d f = comap (Equiv.swap u d) f :=
  (rfl)

@[simp]
theorem isospinConj_apply (u d : ι) (f : Pdf ι) (i : ι) (x Q2 : ℝ) :
    isospinConj u d f i x Q2 = f (Equiv.swap u d i) x Q2 := by
  rw [isospinConj_eq_comap, comap_apply]

/-- The order of the two exchanged flavours does not matter. -/
theorem isospinConj_comm (u d : ι) (f : Pdf ι) : isospinConj u d f = isospinConj d u f := by
  rw [isospinConj_eq_comap, isospinConj_eq_comap, Equiv.swap_comm]

/-- Exchanging a flavour with itself is the identity. -/
@[simp]
theorem isospinConj_self (u : ι) (f : Pdf ι) : isospinConj u u f = f := by
  rw [isospinConj_eq_comap, Equiv.swap_self, Equiv.coe_refl, comap_id]

@[simp]
theorem isospinConj_isospinConj (u d : ι) (f : Pdf ι) :
    isospinConj u d (isospinConj u d f) = f := by
  rw [isospinConj_eq_comap, isospinConj_eq_comap, comap_comap,
    Function.Involutive.comp_self (Equiv.swap_apply_self u d), comap_id]

theorem isospinConj_involutive (u d : ι) :
    Function.Involutive (isospinConj u d : Pdf ι → Pdf ι) :=
  isospinConj_isospinConj u d

@[simp]
theorem mellinMoment_isospinConj (u d : ι) (f : Pdf ι) (n : ℕ) (i : ι) (Q2 : ℝ) :
    mellinMoment (isospinConj u d f) n i Q2 = mellinMoment f n (Equiv.swap u d i) Q2 := by
  rw [isospinConj_eq_comap, mellinMoment_comap]

/-- Isospin conjugation preserves every moment summed over all flavours; for `n = 1` and the
quark-plus-antiquark densities this is the statement that the conjugate carries the same total
quark momentum fraction. -/
theorem sum_mellinMoment_isospinConj [Fintype ι] (u d : ι) (f : Pdf ι) (n : ℕ) (Q2 : ℝ) :
    ∑ i, mellinMoment (isospinConj u d f) n i Q2 = ∑ i, mellinMoment f n i Q2 := by
  rw [isospinConj_eq_comap]
  exact sum_mellinMoment_comap (Equiv.swap u d).bijective f n Q2

/-- Isospin conjugation preserves the physical half of the density assumptions. -/
theorem IsPartonDensity.isospinConj {f : Pdf ι} (h : IsPartonDensity f) (u d : ι) :
    IsPartonDensity (isospinConj u d f) := by
  rw [isospinConj_eq_comap]
  exact h.comap _

/-- Isospin conjugation preserves the analytic half of the density assumptions. -/
theorem Regularity.isospinConj {f : Pdf ι} (h : Regularity f) (u d : ι) :
    Regularity (isospinConj u d f) := by
  rw [isospinConj_eq_comap]
  exact h.comap _

/-- Isospin conjugation preserves the density assumptions. -/
theorem Assumptions.isospinConj {f : Pdf ι} (h : Assumptions f) (u d : ι) :
    Assumptions (isospinConj u d f) := by
  rw [isospinConj_eq_comap]
  exact h.comap _

/-! ### Isospin conjugation over the parton species -/

section Species

variable {Flavor : Type} [DecidableEq Flavor]

/-- The isospin-conjugate density over the parton species: the density of species `s` is the
density, in `f`, of `s` with the up and down flavours exchanged, `s.map (Equiv.swap u d)`, so the
up and down quark densities are exchanged, so are the up and down antiquark densities, and every
other species is kept. With `f` the densities of a hadron, this is the densities of its isospin
partner under exact isospin symmetry. -/
def speciesIsospinConj (u d : Flavor) (f : Pdf (Species Flavor)) : Pdf (Species Flavor) :=
  comap (Species.map (Equiv.swap u d)) f

theorem speciesIsospinConj_eq_comap (u d : Flavor) (f : Pdf (Species Flavor)) :
    speciesIsospinConj u d f = comap (Species.map (Equiv.swap u d)) f :=
  (rfl)

@[simp]
theorem speciesIsospinConj_apply (u d : Flavor) (f : Pdf (Species Flavor)) (s : Species Flavor)
    (x Q2 : ℝ) : speciesIsospinConj u d f s x Q2 = f (s.map (Equiv.swap u d)) x Q2 := by
  rw [speciesIsospinConj_eq_comap, comap_apply]

theorem speciesIsospinConj_comm (u d : Flavor) (f : Pdf (Species Flavor)) :
    speciesIsospinConj u d f = speciesIsospinConj d u f := by
  rw [speciesIsospinConj_eq_comap, speciesIsospinConj_eq_comap, Equiv.swap_comm]

/-- Exchanging a flavour with itself is the identity. -/
@[simp]
theorem speciesIsospinConj_self (u : Flavor) (f : Pdf (Species Flavor)) :
    speciesIsospinConj u u f = f := by
  ext s x Q2
  rw [speciesIsospinConj_apply, Equiv.swap_self, Equiv.coe_refl, Species.map_id]

@[simp]
theorem speciesIsospinConj_speciesIsospinConj (u d : Flavor) (f : Pdf (Species Flavor)) :
    speciesIsospinConj u d (speciesIsospinConj u d f) = f := by
  rw [speciesIsospinConj_eq_comap, speciesIsospinConj_eq_comap, comap_comap,
    Function.Involutive.comp_self (Species.map_involutive (Equiv.swap_apply_self u d)), comap_id]

theorem speciesIsospinConj_involutive (u d : Flavor) :
    Function.Involutive (speciesIsospinConj u d : Pdf (Species Flavor) → Pdf (Species Flavor)) :=
  speciesIsospinConj_speciesIsospinConj u d

/-- **Isospin conjugation commutes with charge conjugation**: exchanging the up and down flavours
and exchanging quarks with antiquarks are independent relabellings of the species. -/
theorem chargeConj_speciesIsospinConj (u d : Flavor) (f : Pdf (Species Flavor)) :
    chargeConj (speciesIsospinConj u d f) = speciesIsospinConj u d (chargeConj f) := by
  ext s x Q2
  rw [chargeConj_apply, speciesIsospinConj_apply, speciesIsospinConj_apply, chargeConj_apply,
    Species.conj_map]

/-- Isospin conjugation commutes with a species-wise rescaling: the conjugate of a rescaled
density is the conjugate density rescaled by the conjugated weight. -/
@[simp]
theorem speciesIsospinConj_weight (u d : Flavor) (w : Species Flavor → ℝ)
    (f : Pdf (Species Flavor)) :
    speciesIsospinConj u d (weight w f)
      = weight (w ∘ Species.map (Equiv.swap u d)) (speciesIsospinConj u d f) := by
  rw [speciesIsospinConj_eq_comap, comap_weight, speciesIsospinConj_eq_comap]

@[simp]
theorem mellinMoment_speciesIsospinConj (u d : Flavor) (f : Pdf (Species Flavor)) (n : ℕ)
    (s : Species Flavor) (Q2 : ℝ) :
    mellinMoment (speciesIsospinConj u d f) n s Q2
      = mellinMoment f n (s.map (Equiv.swap u d)) Q2 := by
  rw [speciesIsospinConj_eq_comap, mellinMoment_comap]

/-- Isospin conjugation preserves every moment summed over all species; for `n = 1` this is the
statement that the conjugate carries the same total momentum. -/
theorem sum_mellinMoment_speciesIsospinConj [Fintype Flavor] (u d : Flavor)
    (f : Pdf (Species Flavor)) (n : ℕ) (Q2 : ℝ) :
    ∑ s, mellinMoment (speciesIsospinConj u d f) n s Q2 = ∑ s, mellinMoment f n s Q2 := by
  rw [speciesIsospinConj_eq_comap]
  exact sum_mellinMoment_comap (Species.map_involutive (Equiv.swap_apply_self u d)).bijective f n
    Q2

/-- Isospin conjugation relabels the valence numbers: the valence number of flavour `i` in the
conjugate is that of `swap u d i` in the density. -/
@[simp]
theorem valenceNumber_speciesIsospinConj (u d : Flavor) (f : Pdf (Species Flavor)) (i : Flavor)
    (Q2 : ℝ) :
    valenceNumber (speciesIsospinConj u d f) i Q2 = valenceNumber f (Equiv.swap u d i) Q2 := by
  rw [valenceNumber_def, valenceNumber_def, mellinMoment_speciesIsospinConj,
    mellinMoment_speciesIsospinConj, Species.map_quark, Species.map_antiquark]

/-- Isospin conjugation over the species preserves the physical half of the density
assumptions. -/
theorem IsPartonDensity.speciesIsospinConj {f : Pdf (Species Flavor)} (h : IsPartonDensity f)
    (u d : Flavor) : IsPartonDensity (speciesIsospinConj u d f) := by
  rw [speciesIsospinConj_eq_comap]
  exact h.comap _

/-- Isospin conjugation over the species preserves the analytic half of the density
assumptions. -/
theorem Regularity.speciesIsospinConj {f : Pdf (Species Flavor)} (h : Regularity f)
    (u d : Flavor) : Regularity (speciesIsospinConj u d f) := by
  rw [speciesIsospinConj_eq_comap]
  exact h.comap _

/-- Isospin conjugation over the species preserves the density assumptions. -/
theorem Assumptions.speciesIsospinConj {f : Pdf (Species Flavor)} (h : Assumptions f)
    (u d : Flavor) : Assumptions (speciesIsospinConj u d f) := by
  rw [speciesIsospinConj_eq_comap]
  exact h.comap _

/-- Isospin conjugation over the species preserves the sum-rule bundle, with the target value of
each species taken from its isospin conjugate. -/
def SumRuleAssumptions.speciesIsospinConj [Fintype Flavor] {f : Pdf (Species Flavor)}
    (h : SumRuleAssumptions f) (u d : Flavor) : SumRuleAssumptions (speciesIsospinConj u d f) :=
  h.comap (Species.map_involutive (Equiv.swap_apply_self u d)).bijective

@[simp]
theorem SumRuleAssumptions.speciesIsospinConj_valenceTarget [Fintype Flavor]
    {f : Pdf (Species Flavor)} (h : SumRuleAssumptions f) (u d : Flavor) (s : Species Flavor) :
    (h.speciesIsospinConj u d).valenceTarget s = h.valenceTarget (s.map (Equiv.swap u d)) :=
  (rfl)

end Species

end PDF

end Parton
end Particles
end EpsilonEridani
