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
up and down quarks but leave their antiquarks in place. The species-level exchange of any two
flavours `i` and `j` is `PDF.speciesSwapFlavor i j f = PDF.comap (Species.map (Equiv.swap i j)) f`;
with `i`, `j` the up and down flavours it is isospin conjugation over the species. It commutes
with charge conjugation (`PDF.chargeConj_speciesSwapFlavor`), and at up and down their composite
is the symmetry that relates the quark and antiquark densities within a charged pion in the
isospin limit.

The operation is an involution, and it preserves `PDF.IsPartonDensity`, `PDF.Regularity`,
`PDF.Assumptions`, every moment (relabelled) and every flavour-summed moment; these are instances
of the general results `PDF.Assumptions.comap` and its companions, as for charge conjugation
(`PDF.chargeConj`). For the flavour-indexed `PDF.isospinConj`, unlike charge conjugation, no
`PDF.SumRuleAssumptions` transport is provided: `ι` is a quark-flavour index rather than
`Species Flavor`, and the momentum sum rule holds only summed over all parton species, including
the gluon, so it is not available for such a density. The species-indexed
`PDF.speciesSwapFlavor` does transport the sum-rule bundle
(`PDF.SumRuleAssumptions.speciesSwapFlavor`), with the target of each species taken from the
species with the two flavours exchanged.

## Main definitions

* `EpsilonEridani.Particles.Parton.PDF.isospinConj`: the isospin-conjugate density.
* `EpsilonEridani.Particles.Parton.PDF.speciesSwapFlavor`: the density over the parton species
  with two flavours exchanged; at up and down, the isospin-conjugate density.

## Main statements

* `PDF.isospinConj_apply`: `isospinConj u d f i = f (swap u d i)`.
* `PDF.isospinConj_isospinConj`: isospin conjugation is an involution.
* `PDF.isospinConj_comm`, `PDF.isospinConj_self`: the order of the exchanged flavours does not
  matter, and exchanging a flavour with itself is the identity.
* `PDF.IsPartonDensity.isospinConj`, `PDF.Regularity.isospinConj`, `PDF.Assumptions.isospinConj`:
  it preserves the density assumptions.
* `PDF.mellinMoment_isospinConj`, `PDF.sum_mellinMoment_isospinConj`: it relabels every moment and
  preserves every flavour-summed moment.
* `PDF.chargeConj_speciesSwapFlavor`: on species-indexed densities, exchanging two flavours
  commutes with charge conjugation.
* `PDF.valenceNumber_speciesSwapFlavor`: it relabels the valence numbers.
* `PDF.SumRuleAssumptions.speciesSwapFlavor`: it transports the sum-rule bundle.

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

/-! ### Exchanging two flavours over the parton species -/

section Species

variable {Flavor : Type} [DecidableEq Flavor]

/-- The density over the parton species with the flavours `i` and `j` exchanged: the density of
species `s` is the density, in `f`, of `s` with the two flavours exchanged,
`s.map (Equiv.swap i j)`, so the `i` and `j` quark densities are exchanged, so are the `i` and
`j` antiquark densities, and every other species is kept. With `f` the densities of a hadron and
`i`, `j` the up and down flavours, this is the densities of its isospin partner under exact
isospin symmetry. -/
def speciesSwapFlavor (i j : Flavor) (f : Pdf (Species Flavor)) : Pdf (Species Flavor) :=
  comap (Species.map (Equiv.swap i j)) f

theorem speciesSwapFlavor_eq_comap (i j : Flavor) (f : Pdf (Species Flavor)) :
    speciesSwapFlavor i j f = comap (Species.map (Equiv.swap i j)) f :=
  (rfl)

@[simp]
theorem speciesSwapFlavor_apply (i j : Flavor) (f : Pdf (Species Flavor)) (s : Species Flavor)
    (x Q2 : ℝ) : speciesSwapFlavor i j f s x Q2 = f (s.map (Equiv.swap i j)) x Q2 := by
  rw [speciesSwapFlavor_eq_comap, comap_apply]

theorem speciesSwapFlavor_comm (i j : Flavor) (f : Pdf (Species Flavor)) :
    speciesSwapFlavor i j f = speciesSwapFlavor j i f := by
  rw [speciesSwapFlavor_eq_comap, speciesSwapFlavor_eq_comap, Equiv.swap_comm]

/-- Exchanging a flavour with itself is the identity. -/
@[simp]
theorem speciesSwapFlavor_self (i : Flavor) (f : Pdf (Species Flavor)) :
    speciesSwapFlavor i i f = f := by
  ext s x Q2
  rw [speciesSwapFlavor_apply, Equiv.swap_self, Equiv.coe_refl, Species.map_id]

@[simp]
theorem speciesSwapFlavor_speciesSwapFlavor (i j : Flavor) (f : Pdf (Species Flavor)) :
    speciesSwapFlavor i j (speciesSwapFlavor i j f) = f := by
  rw [speciesSwapFlavor_eq_comap, speciesSwapFlavor_eq_comap, comap_comap,
    Function.Involutive.comp_self (Species.map_involutive (Equiv.swap_apply_self i j)), comap_id]

theorem speciesSwapFlavor_involutive (i j : Flavor) :
    Function.Involutive (speciesSwapFlavor i j : Pdf (Species Flavor) → Pdf (Species Flavor)) :=
  speciesSwapFlavor_speciesSwapFlavor i j

/-- **Exchanging two flavours commutes with charge conjugation**: exchanging the flavours `i` and
`j` and exchanging quarks with antiquarks are independent relabellings of the species. -/
theorem chargeConj_speciesSwapFlavor (i j : Flavor) (f : Pdf (Species Flavor)) :
    chargeConj (speciesSwapFlavor i j f) = speciesSwapFlavor i j (chargeConj f) := by
  ext s x Q2
  rw [chargeConj_apply, speciesSwapFlavor_apply, speciesSwapFlavor_apply, chargeConj_apply,
    Species.conj_map]

/-- Exchanging two flavours commutes with a species-wise rescaling: the exchange of a rescaled
density is the exchanged density rescaled by the exchanged weight. -/
@[simp]
theorem speciesSwapFlavor_weight (i j : Flavor) (w : Species Flavor → ℝ)
    (f : Pdf (Species Flavor)) :
    speciesSwapFlavor i j (weight w f)
      = weight (w ∘ Species.map (Equiv.swap i j)) (speciesSwapFlavor i j f) := by
  rw [speciesSwapFlavor_eq_comap, comap_weight, speciesSwapFlavor_eq_comap]

@[simp]
theorem mellinMoment_speciesSwapFlavor (i j : Flavor) (f : Pdf (Species Flavor)) (n : ℕ)
    (s : Species Flavor) (Q2 : ℝ) :
    mellinMoment (speciesSwapFlavor i j f) n s Q2
      = mellinMoment f n (s.map (Equiv.swap i j)) Q2 := by
  rw [speciesSwapFlavor_eq_comap, mellinMoment_comap]

/-- Exchanging two flavours preserves every moment summed over all species; for `n = 1` this is
the statement that the exchanged density carries the same total momentum. -/
theorem sum_mellinMoment_speciesSwapFlavor [Fintype Flavor] (i j : Flavor)
    (f : Pdf (Species Flavor)) (n : ℕ) (Q2 : ℝ) :
    ∑ s, mellinMoment (speciesSwapFlavor i j f) n s Q2 = ∑ s, mellinMoment f n s Q2 := by
  rw [speciesSwapFlavor_eq_comap]
  exact sum_mellinMoment_comap (Species.map_involutive (Equiv.swap_apply_self i j)).bijective f n
    Q2

/-- Exchanging two flavours relabels the valence numbers: the valence number of flavour `k` in the
exchanged density is that of `swap i j k` in the density. -/
@[simp]
theorem valenceNumber_speciesSwapFlavor (i j : Flavor) (f : Pdf (Species Flavor)) (k : Flavor)
    (Q2 : ℝ) :
    valenceNumber (speciesSwapFlavor i j f) k Q2 = valenceNumber f (Equiv.swap i j k) Q2 := by
  rw [valenceNumber_def, valenceNumber_def, mellinMoment_speciesSwapFlavor,
    mellinMoment_speciesSwapFlavor, Species.map_quark, Species.map_antiquark]

/-- Exchanging two flavours preserves the physical half of the density assumptions. -/
theorem IsPartonDensity.speciesSwapFlavor {f : Pdf (Species Flavor)} (h : IsPartonDensity f)
    (i j : Flavor) : IsPartonDensity (speciesSwapFlavor i j f) := by
  rw [speciesSwapFlavor_eq_comap]
  exact h.comap _

/-- Exchanging two flavours preserves the analytic half of the density assumptions. -/
theorem Regularity.speciesSwapFlavor {f : Pdf (Species Flavor)} (h : Regularity f)
    (i j : Flavor) : Regularity (speciesSwapFlavor i j f) := by
  rw [speciesSwapFlavor_eq_comap]
  exact h.comap _

/-- Exchanging two flavours preserves the density assumptions. -/
theorem Assumptions.speciesSwapFlavor {f : Pdf (Species Flavor)} (h : Assumptions f)
    (i j : Flavor) : Assumptions (speciesSwapFlavor i j f) := by
  rw [speciesSwapFlavor_eq_comap]
  exact h.comap _

/-- Exchanging two flavours preserves the sum-rule bundle, with the target value of each species
taken from the species with the two flavours exchanged. -/
def SumRuleAssumptions.speciesSwapFlavor [Fintype Flavor] {f : Pdf (Species Flavor)}
    (h : SumRuleAssumptions f) (i j : Flavor) : SumRuleAssumptions (speciesSwapFlavor i j f) :=
  h.comap (Species.map_involutive (Equiv.swap_apply_self i j)).bijective

@[simp]
theorem SumRuleAssumptions.speciesSwapFlavor_valenceTarget [Fintype Flavor]
    {f : Pdf (Species Flavor)} (h : SumRuleAssumptions f) (i j : Flavor) (s : Species Flavor) :
    (h.speciesSwapFlavor i j).valenceTarget s = h.valenceTarget (s.map (Equiv.swap i j)) :=
  (rfl)

end Species

end PDF

end Parton
end Particles
end EpsilonEridani
