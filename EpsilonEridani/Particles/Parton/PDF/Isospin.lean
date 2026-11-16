/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.Basic

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
up and down quarks but leave their antiquarks in place.

The operation is an involution, and it preserves `PDF.IsPartonDensity`, `PDF.Regularity`,
`PDF.Assumptions`, every moment (relabelled) and every flavour-summed moment; these are instances
of the general results `PDF.Assumptions.comap` and its companions, as for charge conjugation
(`PDF.chargeConj`).

## Main definitions

* `EpsilonEridani.Particles.Parton.PDF.isospinConj`: the isospin-conjugate density.

## Main statements

* `PDF.isospinConj_apply`: `isospinConj u d f i = f (swap u d i)`.
* `PDF.isospinConj_isospinConj`: isospin conjugation is an involution.
* `PDF.isospinConj_comm`, `PDF.isospinConj_self`: the order of the exchanged flavours does not
  matter, and exchanging a flavour with itself is the identity.
* `PDF.IsPartonDensity.isospinConj`, `PDF.Regularity.isospinConj`, `PDF.Assumptions.isospinConj`:
  it preserves the density assumptions.
* `PDF.mellinMoment_isospinConj`, `PDF.sum_mellinMoment_isospinConj`: it relabels every moment and
  preserves every flavour-summed moment.

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

end PDF

end Parton
end Particles
end EpsilonEridani
