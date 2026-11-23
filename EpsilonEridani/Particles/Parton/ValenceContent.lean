/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Meson.Basic
public import EpsilonEridani.Particles.Parton.Species

/-!
# The valence content of a hadron multiplet

The valence content of a family of hadrons is a map `valence` sending a hadron `h` to the finite
set of parton species that are valence constituents of `h`. The valence assignment is explicit
data, so whatever is read off it is not a convention.

A flavour for which exactly one of the quark and the antiquark is a valence constituent is a
`IsValenceFlavor`. This holds for each flavour of a flavoured meson and fails for a flavour-neutral
hadron.

A valence assignment is a `ValenceInvariant` of a map `τ` of the hadrons and a map `σ` of the
species when `σ s` is a valence constituent of `τ h` exactly when `s` is one of `h`. This is the
compatibility of the valence content with a symmetry, such as charge conjugation or isospin.

A multiplet of hadrons closed under taking the antiparticle is a `HadronMultiplet`: the
antiparticle involution `conj` on the hadrons, the valence content, and the compatibility of the
two, that the valence constituents of the antiparticle are the antiparticles of the valence
constituents.

The pion triplet is worked out as an instance: `pionMultiplet` is `π⁺ = u dbar`, `π⁻ = d ubar` and
the flavour-neutral `π⁰`.

The pion triplet is indexed by its own two-flavour type `PionFlavor` rather than by the three light
flavours `Meson.LightFlavor`, because the pions form an isospin multiplet of the up and the down
flavour: the isospin reflection `PionFlavor.swap` is an involution exchanging the two, and every
flavour of `PionFlavor` is a valence flavour of each charged pion, which fails for the strange
flavour of `Meson.LightFlavor`. The hadron type `Pion` labels the three pions, including the
neutral pion, which is not a `Meson.PseudoscalarMeson` with a single valence quark and antiquark.
The two encodings are connected by `PionFlavor.toLightFlavor`, under which the valence content of
the charged pions is that of `Meson.piPlus` and `Meson.piMinus`.

## Main definitions

* `EpsilonEridani.Particles.Parton.IsValenceFlavor`: exactly one of the quark and the antiquark of a
  flavour is a valence constituent of a hadron.
* `EpsilonEridani.Particles.Parton.ValenceInvariant`: the valence content is compatible with a map
  of the hadrons and a map of the species.
* `EpsilonEridani.Particles.Parton.HadronMultiplet`: a hadron multiplet with its antiparticle map
  and valence content.
* `EpsilonEridani.Particles.Parton.Pion`, `EpsilonEridani.Particles.Parton.PionFlavor` and
  `EpsilonEridani.Particles.Parton.pionMultiplet`: the pion triplet.
* `EpsilonEridani.Particles.Parton.PionFlavor.toLightFlavor`: the pion flavours as light flavours.

## Main statements

* `IsValenceFlavor.image_conj_inter_valence`: at a valence flavour, conjugation carries the valence
  species of that flavour in a hadron to its non-valence species.
* `ValenceInvariant.image_valence`: a compatible surjective map of the species carries the valence
  content of a hadron to that of its image.
* `HadronMultiplet.valenceInvariant_conj`: the valence content of a multiplet is compatible with
  taking the antiparticle.
* `HadronMultiplet.image_conj_valence`: conjugation carries the valence content of a hadron to that
  of its antiparticle.
* `HadronMultiplet.image_conj_inter_valence` and `HadronMultiplet.image_conj_sdiff_valence`:
  conjugation carries the valence and the non-valence species of a flavour in a hadron to those in
  its antiparticle.
* `IsValenceFlavor.conj`: for a valence content compatible with conjugation, a valence flavour of a
  hadron is a valence flavour of its antiparticle.
* `IsValenceFlavor.inter_valence_conj_eq_sdiff`: at a valence flavour, the valence species of the
  antiparticle are the non-valence species of the hadron.
* `isValenceFlavor_pion_plus`, `isValenceFlavor_pion_minus` and `not_isValenceFlavor_pion_zero`:
  every light flavour is a valence flavour of each charged pion and none is a valence flavour of
  the neutral pion.
* `valenceInvariant_pion_conj` and `valenceInvariant_pion_swap`: the valence content of the pion
  triplet is compatible with charge conjugation and with the isospin reflection.
* `Pion.image_map_valence_plus` and `Pion.image_map_valence_minus`: the valence content of the
  charged pions, read as light flavours, is that of `Meson.piPlus` and `Meson.piMinus`.
-/

public section

namespace EpsilonEridani
namespace Particles
namespace Parton

variable {Hadron Flavor : Type}

/-- The flavour `i` is a *valence flavour* of the hadron `h` for the valence content `valence` when
exactly one of the quark and the antiquark of flavour `i` is a valence constituent of `h`. This
holds for each flavour of a flavoured meson; it fails for a flavour whose quark and antiquark both
occur, as in a flavour-neutral hadron, and for a flavour that does not occur at all. -/
def IsValenceFlavor (valence : Hadron → Finset (Species Flavor)) (h : Hadron) (i : Flavor) :
    Prop :=
  Xor (Species.quark i ∈ valence h) (Species.antiquark i ∈ valence h)

section IsValenceFlavor

variable {valence : Hadron → Finset (Species Flavor)} {h : Hadron} {i : Flavor}

theorem isValenceFlavor_iff : IsValenceFlavor valence h i ↔
    Xor (Species.quark i ∈ valence h) (Species.antiquark i ∈ valence h) :=
  Iff.rfl

/-- A flavour whose quark, and not whose antiquark, is a valence constituent is a valence
flavour. -/
theorem isValenceFlavor_of_quark_mem (hq : Species.quark i ∈ valence h)
    (hq' : Species.antiquark i ∉ valence h) : IsValenceFlavor valence h i :=
  Or.inl ⟨hq, hq'⟩

/-- A flavour whose antiquark, and not whose quark, is a valence constituent is a valence
flavour. -/
theorem isValenceFlavor_of_antiquark_mem (hq' : Species.antiquark i ∈ valence h)
    (hq : Species.quark i ∉ valence h) : IsValenceFlavor valence h i :=
  Or.inr ⟨hq', hq⟩

/-- At a valence flavour, the antiquark is a valence constituent exactly when the quark is
not. -/
theorem IsValenceFlavor.antiquark_mem_iff (hi : IsValenceFlavor valence h i) :
    Species.antiquark i ∈ valence h ↔ Species.quark i ∉ valence h :=
  (xor_iff_not_iff'.1 hi).symm

/-- At a valence flavour, the quark is a valence constituent exactly when the antiquark is
not. -/
theorem IsValenceFlavor.quark_mem_iff (hi : IsValenceFlavor valence h i) :
    Species.quark i ∈ valence h ↔ Species.antiquark i ∉ valence h :=
  xor_iff_iff_not.1 hi

/-- At a valence flavour, conjugation carries the valence species of that flavour in a hadron to
the non-valence species of that flavour in the same hadron. -/
theorem IsValenceFlavor.image_conj_inter_valence [DecidableEq Flavor]
    (hi : IsValenceFlavor valence h i) :
    (Species.flavorPair i ∩ valence h).image Species.conj = Species.flavorPair i \ valence h := by
  ext s
  simp only [Finset.mem_image, Finset.mem_inter, Finset.mem_sdiff, Species.mem_flavorPair]
  rcases hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩ <;> grind [Species.conj_quark, Species.conj_antiquark]

end IsValenceFlavor

/-- The valence content `valence` is *invariant* under a map `τ` of the hadrons and a map `σ` of the
species when `σ s` is a valence constituent of `τ h` exactly when `s` is a valence constituent of
`h`. This is the compatibility of the valence content with a symmetry `(τ, σ)` of the hadrons and
the partons, such as charge conjugation or a relabelling of the quark flavours. -/
def ValenceInvariant (valence : Hadron → Finset (Species Flavor)) (τ : Hadron → Hadron)
    (σ : Species Flavor → Species Flavor) : Prop :=
  ∀ h s, σ s ∈ valence (τ h) ↔ s ∈ valence h

section ValenceInvariant

variable {valence : Hadron → Finset (Species Flavor)} {τ : Hadron → Hadron}
  {σ : Species Flavor → Species Flavor}

theorem valenceInvariant_iff : ValenceInvariant valence τ σ ↔
    ∀ h s, σ s ∈ valence (τ h) ↔ s ∈ valence h :=
  Iff.rfl

theorem ValenceInvariant.mem_iff (hv : ValenceInvariant valence τ σ) (h : Hadron)
    (s : Species Flavor) : σ s ∈ valence (τ h) ↔ s ∈ valence h :=
  hv h s

/-- A compatible surjective map of the species carries the valence content of a hadron to that of
its image. -/
theorem ValenceInvariant.image_valence [DecidableEq Flavor] (hv : ValenceInvariant valence τ σ)
    (hσ : Function.Surjective σ) (h : Hadron) : (valence h).image σ = valence (τ h) := by
  ext s
  obtain ⟨t, rfl⟩ := hσ s
  rw [hv.mem_iff, Finset.mem_image]
  refine ⟨?_, fun ht => ⟨t, ht, rfl⟩⟩
  rintro ⟨a, ha, hat⟩
  rwa [← hv.mem_iff h, ← hat, hv.mem_iff]

end ValenceInvariant

/-- The discrete data of a multiplet of observed hadrons closed under taking the antiparticle: the
antiparticle map `conj` on the hadrons and the valence content `valence h`, the finite set of
parton species that are valence constituents of `h`. The two are tied by `mem_valence_conj`: the
valence constituents of the antiparticle are the antiparticles of the valence constituents. -/
@[ext]
structure HadronMultiplet (Hadron Flavor : Type) where
  /-- The antiparticle of a hadron of the multiplet. -/
  conj : Hadron → Hadron
  /-- Taking the antiparticle twice returns the hadron. -/
  conj_involutive : Function.Involutive conj
  /-- The parton species that are valence constituents of a hadron of the multiplet. -/
  valence : Hadron → Finset (Species Flavor)
  /-- A species is a valence constituent of the antiparticle exactly when its antiparticle is a
  valence constituent of the hadron. -/
  mem_valence_conj (h : Hadron) (s : Species Flavor) :
    s ∈ valence (conj h) ↔ Species.conj s ∈ valence h

namespace HadronMultiplet

variable (C : HadronMultiplet Hadron Flavor)

@[simp]
theorem conj_conj (h : Hadron) : C.conj (C.conj h) = h :=
  C.conj_involutive h

/-- The valence content of a multiplet is compatible with taking the antiparticle of the hadron
and of the parton together. -/
theorem valenceInvariant_conj : ValenceInvariant C.valence C.conj Species.conj := fun h s => by
  rw [C.mem_valence_conj, Species.conj_conj]

/-- Conjugation carries the valence content of a hadron to that of its antiparticle. -/
theorem image_conj_valence [DecidableEq Flavor] (h : Hadron) :
    (C.valence h).image Species.conj = C.valence (C.conj h) :=
  C.valenceInvariant_conj.image_valence Species.conj_involutive.surjective h

/-- Conjugation carries the valence species of a flavour in a hadron to the valence species of
that flavour in its antiparticle. -/
theorem image_conj_inter_valence [DecidableEq Flavor] (h : Hadron) (i : Flavor) :
    (Species.flavorPair i ∩ C.valence h).image Species.conj
      = Species.flavorPair i ∩ C.valence (C.conj h) := by
  rw [Finset.image_inter _ _ Species.conj_involutive.injective, Species.image_conj_flavorPair,
    C.image_conj_valence]

/-- Conjugation carries the non-valence species of a flavour in a hadron to the non-valence
species of that flavour in its antiparticle. -/
theorem image_conj_sdiff_valence [DecidableEq Flavor] (h : Hadron) (i : Flavor) :
    (Species.flavorPair i \ C.valence h).image Species.conj
      = Species.flavorPair i \ C.valence (C.conj h) := by
  rw [Finset.image_sdiff _ _ Species.conj_involutive.injective, Species.image_conj_flavorPair,
    C.image_conj_valence]

end HadronMultiplet

namespace IsValenceFlavor

variable {valence : Hadron → Finset (Species Flavor)} {τ : Hadron → Hadron} {h : Hadron}
  {i : Flavor}

/-- For a valence content compatible with the antiparticle map `τ`, a valence flavour of a hadron
is a valence flavour of its antiparticle. -/
theorem conj (hv : ValenceInvariant valence τ Species.conj) (hi : IsValenceFlavor valence h i) :
    IsValenceFlavor valence (τ h) i := by
  rw [isValenceFlavor_iff, ← hv.mem_iff h, ← hv.mem_iff h, Species.conj_quark,
    Species.conj_antiquark] at hi
  rwa [isValenceFlavor_iff, xor_comm]

variable [DecidableEq Flavor]

/-- For a valence content compatible with the antiparticle map `τ`, at a valence flavour the
valence species of that flavour in the antiparticle are the non-valence species of that flavour in
the hadron. -/
theorem inter_valence_conj_eq_sdiff (hv : ValenceInvariant valence τ Species.conj)
    (hi : IsValenceFlavor valence h i) :
    Species.flavorPair i ∩ valence (τ h) = Species.flavorPair i \ valence h := by
  rw [← hi.image_conj_inter_valence, Finset.image_inter _ _ Species.conj_involutive.injective,
    Species.image_conj_flavorPair, hv.image_valence Species.conj_involutive.surjective]

end IsValenceFlavor

/-! ### The pion triplet -/

/-- The two quark flavours of the pion triplet's valence content. -/
inductive PionFlavor where
  /-- The up flavour. -/
  | up
  /-- The down flavour. -/
  | down
  deriving DecidableEq

instance : Fintype PionFlavor where
  elems := {.up, .down}
  complete i := by cases i <;> simp

/-- The isospin reflection of the light flavours: it exchanges the up and the down flavour. -/
def PionFlavor.swap : PionFlavor → PionFlavor
  | up => down
  | down => up

@[simp]
theorem PionFlavor.swap_up : swap .up = .down :=
  (rfl)

@[simp]
theorem PionFlavor.swap_down : swap .down = .up :=
  (rfl)

@[simp]
theorem PionFlavor.swap_swap (i : PionFlavor) : swap (swap i) = i := by
  cases i <;> rfl

/-- The isospin reflection is an involution. -/
theorem PionFlavor.swap_involutive : Function.Involutive swap :=
  PionFlavor.swap_swap

/-- The pion flavours as light flavours: the up and the down flavour, leaving out the strange
flavour. -/
def PionFlavor.toLightFlavor : PionFlavor → Meson.LightFlavor
  | up => .u
  | down => .d

@[simp]
theorem PionFlavor.toLightFlavor_up : toLightFlavor .up = .u :=
  (rfl)

@[simp]
theorem PionFlavor.toLightFlavor_down : toLightFlavor .down = .d :=
  (rfl)

theorem PionFlavor.toLightFlavor_injective : Function.Injective toLightFlavor := by
  intro i j h
  cases i <;> cases j <;> first | rfl | cases h

/-- The pion triplet. -/
inductive Pion where
  /-- The positive pion `u dbar`. -/
  | plus
  /-- The neutral pion. -/
  | zero
  /-- The negative pion `d ubar`. -/
  | minus
  deriving DecidableEq

instance : Fintype Pion where
  elems := {.plus, .zero, .minus}
  complete h := by cases h <;> simp

/-- The antiparticle of a pion: the charged pions are exchanged and the neutral pion is its own
antiparticle. -/
def Pion.conj : Pion → Pion
  | plus => minus
  | zero => zero
  | minus => plus

@[simp]
theorem Pion.conj_plus : conj .plus = .minus :=
  (rfl)

@[simp]
theorem Pion.conj_zero : conj .zero = .zero :=
  (rfl)

@[simp]
theorem Pion.conj_minus : conj .minus = .plus :=
  (rfl)

@[simp]
theorem Pion.conj_conj (h : Pion) : conj (conj h) = h := by
  cases h <;> rfl

/-- Taking the antiparticle of a pion twice returns the pion. -/
theorem Pion.conj_involutive : Function.Involutive Pion.conj :=
  Pion.conj_conj

/-- The valence content of the pions: `π⁺ = u dbar` and `π⁻ = d ubar`, while the neutral pion, a
superposition of `u ubar` and `d dbar`, has all four light species as valence constituents. -/
def Pion.valence : Pion → Finset (Species PionFlavor)
  | plus => {.quark .up, .antiquark .down}
  | zero => {.quark .up, .antiquark .up, .quark .down, .antiquark .down}
  | minus => {.quark .down, .antiquark .up}

@[simp]
theorem Pion.valence_plus : valence .plus = {.quark .up, .antiquark .down} :=
  (rfl)

@[simp]
theorem Pion.valence_zero :
    valence .zero = {.quark .up, .antiquark .up, .quark .down, .antiquark .down} :=
  (rfl)

@[simp]
theorem Pion.valence_minus : valence .minus = {.quark .down, .antiquark .up} :=
  (rfl)

/-- The valence content of the positive pion, read as light flavours, is the valence quark and the
valence antiquark of `Meson.piPlus`. -/
theorem Pion.image_map_valence_plus :
    (valence .plus).image (Species.map PionFlavor.toLightFlavor)
      = {.quark Meson.piPlus.valenceQuark, .antiquark Meson.piPlus.valenceAntiquark} := by
  simp [Finset.image_insert, Species.map_quark, Species.map_antiquark]

/-- The valence content of the negative pion, read as light flavours, is the valence quark and the
valence antiquark of `Meson.piMinus`. -/
theorem Pion.image_map_valence_minus :
    (valence .minus).image (Species.map PionFlavor.toLightFlavor)
      = {.quark Meson.piMinus.valenceQuark, .antiquark Meson.piMinus.valenceAntiquark} := by
  simp [Finset.image_insert, Species.map_quark, Species.map_antiquark]

/-- The pion triplet as a hadron multiplet. -/
def pionMultiplet : HadronMultiplet Pion PionFlavor where
  conj := Pion.conj
  conj_involutive := Pion.conj_involutive
  valence := Pion.valence
  mem_valence_conj h s := by
    cases h
    all_goals
      simp only [Pion.conj, Pion.valence, Finset.mem_insert, Finset.mem_singleton,
        Species.conj_involutive.eq_iff, Species.conj_quark, Species.conj_antiquark]
      tauto

@[simp]
theorem pionMultiplet_conj : pionMultiplet.conj = Pion.conj :=
  (rfl)

@[simp]
theorem pionMultiplet_valence : pionMultiplet.valence = Pion.valence :=
  (rfl)

/-- Both light flavours are valence flavours of the positive pion: the up quark and the down
antiquark are its valence constituents, and the up antiquark and the down quark are not. -/
theorem isValenceFlavor_pion_plus (i : PionFlavor) : IsValenceFlavor Pion.valence .plus i := by
  cases i
  · exact isValenceFlavor_of_quark_mem (by simp) (by simp)
  · exact isValenceFlavor_of_antiquark_mem (by simp) (by simp)

/-- Both light flavours are valence flavours of the negative pion: the down quark and the up
antiquark are its valence constituents, and the down antiquark and the up quark are not. -/
theorem isValenceFlavor_pion_minus (i : PionFlavor) : IsValenceFlavor Pion.valence .minus i := by
  cases i
  · exact isValenceFlavor_of_antiquark_mem (by simp) (by simp)
  · exact isValenceFlavor_of_quark_mem (by simp) (by simp)

/-- No flavour is a valence flavour of the neutral pion: for each flavour both the quark and the
antiquark are valence constituents, so a flavour-neutral hadron does not distinguish them. -/
theorem not_isValenceFlavor_pion_zero (i : PionFlavor) :
    ¬ IsValenceFlavor Pion.valence .zero i := by
  rintro (⟨-, hq'⟩ | ⟨-, hq⟩)
  · exact hq' (by cases i <;> simp)
  · exact hq (by cases i <;> simp)

/-- The valence content of the pion triplet is compatible with charge conjugation. -/
theorem valenceInvariant_pion_conj : ValenceInvariant Pion.valence Pion.conj Species.conj :=
  pionMultiplet.valenceInvariant_conj

/-- The valence content of the pion triplet is compatible with the isospin reflection, which acts
on the triplet as the antiparticle map. -/
theorem valenceInvariant_pion_swap :
    ValenceInvariant Pion.valence Pion.conj (Species.map PionFlavor.swap) := by
  intro h s
  cases h
  all_goals
    simp only [Pion.conj, Pion.valence, Finset.mem_insert,
      Finset.mem_singleton, (Species.map_involutive PionFlavor.swap_involutive).eq_iff,
      Species.map_quark, Species.map_antiquark, PionFlavor.swap_up, PionFlavor.swap_down]
    -- `simp only` already closes the two charged cases; the neutral one needs the reordering.
    try tauto

end Parton
end Particles
end EpsilonEridani
