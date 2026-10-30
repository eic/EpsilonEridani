/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Parton.Species

/-!
# The valence content of a hadron multiplet

A multiplet of hadrons is described by `ValenceContent`: the antiparticle involution `conj` on the
hadrons, the valence content `valence h` — the finite set of parton species that are valence
constituents of `h` — and the compatibility of the two, that the valence constituents of the
antiparticle are the antiparticles of the valence constituents. The valence assignment is explicit
data, so whatever is read off it is not a convention.

A flavour for which exactly one of the quark and the antiquark is a valence constituent is a
`IsValenceFlavor`. This holds for each flavour of a flavoured meson and fails for a flavour-neutral
hadron.

The pion triplet is worked out as an instance: `pionContent` is `π⁺ = u dbar`, `π⁻ = d ubar` and
the flavour-neutral `π⁰`.

## Main definitions

* `EpsilonEridani.Particles.Parton.ValenceContent`: a hadron multiplet with its antiparticle map
  and valence content.
* `EpsilonEridani.Particles.Parton.ValenceContent.IsValenceFlavor`: exactly one of the quark and
  the antiquark of a flavour is a valence constituent of a hadron.
* `EpsilonEridani.Particles.Parton.Pion`, `EpsilonEridani.Particles.Parton.PionFlavor` and
  `EpsilonEridani.Particles.Parton.pionContent`: the pion triplet.

## Main statements

* `ValenceContent.image_conj_valence`: conjugation carries the valence content of a hadron to that
  of its antiparticle.
* `ValenceContent.IsValenceFlavor.conj`: a valence flavour of a hadron is a valence flavour of its
  antiparticle.
* `isValenceFlavor_pion_plus` and `not_isValenceFlavor_pion_zero`: every light flavour is a valence
  flavour of the positive pion and none is a valence flavour of the neutral pion.
-/

public section

namespace EpsilonEridani
namespace Particles
namespace Parton

variable {Hadron Flavor : Type}

/-- The discrete data of a multiplet of observed hadrons: the antiparticle map `conj` on the
hadrons and the valence content `valence h`, the finite set of parton species that are valence
constituents of `h`. The two are tied by `mem_valence_conj`: the valence constituents of the
antiparticle are the antiparticles of the valence constituents. -/
structure ValenceContent (Hadron Flavor : Type) where
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

namespace ValenceContent

variable (C : ValenceContent Hadron Flavor)

@[simp]
theorem conj_conj (h : Hadron) : C.conj (C.conj h) = h :=
  C.conj_involutive h

/-- Conjugation carries the valence content of a hadron to that of its antiparticle. -/
theorem image_conj_valence [DecidableEq Flavor] (h : Hadron) :
    (C.valence h).image Species.conj = C.valence (C.conj h) := by
  ext s
  rw [C.mem_valence_conj, Finset.mem_image]
  exact ⟨fun ⟨a, ha, hs⟩ => hs ▸ (Species.conj_conj a).symm ▸ ha,
    fun hs => ⟨_, hs, Species.conj_conj s⟩⟩

/-- The flavour `i` is a *valence flavour* of the hadron `h` when exactly one of the quark and the
antiquark of flavour `i` is a valence constituent of `h`. This holds for each flavour of a
flavoured meson; it fails for a flavour whose quark and antiquark both occur, as in a
flavour-neutral hadron, and for a flavour that does not occur at all. -/
def IsValenceFlavor (h : Hadron) (i : Flavor) : Prop :=
  Xor (Species.quark i ∈ C.valence h) (Species.antiquark i ∈ C.valence h)

variable {C} {h : Hadron} {i : Flavor}

theorem isValenceFlavor_iff : C.IsValenceFlavor h i ↔
    Xor (Species.quark i ∈ C.valence h) (Species.antiquark i ∈ C.valence h) :=
  Iff.rfl

/-- A flavour whose quark, and not whose antiquark, is a valence constituent is a valence
flavour. -/
theorem isValenceFlavor_of_quark_mem (hq : Species.quark i ∈ C.valence h)
    (hq' : Species.antiquark i ∉ C.valence h) : C.IsValenceFlavor h i :=
  Or.inl ⟨hq, hq'⟩

/-- A flavour whose antiquark, and not whose quark, is a valence constituent is a valence
flavour. -/
theorem isValenceFlavor_of_antiquark_mem (hq' : Species.antiquark i ∈ C.valence h)
    (hq : Species.quark i ∉ C.valence h) : C.IsValenceFlavor h i :=
  Or.inr ⟨hq', hq⟩

/-- At a valence flavour, the antiquark is a valence constituent exactly when the quark is
not. -/
theorem IsValenceFlavor.antiquark_mem_iff (hi : C.IsValenceFlavor h i) :
    Species.antiquark i ∈ C.valence h ↔ Species.quark i ∉ C.valence h := by
  rcases hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · exact iff_of_false hq' (not_not_intro hq)
  · exact iff_of_true hq' hq

/-- At a valence flavour, the quark is a valence constituent exactly when the antiquark is
not. -/
theorem IsValenceFlavor.quark_mem_iff (hi : C.IsValenceFlavor h i) :
    Species.quark i ∈ C.valence h ↔ Species.antiquark i ∉ C.valence h :=
  iff_not_comm.1 hi.antiquark_mem_iff

/-- A valence flavour of a hadron is a valence flavour of its antiparticle. -/
theorem IsValenceFlavor.conj (hi : C.IsValenceFlavor h i) :
    C.IsValenceFlavor (C.conj h) i := by
  simp only [IsValenceFlavor, C.mem_valence_conj, Species.conj_quark, Species.conj_antiquark]
  rw [xor_comm]
  exact hi

end ValenceContent

/-! ### The pion triplet -/

/-- The two quark flavours of the pion triplet's valence content. -/
inductive PionFlavor where
  /-- The up flavour. -/
  | up
  /-- The down flavour. -/
  | down
  deriving DecidableEq

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

/-- The isospin reflection is an involution. -/
theorem PionFlavor.swap_involutive : Function.Involutive swap := by
  intro i
  cases i <;> rfl

/-- The pion triplet. -/
inductive Pion where
  /-- The positive pion `u dbar`. -/
  | plus
  /-- The neutral pion. -/
  | zero
  /-- The negative pion `d ubar`. -/
  | minus

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

/-- Taking the antiparticle of a pion twice returns the pion. -/
theorem Pion.conj_involutive : Function.Involutive Pion.conj := by
  intro h
  cases h <;> rfl

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

/-- The pion triplet as a hadron multiplet. -/
def pionContent : ValenceContent Pion PionFlavor where
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
theorem pionContent_conj : pionContent.conj = Pion.conj :=
  (rfl)

@[simp]
theorem pionContent_valence : pionContent.valence = Pion.valence :=
  (rfl)

/-- Both light flavours are valence flavours of the positive pion: the up quark and the down
antiquark are its valence constituents, and the up antiquark and the down quark are not. -/
theorem isValenceFlavor_pion_plus (i : PionFlavor) :
    pionContent.IsValenceFlavor .plus i := by
  cases i
  · exact ValenceContent.isValenceFlavor_of_quark_mem (by simp) (by simp)
  · exact ValenceContent.isValenceFlavor_of_antiquark_mem (by simp) (by simp)

/-- No flavour is a valence flavour of the neutral pion: for each flavour both the quark and the
antiquark are valence constituents, so a flavour-neutral hadron does not distinguish them. -/
theorem not_isValenceFlavor_pion_zero (i : PionFlavor) :
    ¬ pionContent.IsValenceFlavor .zero i := by
  rintro (⟨-, hq'⟩ | ⟨-, hq⟩)
  · exact hq' (by cases i <;> simp)
  · exact hq (by cases i <;> simp)

/-- The valence content of the pion triplet is compatible with the isospin reflection, which acts
on the triplet as the antiparticle map. -/
theorem pion_map_swap_mem_valence_conj_iff (h : Pion) (s : Species PionFlavor) :
    Species.map PionFlavor.swap s ∈ pionContent.valence (Pion.conj h)
      ↔ s ∈ pionContent.valence h := by
  cases h
  all_goals
    simp only [pionContent_valence, Pion.conj, Pion.valence, Finset.mem_insert,
      Finset.mem_singleton, (Species.map_involutive PionFlavor.swap_involutive).eq_iff,
      Species.map_quark, Species.map_antiquark, PionFlavor.swap_up, PionFlavor.swap_down]
    -- `simp only` already closes the two charged cases; the neutral one needs the reordering.
    try tauto

end Parton
end Particles
end EpsilonEridani
