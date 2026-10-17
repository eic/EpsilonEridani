/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Fragmentation.Basic
public import EpsilonEridani.Particles.Parton.Species

/-!
# Charge conjugation, flavour symmetry, and the favoured and unfavoured combinations

The fragmentation functions of one hadron multiplet are not independent: the discrete symmetries
relate the fragmentation of a parton into a hadron to the fragmentation of another parton into
another hadron of the same multiplet. This file states those relations and uses them to split the
fragmentation functions of a flavour into the two combinations that are quoted in practice.

A multiplet of observed hadrons is described by `ValenceContent`: the antiparticle involution
`conj` on the hadrons, the valence content `valence h` — the finite set of parton species that are
valence constituents of `h` — and the compatibility of the two, that the valence constituents of
the antiparticle are the antiparticles of the valence constituents. The valence assignment is
explicit data, so the favoured and unfavoured combinations below are read off the data and are not
a convention.

Two relations on a family `D` are named. `ChargeConjRelation τ D` says that the fragmentation of
the antiparton of `s` into the antihadron `τ h` is the fragmentation of `s` into `h`, and
`FlavorRelation τ ρ D` says the same for a relabelling `ρ` of the quark flavours together with
the permutation `τ` of the multiplet it induces; isospin is the case where `ρ` exchanges the up
and the down flavour. Neither is a consequence of the definition of a fragmentation function as
an interface, so both are hypotheses of the theorems that use them. Where both hold with the same
permutation of the multiplet, `apply_map_eq_apply_conj` relates the relabelled and the conjugate
parton inside a single hadron; this is what reduces the number of independent light-hadron
fragmentation functions.

For a hadron `h` and a quark flavour `i`, the *favoured* combination collects the fragmentation
into `h` of those species of flavour `i` that are valence constituents of `h`, and the
*unfavoured* combination collects the rest. A flavour for which exactly one of the quark and the
antiquark is a valence constituent is a `IsValenceFlavor`; for such a flavour each combination is
a single fragmentation function, conjugating the parton index exchanges the two, and their
difference is the valence combination `D_{q_i} - D_{q̄_i}`. For a flavour whose quark and antiquark
both occur, as in a flavour-neutral hadron, the two combinations are not separated, and
`not_isValenceFlavor_pion_zero` exhibits that case.

The pion triplet is worked out as an instance: `pionContent` is `π⁺ = u d̄`, `π⁻ = d ū` and the
flavour-neutral `π⁰`, and `favoured_pion_plus_down_eq_favoured_pion_plus_up` is the familiar
`D_u^{π⁺} = D_{d̄}^{π⁺}`, derived from the two relations rather than assumed.

## Main definitions

* `EpsilonEridani.Particles.Fragmentation.ValenceContent`: a hadron multiplet with its
  antiparticle map and valence content.
* `EpsilonEridani.Particles.Fragmentation.ValenceContent.IsValenceFlavor`: exactly one of the
  quark and the antiquark of a flavour is a valence constituent of a hadron.
* `EpsilonEridani.Particles.Fragmentation.ChargeConjRelation` and
  `EpsilonEridani.Particles.Fragmentation.FlavorRelation`: the two symmetry relations.
* `EpsilonEridani.Particles.Fragmentation.partonConj`: conjugating the parton index alone.
* `EpsilonEridani.Particles.Fragmentation.favoured` and
  `EpsilonEridani.Particles.Fragmentation.unfavoured`: the two combinations of a hadron and a
  flavour.
* `EpsilonEridani.Particles.Fragmentation.valenceStepFrag`: an explicit family satisfying the
  relations and separating the two combinations.

## Main statements

* `Fragmentation.apply_map_eq_apply_conj`: charge conjugation and a flavour relation with the same
  permutation of the multiplet identify the relabelled parton with the conjugate parton.
* `Fragmentation.favoured_add_unfavoured`: the two combinations add up to the total fragmentation
  of the flavour.
* `Fragmentation.favoured_partonConj` and `Fragmentation.unfavoured_partonConj`: on a valence
  flavour, conjugating the parton index exchanges the two combinations.
* `Fragmentation.favoured_conj_of_chargeConjRelation`: under the charge-conjugation relation a
  hadron and its antiparticle have the same favoured combination.
* `Fragmentation.favoured_valenceStepFrag_ne_unfavoured`: the two combinations are not identified
  by the relations.
* `Fragmentation.favoured_pion_plus_down_eq_favoured_pion_plus_up`: `D_u^{π⁺} = D_{d̄}^{π⁺}`.

## References

* J. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), §12.5.
* A. Metz and A. Vossen, *Parton fragmentation functions*, Prog. Part. Nucl. Phys. 91 (2016) 136,
  `arXiv:1607.02521`, §2.3.
* D. de Florian, R. Sassot and M. Stratmann, *Global analysis of fragmentation functions for pions
  and kaons and their uncertainties*, Phys. Rev. D 75 (2007) 114010, §II.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Fragmentation

open Parton

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

/-- The flavour `i` is a *valence flavour* of the hadron `h` when exactly one of the quark and the
antiquark of flavour `i` is a valence constituent of `h`. This holds for each flavour of a
flavoured meson; it fails for a flavour whose quark and antiquark both occur, as in a
flavour-neutral hadron, and for a flavour that does not occur at all. -/
def IsValenceFlavor (h : Hadron) (i : Flavor) : Prop :=
  Xor (Species.quark i ∈ C.valence h) (Species.antiquark i ∈ C.valence h)

variable {C} {h : Hadron} {i : Flavor}

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
    Species.quark i ∈ C.valence h ↔ Species.antiquark i ∉ C.valence h := by
  rcases hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · exact iff_of_true hq hq'
  · exact iff_of_false hq (not_not_intro hq')

/-- A valence flavour of a hadron is a valence flavour of its antiparticle. -/
theorem IsValenceFlavor.conj (hi : C.IsValenceFlavor h i) :
    C.IsValenceFlavor (C.conj h) i := by
  simp only [IsValenceFlavor, C.mem_valence_conj, Species.conj_quark, Species.conj_antiquark]
  rw [xor_comm]
  exact hi

end ValenceContent

/-! ### The two symmetry relations -/

variable {D : Frag Hadron (Species Flavor)} {τ : Hadron → Hadron} {ρ : Flavor → Flavor}

/-- A family satisfies the *charge-conjugation relation* for the antiparticle map `τ` when the
fragmentation of the antiparton of `s` into the antihadron `τ h` is the fragmentation of `s` into
`h`, `D_{τ h}^{s̄} = D_h^s`. It is the relation that the action of charge conjugation on the
light-cone correlator imposes on the fragmentation functions of a multiplet. -/
def ChargeConjRelation (τ : Hadron → Hadron) (D : Frag Hadron (Species Flavor)) : Prop :=
  ∀ h s z Q2, D (τ h) (Species.conj s) z Q2 = D h s z Q2

/-- The charge-conjugation relation, read with the conjugation on the right-hand side. -/
theorem ChargeConjRelation.apply_eq (hCC : ChargeConjRelation τ D) (h : Hadron)
    (s : Species Flavor) (z Q2 : ℝ) : D (τ h) s z Q2 = D h (Species.conj s) z Q2 := by
  have := hCC h (Species.conj s) z Q2
  rwa [Species.conj_conj] at this

/-- A family satisfies the *flavour relation* of the symmetry `(τ, ρ)` — a relabelling `ρ` of the
quark flavours together with the permutation `τ` of the multiplet it induces — when
`D_{τ h}^{ρ s} = D_h^s`. Isospin within a light-hadron multiplet is the case where `ρ` exchanges
the up and the down flavour. -/
def FlavorRelation (τ : Hadron → Hadron) (ρ : Flavor → Flavor)
    (D : Frag Hadron (Species Flavor)) : Prop :=
  ∀ h s z Q2, D (τ h) (Species.map ρ s) z Q2 = D h s z Q2

/-- Conjugating the parton index alone: the fragmentation of the antiparton of `s` into the *same*
hadron. This is not a symmetry of a family — it compares two different physical functions — and on
a valence flavour it exchanges the favoured and the unfavoured combination. -/
def partonConj (D : Frag Hadron (Species Flavor)) : Frag Hadron (Species Flavor) :=
  comap id Species.conj D

@[simp]
theorem partonConj_apply (D : Frag Hadron (Species Flavor)) (h : Hadron) (s : Species Flavor)
    (z Q2 : ℝ) : partonConj D h s z Q2 = D h (Species.conj s) z Q2 :=
  (rfl)

@[simp]
theorem partonConj_partonConj (D : Frag Hadron (Species Flavor)) :
    partonConj (partonConj D) = D := by
  funext h s z Q2
  simp

/-- A family that satisfies both the charge-conjugation relation and the flavour relation of a
symmetry acting on the multiplet by the same permutation relates the relabelled parton to the
conjugate parton inside one hadron: `D_h^{ρ s} = D_h^{s̄}`. For the pion triplet, with `ρ` the
exchange of the up and the down flavour, this is what turns the fragmentation of a down quark
into the fragmentation of an up antiquark. -/
theorem apply_map_eq_apply_conj (hτ : Function.Involutive τ) (hCC : ChargeConjRelation τ D)
    (hF : FlavorRelation τ ρ D) (h : Hadron) (s : Species Flavor) (z Q2 : ℝ) :
    D h (Species.map ρ s) z Q2 = D h (Species.conj s) z Q2 := by
  have h1 := hF (τ h) s z Q2
  rw [hτ h] at h1
  rw [h1, hCC.apply_eq]

/-! ### The favoured and the unfavoured combination -/

variable [DecidableEq Flavor]

/-- The *favoured* combination of the hadron `h` and the flavour `i`: the fragmentation into `h`
of those species of flavour `i` that are valence constituents of `h`. -/
def favoured (C : ValenceContent Hadron Flavor) (D : Frag Hadron (Species Flavor)) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : ℝ :=
  ∑ s ∈ Species.flavorPair i ∩ C.valence h, D h s z Q2

/-- The *unfavoured* combination of the hadron `h` and the flavour `i`: the fragmentation into `h`
of those species of flavour `i` that are not valence constituents of `h`. -/
def unfavoured (C : ValenceContent Hadron Flavor) (D : Frag Hadron (Species Flavor)) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : ℝ :=
  ∑ s ∈ Species.flavorPair i \ C.valence h, D h s z Q2

variable (C : ValenceContent Hadron Flavor) (D)

theorem favoured_def (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    favoured C D h i z Q2 = ∑ s ∈ Species.flavorPair i ∩ C.valence h, D h s z Q2 :=
  (rfl)

theorem unfavoured_def (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    unfavoured C D h i z Q2 = ∑ s ∈ Species.flavorPair i \ C.valence h, D h s z Q2 :=
  (rfl)

/-- The two combinations of a flavour add up to the total fragmentation of that flavour, the sum
over its quark and its antiquark. -/
theorem favoured_add_unfavoured (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    favoured C D h i z Q2 + unfavoured C D h i z Q2
      = D h (Species.quark i) z Q2 + D h (Species.antiquark i) z Q2 := by
  rw [favoured_def, unfavoured_def, Finset.sum_inter_add_sum_sdiff, Species.sum_flavorPair]

/-- The favoured combination of a non-negative family is non-negative on the unit interval. -/
theorem favoured_nonneg {D} (hD : Assumptions D) (h : Hadron) (i : Flavor) {z : ℝ} (hz₀ : 0 ≤ z)
    (hz₁ : z ≤ 1) (Q2 : ℝ) : 0 ≤ favoured C D h i z Q2 :=
  Finset.sum_nonneg fun s _ => hD.nonneg h s z Q2 hz₀ hz₁

/-- The unfavoured combination of a non-negative family is non-negative on the unit interval. -/
theorem unfavoured_nonneg {D} (hD : Assumptions D) (h : Hadron) (i : Flavor) {z : ℝ} (hz₀ : 0 ≤ z)
    (hz₁ : z ≤ 1) (Q2 : ℝ) : 0 ≤ unfavoured C D h i z Q2 :=
  Finset.sum_nonneg fun s _ => hD.nonneg h s z Q2 hz₀ hz₁

variable {C D} {h : Hadron} {i : Flavor}

/-- When the quark of a flavour is its hadron's valence constituent and the antiquark is not,
the favoured combination of that flavour is the quark's fragmentation function. -/
theorem favoured_eq_apply_quark (hq : Species.quark i ∈ C.valence h)
    (hq' : Species.antiquark i ∉ C.valence h) (z Q2 : ℝ) :
    favoured C D h i z Q2 = D h (Species.quark i) z Q2 := by
  have hset : Species.flavorPair i ∩ C.valence h = {Species.quark i} := by
    ext s
    simp only [Finset.mem_inter, Species.mem_flavorPair, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hv⟩
      · rfl
      · exact absurd hv hq'
    · rintro rfl
      exact ⟨Or.inl rfl, hq⟩
  rw [favoured_def, hset, Finset.sum_singleton]

/-- When the quark of a flavour is its hadron's valence constituent and the antiquark is not,
the unfavoured combination of that flavour is the antiquark's fragmentation function. -/
theorem unfavoured_eq_apply_antiquark (hq : Species.quark i ∈ C.valence h)
    (hq' : Species.antiquark i ∉ C.valence h) (z Q2 : ℝ) :
    unfavoured C D h i z Q2 = D h (Species.antiquark i) z Q2 := by
  have hset : Species.flavorPair i \ C.valence h = {Species.antiquark i} := by
    ext s
    simp only [Finset.mem_sdiff, Species.mem_flavorPair, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hv⟩
      · exact absurd hq hv
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hq'⟩
  rw [unfavoured_def, hset, Finset.sum_singleton]

/-- When the antiquark of a flavour is its hadron's valence constituent and the quark is not,
the favoured combination of that flavour is the antiquark's fragmentation function. -/
theorem favoured_eq_apply_antiquark (hq' : Species.antiquark i ∈ C.valence h)
    (hq : Species.quark i ∉ C.valence h) (z Q2 : ℝ) :
    favoured C D h i z Q2 = D h (Species.antiquark i) z Q2 := by
  have hset : Species.flavorPair i ∩ C.valence h = {Species.antiquark i} := by
    ext s
    simp only [Finset.mem_inter, Species.mem_flavorPair, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hv⟩
      · exact absurd hv hq
      · rfl
    · rintro rfl
      exact ⟨Or.inr rfl, hq'⟩
  rw [favoured_def, hset, Finset.sum_singleton]

/-- When the antiquark of a flavour is its hadron's valence constituent and the quark is not,
the unfavoured combination of that flavour is the quark's fragmentation function. -/
theorem unfavoured_eq_apply_quark (hq' : Species.antiquark i ∈ C.valence h)
    (hq : Species.quark i ∉ C.valence h) (z Q2 : ℝ) :
    unfavoured C D h i z Q2 = D h (Species.quark i) z Q2 := by
  have hset : Species.flavorPair i \ C.valence h = {Species.quark i} := by
    ext s
    simp only [Finset.mem_sdiff, Species.mem_flavorPair, Finset.mem_singleton]
    constructor
    · rintro ⟨rfl | rfl, hv⟩
      · rfl
      · exact absurd hq' hv
    · rintro rfl
      exact ⟨Or.inl rfl, hq⟩
  rw [unfavoured_def, hset, Finset.sum_singleton]

/-- On a flavour whose valence constituent is the quark, the difference of the two combinations is
the valence combination `D_{q_i} - D_{q̄_i}` of that flavour. -/
theorem favoured_sub_unfavoured_eq (hq : Species.quark i ∈ C.valence h)
    (hq' : Species.antiquark i ∉ C.valence h) (z Q2 : ℝ) :
    favoured C D h i z Q2 - unfavoured C D h i z Q2
      = D h (Species.quark i) z Q2 - D h (Species.antiquark i) z Q2 := by
  rw [favoured_eq_apply_quark hq hq', unfavoured_eq_apply_antiquark hq hq']

/-! ### Reindexing the combinations by conjugation -/

private theorem image_conj_inter_valence (C : ValenceContent Hadron Flavor) (h : Hadron)
    (i : Flavor) : (Species.flavorPair i ∩ C.valence h).image Species.conj
      = Species.flavorPair i ∩ C.valence (C.conj h) := by
  ext s
  simp only [Finset.mem_image, Finset.mem_inter, C.mem_valence_conj]
  refine ⟨fun hs => ?_, fun hs => ⟨Species.conj s,
    ⟨Species.conj_mem_flavorPair.2 hs.1, hs.2⟩, Species.conj_conj s⟩⟩
  obtain ⟨a, ⟨ha, hv⟩, rfl⟩ := hs
  exact ⟨Species.conj_mem_flavorPair.2 ha, by simpa using hv⟩

private theorem image_conj_sdiff_valence (C : ValenceContent Hadron Flavor) (h : Hadron)
    (i : Flavor) : (Species.flavorPair i \ C.valence h).image Species.conj
      = Species.flavorPair i \ C.valence (C.conj h) := by
  ext s
  simp only [Finset.mem_image, Finset.mem_sdiff, C.mem_valence_conj]
  refine ⟨fun hs => ?_, fun hs => ⟨Species.conj s,
    ⟨Species.conj_mem_flavorPair.2 hs.1, hs.2⟩, Species.conj_conj s⟩⟩
  obtain ⟨a, ⟨ha, hv⟩, rfl⟩ := hs
  exact ⟨Species.conj_mem_flavorPair.2 ha, by simpa using hv⟩

private theorem inter_valence_conj_eq_sdiff (hi : C.IsValenceFlavor h i) :
    Species.flavorPair i ∩ C.valence (C.conj h) = Species.flavorPair i \ C.valence h := by
  ext s
  simp only [Finset.mem_inter, Finset.mem_sdiff, C.mem_valence_conj, Species.mem_flavorPair]
  refine and_congr_right fun hs => ?_
  rcases hs with rfl | rfl
  · rw [Species.conj_quark]
    exact hi.antiquark_mem_iff
  · rw [Species.conj_antiquark]
    exact hi.quark_mem_iff

private theorem sdiff_valence_conj_eq_inter (hi : C.IsValenceFlavor h i) :
    Species.flavorPair i \ C.valence (C.conj h) = Species.flavorPair i ∩ C.valence h := by
  have h' := inter_valence_conj_eq_sdiff hi.conj
  rw [C.conj_conj] at h'
  exact h'.symm

/-- On a valence flavour, conjugating the parton index carries the favoured combination to the
unfavoured one. -/
theorem favoured_partonConj (hi : C.IsValenceFlavor h i) (z Q2 : ℝ) :
    favoured C (partonConj D) h i z Q2 = unfavoured C D h i z Q2 := by
  rw [favoured_def, unfavoured_def, ← inter_valence_conj_eq_sdiff hi,
    ← image_conj_inter_valence, Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => partonConj_apply D h s z Q2

/-- On a valence flavour, conjugating the parton index carries the unfavoured combination to the
favoured one. -/
theorem unfavoured_partonConj (hi : C.IsValenceFlavor h i) (z Q2 : ℝ) :
    unfavoured C (partonConj D) h i z Q2 = favoured C D h i z Q2 := by
  rw [favoured_def, unfavoured_def, ← sdiff_valence_conj_eq_inter hi,
    ← image_conj_sdiff_valence, Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => partonConj_apply D h s z Q2

/-- Under the charge-conjugation relation of a multiplet, a hadron and its antiparticle have the
same favoured combination at every flavour. -/
theorem favoured_conj_of_chargeConjRelation (C : ValenceContent Hadron Flavor)
    {D : Frag Hadron (Species Flavor)} (hCC : ChargeConjRelation C.conj D) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : favoured C D (C.conj h) i z Q2 = favoured C D h i z Q2 := by
  rw [favoured_def, favoured_def, ← image_conj_inter_valence,
    Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => hCC h s z Q2

/-- Under the charge-conjugation relation of a multiplet, a hadron and its antiparticle have the
same unfavoured combination at every flavour. -/
theorem unfavoured_conj_of_chargeConjRelation (C : ValenceContent Hadron Flavor)
    {D : Frag Hadron (Species Flavor)} (hCC : ChargeConjRelation C.conj D) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : unfavoured C D (C.conj h) i z Q2 = unfavoured C D h i z Q2 := by
  rw [unfavoured_def, unfavoured_def, ← image_conj_sdiff_valence,
    Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => hCC h s z Q2

/-! ### An explicit family -/

/-- An explicit fragmentation family on a multiplet: it takes the value `2 z` on the valence
species of a hadron and `1 - z` on every other species, cut off outside the unit interval. It
satisfies `Assumptions` and the charge-conjugation relation of the multiplet, and it separates the
favoured from the unfavoured combination of every valence flavour. -/
def valenceStepFrag (C : ValenceContent Hadron Flavor) : Frag Hadron (Species Flavor) :=
  indicatorUnitInterval fun h s z _ => if s ∈ C.valence h then 2 * z else 1 - z

theorem valenceStepFrag_def (C : ValenceContent Hadron Flavor) :
    valenceStepFrag C
      = indicatorUnitInterval fun h s z _ => if s ∈ C.valence h then 2 * z else 1 - z :=
  (rfl)

/-- On the unit interval, `valenceStepFrag` is `2 z` on a valence species. -/
theorem valenceStepFrag_apply_of_mem (C : ValenceContent Hadron Flavor) {h : Hadron}
    {s : Species Flavor} {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) (hs : s ∈ C.valence h) (Q2 : ℝ) :
    valenceStepFrag C h s z Q2 = 2 * z := by
  rw [valenceStepFrag_def, indicatorUnitInterval_of_mem _ hz, ite_eq_left hs]

/-- On the unit interval, `valenceStepFrag` is `1 - z` off the valence species. -/
theorem valenceStepFrag_apply_of_notMem (C : ValenceContent Hadron Flavor) {h : Hadron}
    {s : Species Flavor} {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) (hs : s ∉ C.valence h) (Q2 : ℝ) :
    valenceStepFrag C h s z Q2 = 1 - z := by
  rw [valenceStepFrag_def, indicatorUnitInterval_of_mem _ hz, ite_eq_right hs]

/-- `valenceStepFrag` vanishes outside the unit interval. -/
@[simp]
theorem valenceStepFrag_eq_zero (C : ValenceContent Hadron Flavor) {z : ℝ}
    (hz : z ∉ Set.Icc (0 : ℝ) 1) (h : Hadron) (s : Species Flavor) (Q2 : ℝ) :
    valenceStepFrag C h s z Q2 = 0 := by
  rw [valenceStepFrag_def, indicatorUnitInterval_of_notMem _ hz]

/-- `valenceStepFrag` is a fragmentation family: it is supported in, and non-negative on, the
unit interval. -/
theorem assumptions_valenceStepFrag (C : ValenceContent Hadron Flavor) :
    Assumptions (valenceStepFrag C) := by
  refine assumptions_indicatorUnitInterval fun h s z Q2 hz₀ hz₁ => ?_
  split
  · positivity
  · linarith

/-- `valenceStepFrag` satisfies the charge-conjugation relation of its multiplet, because the
valence content does. -/
theorem chargeConjRelation_valenceStepFrag (C : ValenceContent Hadron Flavor) :
    ChargeConjRelation C.conj (valenceStepFrag C) := by
  intro h s z Q2
  by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
  · by_cases hs : s ∈ C.valence h
    · rw [valenceStepFrag_apply_of_mem C hz hs,
        valenceStepFrag_apply_of_mem C hz (by simpa [C.mem_valence_conj] using hs)]
    · rw [valenceStepFrag_apply_of_notMem C hz hs,
        valenceStepFrag_apply_of_notMem C hz (by simpa [C.mem_valence_conj] using hs)]
  · rw [valenceStepFrag_eq_zero C hz, valenceStepFrag_eq_zero C hz]

/-- The flavour relation of a symmetry `(τ, ρ)` holds for `valenceStepFrag` exactly because the
valence content is compatible with the symmetry. -/
theorem flavorRelation_valenceStepFrag (C : ValenceContent Hadron Flavor)
    (hv : ∀ h s, Species.map ρ s ∈ C.valence (τ h) ↔ s ∈ C.valence h) :
    FlavorRelation τ ρ (valenceStepFrag C) := by
  intro h s z Q2
  by_cases hz : z ∈ Set.Icc (0 : ℝ) 1
  · by_cases hs : s ∈ C.valence h
    · rw [valenceStepFrag_apply_of_mem C hz hs,
        valenceStepFrag_apply_of_mem C hz ((hv h s).2 hs)]
    · rw [valenceStepFrag_apply_of_notMem C hz hs,
        valenceStepFrag_apply_of_notMem C hz (fun hc => hs ((hv h s).1 hc))]
  · rw [valenceStepFrag_eq_zero C hz, valenceStepFrag_eq_zero C hz]

/-- On a valence flavour the favoured combination of `valenceStepFrag` is `2 z`. -/
theorem favoured_valenceStepFrag (hi : C.IsValenceFlavor h i) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (Q2 : ℝ) :
    favoured C (valenceStepFrag C) h i z Q2 = 2 * z := by
  rcases hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · rw [favoured_eq_apply_quark hq hq', valenceStepFrag_apply_of_mem C hz hq]
  · rw [favoured_eq_apply_antiquark hq' hq, valenceStepFrag_apply_of_mem C hz hq']

/-- On a valence flavour the unfavoured combination of `valenceStepFrag` is `1 - z`. -/
theorem unfavoured_valenceStepFrag (hi : C.IsValenceFlavor h i) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (Q2 : ℝ) :
    unfavoured C (valenceStepFrag C) h i z Q2 = 1 - z := by
  rcases hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · rw [unfavoured_eq_apply_antiquark hq hq', valenceStepFrag_apply_of_notMem C hz hq']
  · rw [unfavoured_eq_apply_quark hq' hq, valenceStepFrag_apply_of_notMem C hz hq]

/-- The favoured and the unfavoured combination of a valence flavour are different functions, and
the charge-conjugation relation does not identify them: `valenceStepFrag` satisfies that relation
and gives `1` for the favoured and `1/2` for the unfavoured combination at `z = 1/2`. -/
theorem favoured_valenceStepFrag_ne_unfavoured (hi : C.IsValenceFlavor h i) (Q2 : ℝ) :
    favoured C (valenceStepFrag C) h i (1 / 2) Q2
      ≠ unfavoured C (valenceStepFrag C) h i (1 / 2) Q2 := by
  rw [favoured_valenceStepFrag hi (by norm_num), unfavoured_valenceStepFrag hi (by norm_num)]
  norm_num

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
  /-- The positive pion `u d̄`. -/
  | plus
  /-- The neutral pion. -/
  | zero
  /-- The negative pion `d ū`. -/
  | minus

/-- The antiparticle of a pion: the charged pions are exchanged and the neutral pion is its own
antiparticle. -/
def Pion.conj : Pion → Pion
  | plus => minus
  | zero => zero
  | minus => plus

/-- Taking the antiparticle of a pion twice returns the pion. -/
theorem Pion.conj_involutive : Function.Involutive Pion.conj := by
  intro h
  cases h <;> rfl

/-- The valence content of the pions: `π⁺ = u d̄` and `π⁻ = d ū`, while the neutral pion, a
superposition of `u ū` and `d d̄`, has all four light species as valence constituents. -/
def Pion.valence : Pion → Finset (Species PionFlavor)
  | plus => {.quark .up, .antiquark .down}
  | zero => {.quark .up, .antiquark .up, .quark .down, .antiquark .down}
  | minus => {.quark .down, .antiquark .up}

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
  · exact ValenceContent.isValenceFlavor_of_quark_mem (by simp [Pion.valence])
      (by simp [Pion.valence])
  · exact ValenceContent.isValenceFlavor_of_antiquark_mem (by simp [Pion.valence])
      (by simp [Pion.valence])

/-- No flavour is a valence flavour of the neutral pion: for each flavour both the quark and the
antiquark are valence constituents, so the favoured and the unfavoured combination are not
separated. -/
theorem not_isValenceFlavor_pion_zero (i : PionFlavor) :
    ¬ pionContent.IsValenceFlavor .zero i := by
  rintro (⟨-, hq'⟩ | ⟨-, hq⟩)
  · exact hq' (by cases i <;> simp [Pion.valence])
  · exact hq (by cases i <;> simp [Pion.valence])

/-- The favoured combination of the positive pion at the up flavour is the fragmentation of the
up quark. -/
theorem favoured_pion_plus_up (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    favoured pionContent D .plus .up z Q2 = D .plus (.quark .up) z Q2 :=
  favoured_eq_apply_quark (by simp [Pion.valence]) (by simp [Pion.valence]) z Q2

/-- The favoured combination of the positive pion at the down flavour is the fragmentation of
the down antiquark. -/
theorem favoured_pion_plus_down (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    favoured pionContent D .plus .down z Q2 = D .plus (.antiquark .down) z Q2 :=
  favoured_eq_apply_antiquark (by simp [Pion.valence]) (by simp [Pion.valence]) z Q2

/-- The unfavoured combination of the positive pion at the up flavour is the fragmentation of
the up antiquark. -/
theorem unfavoured_pion_plus_up (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    unfavoured pionContent D .plus .up z Q2 = D .plus (.antiquark .up) z Q2 :=
  unfavoured_eq_apply_antiquark (by simp [Pion.valence]) (by simp [Pion.valence]) z Q2

/-- The unfavoured combination of the positive pion at the down flavour is the fragmentation of
the down quark. -/
theorem unfavoured_pion_plus_down (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    unfavoured pionContent D .plus .down z Q2 = D .plus (.quark .down) z Q2 :=
  unfavoured_eq_apply_quark (by simp [Pion.valence]) (by simp [Pion.valence]) z Q2

/-- The valence content of the pion triplet is compatible with the isospin reflection, which acts
on the triplet as the antiparticle map. -/
theorem pion_map_swap_mem_valence_conj (h : Pion) (s : Species PionFlavor) :
    Species.map PionFlavor.swap s ∈ pionContent.valence (Pion.conj h)
      ↔ s ∈ pionContent.valence h := by
  cases h
  all_goals
    simp only [pionContent_valence, Pion.conj, Pion.valence, Finset.mem_insert,
      Finset.mem_singleton, (Species.map_involutive PionFlavor.swap_involutive).eq_iff,
      Species.map_quark, Species.map_antiquark, PionFlavor.swap_up, PionFlavor.swap_down]
    -- `simp only` already closes the two charged cases; the neutral one needs the reordering.
    try tauto

/-- The two favoured combinations of the positive pion agree: `D_u^{π⁺} = D_{d̄}^{π⁺}`. This is the
relation that reduces the independent pion fragmentation functions to one favoured and one
unfavoured function, and it is a consequence of charge conjugation together with isospin, not a
separate assumption. -/
theorem favoured_pion_plus_down_eq_favoured_pion_plus_up
    {D : Frag Pion (Species PionFlavor)} (hCC : ChargeConjRelation Pion.conj D)
    (hI : FlavorRelation Pion.conj PionFlavor.swap D) (z Q2 : ℝ) :
    favoured pionContent D .plus .down z Q2 = favoured pionContent D .plus .up z Q2 := by
  rw [favoured_pion_plus_down, favoured_pion_plus_up]
  have h1 := apply_map_eq_apply_conj Pion.conj_involutive hCC hI .plus (Species.quark .down) z Q2
  simpa using h1.symm

/-- The two unfavoured combinations of the positive pion agree: `D_d^{π⁺} = D_{ū}^{π⁺}`. -/
theorem unfavoured_pion_plus_down_eq_unfavoured_pion_plus_up
    {D : Frag Pion (Species PionFlavor)} (hCC : ChargeConjRelation Pion.conj D)
    (hI : FlavorRelation Pion.conj PionFlavor.swap D) (z Q2 : ℝ) :
    unfavoured pionContent D .plus .down z Q2 = unfavoured pionContent D .plus .up z Q2 := by
  rw [unfavoured_pion_plus_down, unfavoured_pion_plus_up]
  have h1 := apply_map_eq_apply_conj Pion.conj_involutive hCC hI .plus (Species.quark .up) z Q2
  simpa using h1

/-- The two relations of the pion triplet are satisfied together by a family whose favoured and
unfavoured combinations differ, so they leave both combinations free. -/
theorem exists_chargeConjRelation_and_flavorRelation_favoured_ne_unfavoured :
    ∃ D : Frag Pion (Species PionFlavor), Assumptions D ∧ ChargeConjRelation Pion.conj D ∧
      FlavorRelation Pion.conj PionFlavor.swap D ∧
      ∀ Q2 : ℝ, favoured pionContent D .plus .up (1 / 2) Q2
        ≠ unfavoured pionContent D .plus .up (1 / 2) Q2 :=
  ⟨valenceStepFrag pionContent, assumptions_valenceStepFrag _,
    chargeConjRelation_valenceStepFrag _,
    flavorRelation_valenceStepFrag _ pion_map_swap_mem_valence_conj,
    fun Q2 => favoured_valenceStepFrag_ne_unfavoured (isValenceFlavor_pion_plus .up) Q2⟩

end Fragmentation
end Particles
end EpsilonEridani
