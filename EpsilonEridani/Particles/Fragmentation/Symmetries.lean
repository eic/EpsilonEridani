/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Fragmentation.Basic
public import EpsilonEridani.Particles.Parton.ValenceContent

/-!
# Charge conjugation, flavour symmetry, and the favoured and unfavoured combinations

The fragmentation functions of one hadron multiplet are not independent: the discrete symmetries
relate the fragmentation of a parton into a hadron to the fragmentation of another parton into
another hadron of the same multiplet. This file states those relations and uses them to split the
fragmentation functions of a flavour into the two combinations that are quoted in practice.

A multiplet of observed hadrons is described by `Parton.ValenceContent`, whose valence assignment
is explicit data, so the favoured and unfavoured combinations below are read off the data and are
not a convention.

Two relations on a family `D` are named, both instances of `Invariant`. `ChargeConjRelation τ D`
says that the fragmentation of the antiparton of `s` into the antihadron `τ h` is the fragmentation
of `s` into `h`, and `FlavorRelation τ ρ D` says the same for a relabelling `ρ` of the quark
flavours together with the permutation `τ` of the multiplet it induces; isospin is the case where
`ρ` exchanges the up and the down flavour. Neither is a consequence of the definition of a
fragmentation function as an interface, so both are hypotheses of the theorems that use them. Where
both hold with the same permutation of the multiplet, `Invariant.apply_eq_apply` relates the
relabelled and the conjugate parton inside a single hadron; this is what reduces the number of
independent light-hadron fragmentation functions.

For a hadron `h` and a quark flavour `i`, the *favoured* combination collects the fragmentation
into `h` of those species of flavour `i` that are valence constituents of `h`, and the
*unfavoured* combination collects the rest. A flavour for which exactly one of the quark and the
antiquark is a valence constituent is a `IsValenceFlavor`; for such a flavour each combination is
a single fragmentation function, conjugating the parton index exchanges the two, and their
difference is the valence combination `D_{q_i} - D_{qbar_i}` when the valence constituent is the
quark and its negative when it is the antiquark. For a flavour whose quark and antiquark both
occur, as in a flavour-neutral hadron, the two combinations are not separated, and
`not_isValenceFlavor_pion_zero` exhibits that case.

The pion triplet `Parton.pionContent` is worked out as an instance:
`favored_pion_plus_down_eq_favored_pion_plus_up` is the familiar `D_u^{π⁺} = D_{dbar}^{π⁺}`, derived
from the two relations rather than assumed.

## Main definitions

* `EpsilonEridani.Particles.Fragmentation.ChargeConjRelation` and
  `EpsilonEridani.Particles.Fragmentation.FlavorRelation`: the two symmetry relations.
* `EpsilonEridani.Particles.Fragmentation.partonConj`: conjugating the parton index alone.
* `EpsilonEridani.Particles.Fragmentation.favored` and
  `EpsilonEridani.Particles.Fragmentation.unfavored`: the two combinations of a hadron and a
  flavour.
* `EpsilonEridani.Particles.Fragmentation.valenceStepFrag`: an explicit family satisfying the
  relations and separating the two combinations.

## Main statements

* `Fragmentation.favored_add_unfavored`: the two combinations add up to the total fragmentation
  of the flavour.
* `Fragmentation.favored_partonConj` and `Fragmentation.unfavored_partonConj`: on a valence
  flavour, conjugating the parton index exchanges the two combinations.
* `Fragmentation.favored_conj_of_chargeConjRelation`: under the charge-conjugation relation a
  hadron and its antiparticle have the same favoured combination.
* `Fragmentation.favored_valenceStepFrag_ne_unfavored`: the two combinations are not identified
  by the relations.
* `Fragmentation.favored_pion_plus_down_eq_favored_pion_plus_up`: `D_u^{π⁺} = D_{dbar}^{π⁺}`.

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

/-! ### The two symmetry relations -/

variable {D : Frag Hadron (Species Flavor)} {τ : Hadron → Hadron} {ρ : Flavor → Flavor}

/-- A family satisfies the *charge-conjugation relation* for the antiparticle map `τ` when the
fragmentation of the antiparton of `s` into the antihadron `τ h` is the fragmentation of `s` into
`h`, `D_{τ h}^{sbar} = D_h^s`. It is the relation that the action of charge conjugation on the
light-cone correlator imposes on the fragmentation functions of a multiplet. -/
abbrev ChargeConjRelation (τ : Hadron → Hadron) (D : Frag Hadron (Species Flavor)) : Prop :=
  Invariant τ Species.conj D

theorem chargeConjRelation_iff : ChargeConjRelation τ D ↔
    ∀ h s z Q2, D (τ h) (Species.conj s) z Q2 = D h s z Q2 :=
  invariant_iff

/-- A family satisfies the *flavour relation* of the symmetry `(τ, ρ)` — a relabelling `ρ` of the
quark flavours together with the permutation `τ` of the multiplet it induces — when
`D_{τ h}^{ρ s} = D_h^s`. Isospin within a light-hadron multiplet is the case where `ρ` exchanges
the up and the down flavour. -/
abbrev FlavorRelation (τ : Hadron → Hadron) (ρ : Flavor → Flavor)
    (D : Frag Hadron (Species Flavor)) : Prop :=
  Invariant τ (Species.map ρ) D

theorem flavorRelation_iff : FlavorRelation τ ρ D ↔
    ∀ h s z Q2, D (τ h) (Species.map ρ s) z Q2 = D h s z Q2 :=
  invariant_iff

/-- Conjugating the parton index alone: the fragmentation of the antiparton of `s` into the *same*
hadron. This is not a symmetry of a family — it compares two different physical functions — and on
a valence flavour it exchanges the favoured and the unfavoured combination. -/
def partonConj (D : Frag Hadron (Species Flavor)) : Frag Hadron (Species Flavor) :=
  comap id Species.conj D

theorem partonConj_eq_comap (D : Frag Hadron (Species Flavor)) :
    partonConj D = comap id Species.conj D :=
  (rfl)

@[simp]
theorem partonConj_apply (D : Frag Hadron (Species Flavor)) (h : Hadron) (s : Species Flavor)
    (z Q2 : ℝ) : partonConj D h s z Q2 = D h (Species.conj s) z Q2 :=
  (rfl)

@[simp]
theorem partonConj_partonConj (D : Frag Hadron (Species Flavor)) :
    partonConj (partonConj D) = D := by
  rw [partonConj_eq_comap, partonConj_eq_comap, comap_comap, Species.conj_involutive.comp_self]
  exact comap_id D

@[simp]
theorem zMoment_partonConj (D : Frag Hadron (Species Flavor)) (n : ℕ) (h : Hadron)
    (s : Species Flavor) (Q2 : ℝ) :
    zMoment (partonConj D) n h s Q2 = zMoment D n h (Species.conj s) Q2 :=
  zMoment_comap id Species.conj D n h s Q2

/-- Conjugating the parton index preserves the structural assumptions. -/
theorem Assumptions.partonConj (hD : Assumptions D) : Assumptions (Fragmentation.partonConj D) :=
  hD.comap id Species.conj

/-! ### The favoured and the unfavoured combination -/

variable [DecidableEq Flavor]

/-- The *favoured* combination of the hadron `h` and the flavour `i`: the fragmentation into `h`
of those species of flavour `i` that are valence constituents of `h`. -/
def favored (C : ValenceContent Hadron Flavor) (D : Frag Hadron (Species Flavor)) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : ℝ :=
  ∑ s ∈ Species.flavorPair i ∩ C.valence h, D h s z Q2

/-- The *unfavoured* combination of the hadron `h` and the flavour `i`: the fragmentation into `h`
of those species of flavour `i` that are not valence constituents of `h`. -/
def unfavored (C : ValenceContent Hadron Flavor) (D : Frag Hadron (Species Flavor)) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : ℝ :=
  ∑ s ∈ Species.flavorPair i \ C.valence h, D h s z Q2

variable (C : ValenceContent Hadron Flavor) (D)

theorem favored_def (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    favored C D h i z Q2 = ∑ s ∈ Species.flavorPair i ∩ C.valence h, D h s z Q2 :=
  (rfl)

theorem unfavored_def (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    unfavored C D h i z Q2 = ∑ s ∈ Species.flavorPair i \ C.valence h, D h s z Q2 :=
  (rfl)

/-- The two combinations of a flavour add up to the total fragmentation of that flavour, the sum
over its quark and its antiquark. -/
theorem favored_add_unfavored (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    favored C D h i z Q2 + unfavored C D h i z Q2
      = D h (Species.quark i) z Q2 + D h (Species.antiquark i) z Q2 := by
  rw [favored_def, unfavored_def, Finset.sum_inter_add_sum_sdiff, Species.sum_flavorPair]

/-- The favoured combination of a non-negative family is non-negative on the unit interval. -/
theorem favored_nonneg {D} (hD : Assumptions D) (h : Hadron) (i : Flavor) {z : ℝ} (hz₀ : 0 ≤ z)
    (hz₁ : z ≤ 1) (Q2 : ℝ) : 0 ≤ favored C D h i z Q2 :=
  Finset.sum_nonneg fun s _ => hD.nonneg h s z Q2 hz₀ hz₁

/-- The unfavoured combination of a non-negative family is non-negative on the unit interval. -/
theorem unfavored_nonneg {D} (hD : Assumptions D) (h : Hadron) (i : Flavor) {z : ℝ} (hz₀ : 0 ≤ z)
    (hz₁ : z ≤ 1) (Q2 : ℝ) : 0 ≤ unfavored C D h i z Q2 :=
  Finset.sum_nonneg fun s _ => hD.nonneg h s z Q2 hz₀ hz₁

variable {C D} {h : Hadron} {i : Flavor}

/-- When the quark of a flavour is its hadron's valence constituent and the antiquark is not,
the favoured combination of that flavour is the quark's fragmentation function. -/
theorem favored_eq_apply_quark (hq : Species.quark i ∈ C.valence h)
    (hq' : Species.antiquark i ∉ C.valence h) (z Q2 : ℝ) :
    favored C D h i z Q2 = D h (Species.quark i) z Q2 := by
  rw [favored_def, Species.flavorPair_def, Finset.insert_inter_of_mem hq,
    Finset.singleton_inter_of_notMem hq', insert_empty_eq, Finset.sum_singleton]

/-- When the antiquark of a flavour is its hadron's valence constituent and the quark is not,
the favoured combination of that flavour is the antiquark's fragmentation function. -/
theorem favored_eq_apply_antiquark (hq' : Species.antiquark i ∈ C.valence h)
    (hq : Species.quark i ∉ C.valence h) (z Q2 : ℝ) :
    favored C D h i z Q2 = D h (Species.antiquark i) z Q2 := by
  rw [favored_def, Species.flavorPair_def, Finset.insert_inter_of_notMem hq,
    Finset.singleton_inter_of_mem hq', Finset.sum_singleton]

/-- When the quark of a flavour is its hadron's valence constituent and the antiquark is not,
the unfavoured combination of that flavour is the antiquark's fragmentation function. -/
theorem unfavored_eq_apply_antiquark (hq : Species.quark i ∈ C.valence h)
    (hq' : Species.antiquark i ∉ C.valence h) (z Q2 : ℝ) :
    unfavored C D h i z Q2 = D h (Species.antiquark i) z Q2 := by
  have := favored_add_unfavored D C h i z Q2
  rw [favored_eq_apply_quark hq hq'] at this
  linarith

/-- When the antiquark of a flavour is its hadron's valence constituent and the quark is not,
the unfavoured combination of that flavour is the quark's fragmentation function. -/
theorem unfavored_eq_apply_quark (hq' : Species.antiquark i ∈ C.valence h)
    (hq : Species.quark i ∉ C.valence h) (z Q2 : ℝ) :
    unfavored C D h i z Q2 = D h (Species.quark i) z Q2 := by
  have := favored_add_unfavored D C h i z Q2
  rw [favored_eq_apply_antiquark hq' hq] at this
  linarith

/-- On a flavour whose valence constituent is the quark, the difference of the two combinations is
the valence combination `D_{q_i} - D_{qbar_i}` of that flavour. -/
theorem favored_sub_unfavored_eq_of_quark_mem (hq : Species.quark i ∈ C.valence h)
    (hq' : Species.antiquark i ∉ C.valence h) (z Q2 : ℝ) :
    favored C D h i z Q2 - unfavored C D h i z Q2
      = D h (Species.quark i) z Q2 - D h (Species.antiquark i) z Q2 := by
  rw [favored_eq_apply_quark hq hq', unfavored_eq_apply_antiquark hq hq']

/-- On a flavour whose valence constituent is the antiquark, the difference of the two combinations
is the opposite `D_{qbar_i} - D_{q_i}` of the valence combination of that flavour. -/
theorem favored_sub_unfavored_eq_of_antiquark_mem (hq' : Species.antiquark i ∈ C.valence h)
    (hq : Species.quark i ∉ C.valence h) (z Q2 : ℝ) :
    favored C D h i z Q2 - unfavored C D h i z Q2
      = D h (Species.antiquark i) z Q2 - D h (Species.quark i) z Q2 := by
  rw [favored_eq_apply_antiquark hq' hq, unfavored_eq_apply_quark hq' hq]

/-! ### Reindexing the combinations by conjugation -/

private theorem image_conj_inter_valence (C : ValenceContent Hadron Flavor) (h : Hadron)
    (i : Flavor) : (Species.flavorPair i ∩ C.valence h).image Species.conj
      = Species.flavorPair i ∩ C.valence (C.conj h) := by
  rw [Finset.image_inter _ _ Species.conj_involutive.injective, Species.image_conj_flavorPair,
    C.image_conj_valence]

private theorem image_conj_sdiff_valence (C : ValenceContent Hadron Flavor) (h : Hadron)
    (i : Flavor) : (Species.flavorPair i \ C.valence h).image Species.conj
      = Species.flavorPair i \ C.valence (C.conj h) := by
  rw [Finset.image_sdiff _ _ Species.conj_involutive.injective, Species.image_conj_flavorPair,
    C.image_conj_valence]

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
theorem favored_partonConj (hi : C.IsValenceFlavor h i) (z Q2 : ℝ) :
    favored C (partonConj D) h i z Q2 = unfavored C D h i z Q2 := by
  rw [favored_def, unfavored_def, ← inter_valence_conj_eq_sdiff hi,
    ← image_conj_inter_valence, Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => partonConj_apply D h s z Q2

/-- On a valence flavour, conjugating the parton index carries the unfavoured combination to the
favoured one. -/
theorem unfavored_partonConj (hi : C.IsValenceFlavor h i) (z Q2 : ℝ) :
    unfavored C (partonConj D) h i z Q2 = favored C D h i z Q2 := by
  rw [favored_def, unfavored_def, ← sdiff_valence_conj_eq_inter hi,
    ← image_conj_sdiff_valence, Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => partonConj_apply D h s z Q2

/-- Under the charge-conjugation relation of a multiplet, a hadron and its antiparticle have the
same favoured combination at every flavour. -/
theorem favored_conj_of_chargeConjRelation (C : ValenceContent Hadron Flavor)
    {D : Frag Hadron (Species Flavor)} (hCC : ChargeConjRelation C.conj D) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : favored C D (C.conj h) i z Q2 = favored C D h i z Q2 := by
  rw [favored_def, favored_def, ← image_conj_inter_valence,
    Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => hCC.apply h s z Q2

/-- Under the charge-conjugation relation of a multiplet, a hadron and its antiparticle have the
same unfavoured combination at every flavour. -/
theorem unfavored_conj_of_chargeConjRelation (C : ValenceContent Hadron Flavor)
    {D : Frag Hadron (Species Flavor)} (hCC : ChargeConjRelation C.conj D) (h : Hadron)
    (i : Flavor) (z Q2 : ℝ) : unfavored C D (C.conj h) i z Q2 = unfavored C D h i z Q2 := by
  rw [unfavored_def, unfavored_def, ← image_conj_sdiff_valence,
    Finset.sum_image Species.conj_involutive.injective.injOn]
  exact Finset.sum_congr rfl fun s _ => hCC.apply h s z Q2

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

/-- `valenceStepFrag` is invariant under a map of the hadrons and a map of the species exactly
because the valence content is. -/
theorem invariant_valenceStepFrag (C : ValenceContent Hadron Flavor)
    {σ : Species Flavor → Species Flavor}
    (hv : ∀ h s, σ s ∈ C.valence (τ h) ↔ s ∈ C.valence h) :
    Invariant τ σ (valenceStepFrag C) := by
  rw [Invariant, valenceStepFrag_def, comap_indicatorUnitInterval]
  congr 1
  funext h s z _
  simp only [comap_apply, hv]

/-- `valenceStepFrag` satisfies the charge-conjugation relation of its multiplet, because the
valence content does. -/
theorem chargeConjRelation_valenceStepFrag (C : ValenceContent Hadron Flavor) :
    ChargeConjRelation C.conj (valenceStepFrag C) :=
  invariant_valenceStepFrag C fun h s => by rw [C.mem_valence_conj, Species.conj_conj]

/-- On a valence flavour the favoured combination of `valenceStepFrag` is `2 z`. -/
theorem favored_valenceStepFrag (hi : C.IsValenceFlavor h i) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (Q2 : ℝ) :
    favored C (valenceStepFrag C) h i z Q2 = 2 * z := by
  rcases ValenceContent.isValenceFlavor_iff.1 hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · rw [favored_eq_apply_quark hq hq', valenceStepFrag_apply_of_mem C hz hq]
  · rw [favored_eq_apply_antiquark hq' hq, valenceStepFrag_apply_of_mem C hz hq']

/-- On a valence flavour the unfavoured combination of `valenceStepFrag` is `1 - z`. -/
theorem unfavored_valenceStepFrag (hi : C.IsValenceFlavor h i) {z : ℝ}
    (hz : z ∈ Set.Icc (0 : ℝ) 1) (Q2 : ℝ) :
    unfavored C (valenceStepFrag C) h i z Q2 = 1 - z := by
  rcases ValenceContent.isValenceFlavor_iff.1 hi with ⟨hq, hq'⟩ | ⟨hq', hq⟩
  · rw [unfavored_eq_apply_antiquark hq hq', valenceStepFrag_apply_of_notMem C hz hq']
  · rw [unfavored_eq_apply_quark hq' hq, valenceStepFrag_apply_of_notMem C hz hq]

/-- The favoured and the unfavoured combination of a valence flavour are different functions, and
the charge-conjugation relation does not identify them: `valenceStepFrag` satisfies that relation
and gives `1` for the favoured and `1/2` for the unfavoured combination at `z = 1/2`. -/
theorem favored_valenceStepFrag_ne_unfavored (hi : C.IsValenceFlavor h i) (Q2 : ℝ) :
    favored C (valenceStepFrag C) h i (1 / 2) Q2
      ≠ unfavored C (valenceStepFrag C) h i (1 / 2) Q2 := by
  rw [favored_valenceStepFrag hi (by norm_num), unfavored_valenceStepFrag hi (by norm_num)]
  norm_num

/-! ### The pion triplet -/

/-- The favoured combination of the positive pion at the up flavour is the fragmentation of the
up quark. -/
theorem favored_pion_plus_up (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    favored pionContent D .plus .up z Q2 = D .plus (.quark .up) z Q2 :=
  favored_eq_apply_quark (by simp) (by simp) z Q2

/-- The favoured combination of the positive pion at the down flavour is the fragmentation of
the down antiquark. -/
theorem favored_pion_plus_down (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    favored pionContent D .plus .down z Q2 = D .plus (.antiquark .down) z Q2 :=
  favored_eq_apply_antiquark (by simp) (by simp) z Q2

/-- The unfavoured combination of the positive pion at the up flavour is the fragmentation of
the up antiquark. -/
theorem unfavored_pion_plus_up (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    unfavored pionContent D .plus .up z Q2 = D .plus (.antiquark .up) z Q2 :=
  unfavored_eq_apply_antiquark (by simp) (by simp) z Q2

/-- The unfavoured combination of the positive pion at the down flavour is the fragmentation of
the down quark. -/
theorem unfavored_pion_plus_down (D : Frag Pion (Species PionFlavor)) (z Q2 : ℝ) :
    unfavored pionContent D .plus .down z Q2 = D .plus (.quark .down) z Q2 :=
  unfavored_eq_apply_quark (by simp) (by simp) z Q2

/-- The two favoured combinations of the positive pion agree: `D_u^{π⁺} = D_{dbar}^{π⁺}`. This is
the relation that reduces the independent pion fragmentation functions to one favoured and one
unfavoured function, and it is a consequence of charge conjugation together with isospin, not a
separate assumption. -/
theorem favored_pion_plus_down_eq_favored_pion_plus_up
    {D : Frag Pion (Species PionFlavor)} (hCC : ChargeConjRelation Pion.conj D)
    (hI : FlavorRelation Pion.conj PionFlavor.swap D) (z Q2 : ℝ) :
    favored pionContent D .plus .down z Q2 = favored pionContent D .plus .up z Q2 := by
  rw [favored_pion_plus_down, favored_pion_plus_up]
  have h1 := Invariant.apply_eq_apply Pion.conj_involutive hCC hI .plus (Species.quark .down) z Q2
  simpa using h1.symm

/-- The two unfavoured combinations of the positive pion agree: `D_d^{π⁺} = D_{ubar}^{π⁺}`. -/
theorem unfavored_pion_plus_down_eq_unfavored_pion_plus_up
    {D : Frag Pion (Species PionFlavor)} (hCC : ChargeConjRelation Pion.conj D)
    (hI : FlavorRelation Pion.conj PionFlavor.swap D) (z Q2 : ℝ) :
    unfavored pionContent D .plus .down z Q2 = unfavored pionContent D .plus .up z Q2 := by
  rw [unfavored_pion_plus_down, unfavored_pion_plus_up]
  have h1 := Invariant.apply_eq_apply Pion.conj_involutive hCC hI .plus (Species.quark .up) z Q2
  simpa using h1

/-- The two relations of the pion triplet are satisfied together by a family whose favoured and
unfavoured combinations differ, so the two relations do not identify the favoured with the
unfavoured combination. -/
theorem exists_chargeConjRelation_and_flavorRelation_favored_ne_unfavored :
    ∃ D : Frag Pion (Species PionFlavor), Assumptions D ∧ ChargeConjRelation Pion.conj D ∧
      FlavorRelation Pion.conj PionFlavor.swap D ∧
      ∀ Q2 : ℝ, favored pionContent D .plus .up (1 / 2) Q2
        ≠ unfavored pionContent D .plus .up (1 / 2) Q2 :=
  ⟨valenceStepFrag pionContent, assumptions_valenceStepFrag _,
    pionContent_conj ▸ chargeConjRelation_valenceStepFrag _,
    invariant_valenceStepFrag _ pion_map_swap_mem_valence_conj_iff,
    fun Q2 => favored_valenceStepFrag_ne_unfavored (isValenceFlavor_pion_plus .up) Q2⟩

end Fragmentation
end Particles
end EpsilonEridani
