/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.Basic
public import EpsilonEridani.Particles.Parton.Species

/-!
# Charge conjugation and valence numbers of collinear densities

A collinear density over the parton species `Species Flavor` carries the quark, antiquark and
gluon densities of a hadron in one `PDF.Pdf`, so a species sum such as the momentum sum rule
`∑ₛ ∫₀¹ x fₛ(x) dx = 1` runs over all of them, the gluon included.

Charge conjugation acts on densities by pulling back along `Species.conj`,
`PDF.chargeConj f s = f s.conj`: the densities of a hadron's antiparticle are the charge
conjugates of the hadron's densities. The operation is an involution, it preserves
`PDF.IsPartonDensity`, `PDF.Regularity` and `PDF.Assumptions`, the momentum sum and the sum-rule
bundle `PDF.SumRuleAssumptions`; these are instances of the general results
`PDF.Assumptions.comap` and its companions.

On a density over `Species Flavor` the integral `∫₀¹ (q_i(x) - qbar_i(x)) dx` is the net number of
quarks of flavour `i`, the valence number `PDF.valenceNumber`. The valence sum rules of a hadron
prescribe it flavour by flavour. Charge conjugation negates every valence number, and a flavour
whose quark and antiquark densities agree, as in a charge-conjugation invariant density, has no
valence number.

For a density carrying the sum-rule bundle, prescribing the valence numbers to be a given
`v : Flavor → ℝ` is a condition on the bundle's scale-independent valence targets alone
(`valenceNumber_eq_sub_valenceTarget`, `forall_valenceNumber_eq_iff_valenceTarget`); in
particular such a prescription needs to be imposed at only one scale
(`valenceNumber_eq_of_forall_valenceNumber_eq`).

## Main definitions

* `EpsilonEridani.Particles.Parton.PDF.chargeConj`: the charge-conjugate density.
* `EpsilonEridani.Particles.Parton.PDF.valenceNumber`: `∫₀¹ (q_i - qbar_i)`.

## Main statements

* `PDF.IsPartonDensity.chargeConj`, `PDF.Regularity.chargeConj`, `PDF.Assumptions.chargeConj`,
  `PDF.SumRuleAssumptions.chargeConj`: charge conjugation preserves the density assumptions and
  the sum-rule bundle.
* `PDF.sum_mellinMoment_chargeConj`: it preserves every species-summed moment, in particular the
  momentum sum.
* `PDF.chargeConj_weight`: it commutes with a species-wise rescaling, conjugating the weight.
* `PDF.valenceNumber_chargeConj`: it negates the valence numbers.
* `PDF.valenceNumber_eq_sub_valenceTarget`: under the sum-rule bundle, the valence number is the
  quark target minus the antiquark target.
* `PDF.forall_valenceNumber_eq_iff_valenceTarget`: under the sum-rule bundle, prescribed valence
  numbers are a condition on the bundle's valence targets alone;
  `PDF.valenceNumber_eq_of_forall_valenceNumber_eq` is that such a prescription holds at every
  scale as soon as it holds at one.
* `PDF.valenceNumber_eq_zero_of_quark_eq_antiquark`: a flavour with equal quark and antiquark
  densities on the unit interval at a scale has vanishing valence number there;
  `PDF.valenceNumber_eq_zero_of_chargeConj_eq` is the case of a charge-conjugation invariant
  density.

## References

* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), ch. 6.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace PDF

open Species

variable {Flavor : Type}

/-- The charge-conjugate density: the density of species `s` is the density of `s.conj` in `f`.
The densities of a hadron's antiparticle are the charge conjugates of the hadron's densities. -/
def chargeConj (f : Pdf (Species Flavor)) : Pdf (Species Flavor) :=
  comap conj f

theorem chargeConj_eq_comap (f : Pdf (Species Flavor)) : chargeConj f = comap conj f :=
  (rfl)

@[simp]
theorem chargeConj_apply (f : Pdf (Species Flavor)) (s : Species Flavor) (x Q2 : ℝ) :
    chargeConj f s x Q2 = f s.conj x Q2 := by
  rw [chargeConj_eq_comap, comap_apply]

@[simp]
theorem chargeConj_chargeConj (f : Pdf (Species Flavor)) : chargeConj (chargeConj f) = f := by
  rw [chargeConj_eq_comap, chargeConj_eq_comap, comap_comap, conj_involutive.comp_self, comap_id]

theorem chargeConj_involutive :
    Function.Involutive (chargeConj : Pdf (Species Flavor) → Pdf (Species Flavor)) :=
  chargeConj_chargeConj

@[simp]
theorem mellinMoment_chargeConj (f : Pdf (Species Flavor)) (n : ℕ) (s : Species Flavor)
    (Q2 : ℝ) : mellinMoment (chargeConj f) n s Q2 = mellinMoment f n s.conj Q2 := by
  rw [chargeConj_eq_comap, mellinMoment_comap]

/-- Charge conjugation preserves every moment summed over all species; for `n = 1` this is the
statement that the momentum sum of the conjugate density is that of the density. -/
theorem sum_mellinMoment_chargeConj [Fintype Flavor] (f : Pdf (Species Flavor)) (n : ℕ)
    (Q2 : ℝ) : ∑ s, mellinMoment (chargeConj f) n s Q2 = ∑ s, mellinMoment f n s Q2 := by
  rw [chargeConj_eq_comap]
  exact sum_mellinMoment_comap conj_involutive.bijective f n Q2

/-- Charge conjugation commutes with a species-wise rescaling: the conjugate of a rescaled
density is the conjugate density rescaled by the conjugated weight. -/
theorem chargeConj_weight (w : Species Flavor → ℝ) (f : Pdf (Species Flavor)) :
    chargeConj (weight w f) = weight (w ∘ conj) (chargeConj f) := by
  rw [chargeConj_eq_comap, comap_weight, chargeConj_eq_comap]

/-- Charge conjugation preserves the physical half of the density assumptions. -/
theorem IsPartonDensity.chargeConj {f : Pdf (Species Flavor)} (h : IsPartonDensity f) :
    IsPartonDensity (chargeConj f) := by
  rw [chargeConj_eq_comap]
  exact h.comap conj

/-- Charge conjugation preserves the analytic half of the density assumptions. -/
theorem Regularity.chargeConj {f : Pdf (Species Flavor)} (h : Regularity f) :
    Regularity (chargeConj f) := by
  rw [chargeConj_eq_comap]
  exact h.comap conj

/-- Charge conjugation preserves the density assumptions. -/
theorem Assumptions.chargeConj {f : Pdf (Species Flavor)} (h : Assumptions f) :
    Assumptions (chargeConj f) := by
  rw [chargeConj_eq_comap]
  exact h.comap conj

/-- Charge conjugation preserves the sum-rule bundle, with the target values of each species
taken from its conjugate. -/
def SumRuleAssumptions.chargeConj [Fintype Flavor] {f : Pdf (Species Flavor)}
    (h : SumRuleAssumptions f) : SumRuleAssumptions (chargeConj f) :=
  h.comap conj_involutive.bijective

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

/-- Under the sum-rule bundle, the valence number of a flavour is the target value of its quark
minus that of its antiquark, at every scale. -/
theorem valenceNumber_eq_sub_valenceTarget [Fintype Flavor] {f : Pdf (Species Flavor)}
    (h : SumRuleAssumptions f) (i : Flavor) (Q2 : ℝ) :
    valenceNumber f i Q2 = h.valenceTarget (.quark i) - h.valenceTarget (.antiquark i) := by
  rw [valenceNumber_def, h.valence, h.valence]

/-- **Prescribed valence numbers are a condition on the valence targets.** For a density carrying
the sum-rule bundle, carrying the valence numbers `v` at every flavour and every scale holds
exactly when the target of the quark of each flavour minus that of its antiquark is `v` at that
flavour. In particular such a prescription constrains no other datum of the bundle. -/
theorem forall_valenceNumber_eq_iff_valenceTarget [Fintype Flavor] {f : Pdf (Species Flavor)}
    (h : SumRuleAssumptions f) (v : Flavor → ℝ) :
    (∀ i Q2, valenceNumber f i Q2 = v i) ↔
      ∀ i, h.valenceTarget (.quark i) - h.valenceTarget (.antiquark i) = v i := by
  refine ⟨fun hf i => ?_, fun hf i Q2 => ?_⟩
  · rw [← valenceNumber_eq_sub_valenceTarget h i 0]
    exact hf i 0
  · rw [valenceNumber_eq_sub_valenceTarget h i Q2]
    exact hf i

/-- **One scale is enough.** A density carrying the sum-rule bundle and the valence numbers `v` at
a single scale `Q2₀` carries them at every scale: by `forall_valenceNumber_eq_iff_valenceTarget`
the prescription is a condition on the bundle's scale-independent valence targets. -/
theorem valenceNumber_eq_of_forall_valenceNumber_eq [Fintype Flavor] {f : Pdf (Species Flavor)}
    {v : Flavor → ℝ} (h : SumRuleAssumptions f) {Q2₀ : ℝ}
    (hf : ∀ i, valenceNumber f i Q2₀ = v i) (i : Flavor) (Q2 : ℝ) :
    valenceNumber f i Q2 = v i :=
  (forall_valenceNumber_eq_iff_valenceTarget h v).2
    (fun j => by rw [← valenceNumber_eq_sub_valenceTarget h j Q2₀]; exact hf j) i Q2

/-- Charge conjugation negates the valence number of every flavour. -/
@[simp]
theorem valenceNumber_chargeConj (f : Pdf (Species Flavor)) (i : Flavor) (Q2 : ℝ) :
    valenceNumber (chargeConj f) i Q2 = -valenceNumber f i Q2 := by
  simp [valenceNumber_def]

/-- A flavour whose quark and antiquark densities coincide on the unit interval at the scale
`Q2` has vanishing valence number there. -/
theorem valenceNumber_eq_zero_of_quark_eq_antiquark {f : Pdf (Species Flavor)} {i : Flavor}
    {Q2 : ℝ} (h : Set.EqOn (f (.quark i) · Q2) (f (.antiquark i) · Q2) (Set.Icc 0 1)) :
    valenceNumber f i Q2 = 0 := by
  rw [valenceNumber_def, mellinMoment_congr h, sub_self]

/-- A density invariant under charge conjugation has vanishing valence number for every flavour
at every scale. -/
theorem valenceNumber_eq_zero_of_chargeConj_eq {f : Pdf (Species Flavor)} (h : chargeConj f = f)
    (i : Flavor) (Q2 : ℝ) : valenceNumber f i Q2 = 0 :=
  valenceNumber_eq_zero_of_quark_eq_antiquark fun x _ => by
    simpa using congr_fun₃ h (.antiquark i) x Q2

end PDF

end Parton
end Particles
end EpsilonEridani
