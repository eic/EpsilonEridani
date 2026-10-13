/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib
/-!

# Collinear PDF Object Model

This module introduces first-class collinear PDF objects with explicit assumptions,
sum-rule interfaces, and Mellin-moment hooks.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace PDF

variable {Flavor : Type}

/-- A collinear PDF family with flavor index `i`, Bjorken variable `x`, and scale `Q2`. -/
abbrev Pdf (Flavor : Type) : Type := Flavor → ℝ → ℝ → ℝ

/-- The Mellin moment used by evolution and sum-rule interfaces. -/
def mellinMoment (f : Pdf Flavor) (n : ℕ) (i : Flavor) (Q2 : ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, x ^ n * f i x Q2

/-- Structural assumptions for a collinear PDF object.

The `nonneg` field is derivable, not fundamental. Positivity of a leading-twist parton density
is a consequence of positive semidefiniteness of the parton spin-density matrix, and for any
density built through that route it is a theorem: see `PDF.pdfOfSpinDensity_nonneg` and
`PDF.assumptions_pdfOfSpinDensity` in `Physlib/Particles/Parton/PDF/Positivity.lean`, where the
remaining three fields are exactly what has to be supplied. The field is kept here so that
existing users of `Assumptions` are unaffected. -/
structure Assumptions (f : Pdf Flavor) : Prop where
  support : ∀ i x Q2, x < 0 ∨ 1 < x → f i x Q2 = 0
  nonneg : ∀ i x Q2, 0 ≤ x → x ≤ 1 → 0 ≤ f i x Q2
  measurable : ∀ i Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => f i x Q2)
  momentIntegrable : ∀ n i Q2, MeasureTheory.Integrable (fun x : ℝ => x ^ n * f i x Q2)

/-- Outside the physical support domain, the PDF vanishes. -/
lemma eq_zero_of_not_mem_unitInterval
    (f : Pdf Flavor) (h : Assumptions f) (i : Flavor) (x Q2 : ℝ)
    (hx : x < 0 ∨ 1 < x) :
    f i x Q2 = 0 :=
  h.support i x Q2 hx

/-- On the unit interval, the PDF is nonnegative. -/
lemma nonneg_on_unitInterval
    (f : Pdf Flavor) (h : Assumptions f) (i : Flavor) (x Q2 : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ f i x Q2 :=
  h.nonneg i x Q2 hx0 hx1

/-- Integrability of Mellin-moment integrands provided by structural assumptions. -/
lemma mellinMoment_integrable
    (f : Pdf Flavor) (h : Assumptions f) (n : ℕ) (i : Flavor) (Q2 : ℝ) :
  MeasureTheory.Integrable (fun x : ℝ => x ^ n * f i x Q2) :=
  h.momentIntegrable n i Q2

/-! ### The analytic/physical split of `Assumptions`

`Assumptions` bundles two kinds of hypothesis, and the difference decides what can be
discharged and what cannot.

* `IsPartonDensity` is the **physical** half: the momentum fraction lies in `[0, 1]` and the
  density is nonnegative there. This is not a gap in the development. It is what the words
  "parton density" mean, and there is no formulation in which it becomes a theorem about an
  arbitrary function `Flavor → ℝ → ℝ → ℝ`; a concrete model either has the property or is
  not a parton density. (For a density built from a spin-density matrix the `nonneg` clause
  *is* a theorem — `EpsilonEridani.Particles.Parton.PDF.pdfOfSpinDensity_nonneg` — but that is a
  statement about that construction, not about `Pdf` in general.)
* `Regularity` is the **analytic** half: measurability in the momentum fraction and
  integrability of the Mellin-moment integrands. These are genuine obligations, and
  `EpsilonEridani.Particles.Parton.PDF.Model` discharges them for an explicit model.

`assumptions_iff` records that the split is exact: the bundle is the conjunction of the two
halves and nothing else. `Assumptions` itself is left in place with its field set unchanged,
because modules outside this one take it as a hypothesis.
-/

/-- **What it means to be a collinear parton density**: support in the physical range of the
momentum fraction, and nonnegativity there. A definition, not a theorem. -/
structure IsPartonDensity (f : Pdf Flavor) : Prop where
  /-- The density vanishes outside `[0, 1]`. -/
  support : ∀ i x Q2, x < 0 ∨ 1 < x → f i x Q2 = 0
  /-- The density is nonnegative on `[0, 1]`. -/
  nonneg : ∀ i x Q2, 0 ≤ x → x ≤ 1 → 0 ≤ f i x Q2

/-- **The analytic half of `Assumptions`**: measurability and moment integrability. Unlike
`IsPartonDensity` these are obligations that a concrete model discharges. -/
structure Regularity (f : Pdf Flavor) : Prop where
  /-- `f i · Q2` is almost-everywhere strongly measurable. -/
  measurable : ∀ i Q2, MeasureTheory.AEStronglyMeasurable (fun x : ℝ => f i x Q2)
  /-- Every Mellin-moment integrand of `f` is integrable. -/
  momentIntegrable : ∀ n i Q2, MeasureTheory.Integrable (fun x : ℝ => x ^ n * f i x Q2)

/-- The physical half of a full assumption bundle. -/
lemma Assumptions.isPartonDensity {f : Pdf Flavor} (h : Assumptions f) :
    IsPartonDensity f :=
  { support := h.support, nonneg := h.nonneg }

/-- The analytic half of a full assumption bundle. -/
lemma Assumptions.regularity {f : Pdf Flavor} (h : Assumptions f) : Regularity f :=
  { measurable := h.measurable, momentIntegrable := h.momentIntegrable }

/-- The split is exact: `Assumptions` is the conjunction of the physical and the analytic
half, with no residue. -/
lemma assumptions_iff {f : Pdf Flavor} :
    Assumptions f ↔ IsPartonDensity f ∧ Regularity f :=
  ⟨fun h => ⟨h.isPartonDensity, h.regularity⟩, fun h =>
    { support := h.1.support
      nonneg := h.1.nonneg
      measurable := h.2.measurable
      momentIntegrable := h.2.momentIntegrable }⟩

/-- Sum-rule assumptions used by the PDF interfaces. -/
structure SumRuleAssumptions [Fintype Flavor] (f : Pdf Flavor) : Type where
  momentum : ∀ Q2, (∑ i, mellinMoment f 1 i Q2) = 1
  /-- Target value of the zeroth Mellin moment of each flavor. -/
  valenceTarget : Flavor → ℝ
  valence : ∀ i Q2, mellinMoment f 0 i Q2 = valenceTarget i

/-- Momentum sum-rule interface theorem. -/
lemma momentum_sumRule [Fintype Flavor]
    (f : Pdf Flavor) (h : SumRuleAssumptions f) (Q2 : ℝ) :
    (∑ i, mellinMoment f 1 i Q2) = 1 :=
  h.momentum Q2

/-- Valence sum-rule interface theorem. -/
lemma valence_sumRule [Fintype Flavor]
    (f : Pdf Flavor) (h : SumRuleAssumptions f) (i : Flavor) (Q2 : ℝ) :
    mellinMoment f 0 i Q2 = h.valenceTarget i :=
  h.valence i Q2

/-! ### Pulling a density back along a map of parton indices

A map `σ : κ → ι` of parton indices pulls a density over `ι` back to a density over `κ`,
`comap σ f k = f (σ k)`. The density assumptions survive any such pullback; the summed moments
and the sum-rule bundle survive a bijective one. Charge conjugation and flavour symmetries act on
densities this way. -/

section Comap

variable {ι κ μ : Type}

/-- A moment of a density depends on it only through the density of the given parton at the
given scale on the unit interval. -/
lemma mellinMoment_congr {f : Pdf ι} {g : Pdf κ} {i : ι} {j : κ} {Q2 : ℝ}
    (h : Set.EqOn (f i · Q2) (g j · Q2) (Set.Icc 0 1)) (n : ℕ) :
    mellinMoment f n i Q2 = mellinMoment g n j Q2 :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => by
    simp only [show f i x Q2 = g j x Q2 from h hx]

/-- The density over `κ` whose parton `k` carries the density of parton `σ k` in `f`. -/
def comap (σ : κ → ι) (f : Pdf ι) : Pdf κ := fun k => f (σ k)

@[simp]
lemma comap_apply (σ : κ → ι) (f : Pdf ι) (k : κ) (x Q2 : ℝ) :
    comap σ f k x Q2 = f (σ k) x Q2 :=
  rfl

@[simp]
lemma comap_id (f : Pdf ι) : comap id f = f :=
  rfl

@[simp]
lemma comap_comap (σ : κ → ι) (τ : μ → κ) (f : Pdf ι) :
    comap τ (comap σ f) = comap (σ ∘ τ) f :=
  rfl

@[simp]
lemma mellinMoment_comap (σ : κ → ι) (f : Pdf ι) (n : ℕ) (k : κ) (Q2 : ℝ) :
    mellinMoment (comap σ f) n k Q2 = mellinMoment f n (σ k) Q2 :=
  mellinMoment_congr (fun _ _ => comap_apply σ f k _ Q2) n

/-- A bijective pullback preserves every moment summed over all partons. -/
lemma sum_mellinMoment_comap [Fintype ι] [Fintype κ] {σ : κ → ι} (hσ : σ.Bijective)
    (f : Pdf ι) (n : ℕ) (Q2 : ℝ) :
    ∑ k, mellinMoment (comap σ f) n k Q2 = ∑ i, mellinMoment f n i Q2 := by
  simp only [mellinMoment_comap]
  exact hσ.sum_comp fun i => mellinMoment f n i Q2

/-- A pullback preserves the physical half of the assumptions. -/
lemma IsPartonDensity.comap {f : Pdf ι} (h : IsPartonDensity f) (σ : κ → ι) :
    IsPartonDensity (comap σ f) where
  support k x Q2 hx := by simpa only [comap_apply] using h.support (σ k) x Q2 hx
  nonneg k x Q2 hx₀ hx₁ := by simpa only [comap_apply] using h.nonneg (σ k) x Q2 hx₀ hx₁

/-- A pullback preserves the analytic half of the assumptions. -/
lemma Regularity.comap {f : Pdf ι} (h : Regularity f) (σ : κ → ι) :
    Regularity (comap σ f) where
  measurable k Q2 := by simpa only [comap_apply] using h.measurable (σ k) Q2
  momentIntegrable n k Q2 := by simpa only [comap_apply] using h.momentIntegrable n (σ k) Q2

/-- A pullback preserves the density assumptions. -/
lemma Assumptions.comap {f : Pdf ι} (h : Assumptions f) (σ : κ → ι) :
    Assumptions (comap σ f) :=
  assumptions_iff.2 ⟨h.isPartonDensity.comap σ, h.regularity.comap σ⟩

/-- A bijective pullback preserves the sum-rule bundle, with the target value of each parton
taken from its image. -/
def SumRuleAssumptions.comap [Fintype ι] [Fintype κ] {f : Pdf ι} (h : SumRuleAssumptions f)
    {σ : κ → ι} (hσ : σ.Bijective) : SumRuleAssumptions (comap σ f) where
  momentum Q2 := (sum_mellinMoment_comap hσ f 1 Q2).trans (h.momentum Q2)
  valenceTarget k := h.valenceTarget (σ k)
  valence k Q2 := (mellinMoment_comap σ f 0 k Q2).trans (h.valence (σ k) Q2)

@[simp]
lemma SumRuleAssumptions.comap_valenceTarget [Fintype ι] [Fintype κ] {f : Pdf ι}
    (h : SumRuleAssumptions f) {σ : κ → ι} (hσ : σ.Bijective) (k : κ) :
    (h.comap hσ).valenceTarget k = h.valenceTarget (σ k) :=
  rfl

end Comap

end PDF
end Parton
end Particles
end EpsilonEridani
