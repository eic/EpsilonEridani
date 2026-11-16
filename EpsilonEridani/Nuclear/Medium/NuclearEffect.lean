/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# The initial-state / final-state decomposition of a nuclear effect

A semi-inclusive observable on a nucleus, such as the hadron multiplicity ratio of a nucleus to a
nucleon, depends on the momentum fraction `x`, the hard scale `Q2`, the energy transfer `ν` and the
hadron momentum fraction `z`. Its nuclear modification receives two kinds of contribution: an
*initial-state* one, from the modification of the parton densities of the bound nucleons, and a
*final-state* one, from what happens to the struck parton and the forming hadron on their way out
of the nucleus. A `NuclearEffect` records the two as separate data. Its initial-state factor is a
function of `x` and `Q2` only, so that its independence of the energy transfer at fixed momentum
fraction and scale is part of its type. Its final-state factor depends on all four variables.

The split is only meaningful if an observable determines it. This file proves that it does,
under three conditions: the observable is the product of the two factors
(`NuclearEffect.FactorizationHypothesis`), the final-state factor tends to one along a nontrivial
filter `l` of energy transfers (`NuclearEffect.IsNormalized`), and the initial-state factor vanishes
nowhere. Physically `l` is `Filter.atTop`: at large
energy transfer the hadron forms outside the nucleus and the final-state effects disappear. A
reference energy transfer `ν₀` at which the final-state factor is one by convention is
`l = pure ν₀`. Without the normalisation the split is determined only up to a factor depending on
`x` and `Q2`, which can be moved from one factor to the other.

The independence of the initial-state factor from the energy transfer is what makes the split
unique. If it is dropped, so that both factors may depend on all four variables, the normalised
splits of one observable form an explicit family parametrised by a nowhere-zero function tending to
one along `l`, and this family has more than one member.

## Main definitions

* `NuclearEffect`: an initial-state factor of `(x, Q2)` and a final-state factor of
  `(x, Q2, ν, z)`.
* `NuclearEffect.FactorizationHypothesis E obs`: the observable `obs` is the product of the two
  factors of `E`, with no cross term.
* `NuclearEffect.IsNormalized E l`: the final-state factor of `E` tends to one along `l`.
* `IsNormalizedSplit obs I F l`: `obs = I * F` with `F` tending to one along `l`, where both factors
  may depend on all four variables.

## Main results

* `NuclearEffect.FactorizationHypothesis.tendsto_initialState`: under the normalisation, the
  initial-state factor is the limit of the observable along `l`.
* `NuclearEffect.FactorizationHypothesis.finalState_eq_div`: where the initial-state factor does
  not vanish, the final-state factor is the observable divided by the initial-state factor.
* `NuclearEffect.FactorizationHypothesis.div_eq_finalState_div`: where the initial-state factor
  does not vanish, the ratio of the observable at two energy transfers equals the ratio of the
  final-state factors, so the energy-transfer dependence at fixed momentum fraction and scale
  measures the final-state factor alone.
* `NuclearEffect.FactorizationHypothesis.finalState_eq_mul`: where the initial-state factor of the
  second split does not vanish, two splits of one observable have final-state factors that differ
  by a factor depending only on `x` and `Q2`.
* `NuclearEffect.FactorizationHypothesis.unique`: two normalised nuclear effects factorising one
  observable, one with a nowhere-vanishing initial-state factor, are equal.
* `IsNormalizedSplit.mul_div`: multiplying the first factor of a normalised split by a nowhere-zero
  `g` tending to one along `l`, and dividing the second by it, gives another normalised split.
* `IsNormalizedSplit.isNormalizedSplit_iff_exists`: without the independence assumption, the
  normalised splits of a nowhere-vanishing observable are exactly `(I * g, F / g)` for
  nowhere-zero `g` tending to one along `l`.
* `IsNormalizedSplit.exists_isNormalizedSplit_ne`: without the independence assumption, for a
  filter eventually avoiding some energy transfer `ν₁` (e.g. `atTop`), a normalised split whose
  first factor is nonzero at `ν₁` admits a second split with a different first factor.

## References

* A. Accardi, F. Arleo, W. K. Brooks, D. D'Enterria and V. Muccifora, *Parton propagation and
  fragmentation in QCD matter*, Riv. Nuovo Cim. 32 (2009) 439, `arXiv:0907.3534`, §2.
* R. Abdul Khalek et al., *Science Requirements and Detector Concepts for the Electron-Ion
  Collider: EIC Yellow Report*, Nucl. Phys. A 1026 (2022) 122447, `arXiv:2103.05419`, §7.3.4.
-/

public section

open Filter Topology

namespace EpsilonEridani
namespace Nuclear
namespace Medium

/-- A nuclear effect on a semi-inclusive observable, split into an initial-state factor and a
final-state factor. The arguments are, in order, the momentum fraction `x`, the hard scale `Q2`,
the energy transfer `ν` and the hadron momentum fraction `z`. The initial-state factor takes only
`x` and `Q2`, so it is independent of the energy transfer and the hadron momentum fraction by
construction. -/
@[ext]
structure NuclearEffect where
  /-- The initial-state factor, a function of the momentum fraction and the scale. -/
  initialState : ℝ → ℝ → ℝ
  /-- The final-state factor, a function of the momentum fraction, the scale, the energy transfer
  and the hadron momentum fraction. -/
  finalState : ℝ → ℝ → ℝ → ℝ → ℝ

namespace NuclearEffect

variable {E E' : NuclearEffect} {obs : ℝ → ℝ → ℝ → ℝ → ℝ} {l : Filter ℝ}

/-- The factorisation hypothesis: the observable `obs` is the product of the initial-state and the
final-state factors of `E`, with no cross term. -/
def FactorizationHypothesis (E : NuclearEffect) (obs : ℝ → ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x Q2 ν z, obs x Q2 ν z = E.initialState x Q2 * E.finalState x Q2 ν z

/-- The final-state factor of `E` tends to one along the filter `l` of energy transfers, at every
momentum fraction, scale and hadron momentum fraction. For `l = atTop` this says that the
final-state effects disappear at large energy transfer; for `l = pure ν₀` it says that the
final-state factor is one at the reference energy transfer `ν₀`. -/
def IsNormalized (E : NuclearEffect) (l : Filter ℝ) : Prop :=
  ∀ x Q2 z, Tendsto (fun ν => E.finalState x Q2 ν z) l (𝓝 1)

/-- Restates the sealed definition `FactorizationHypothesis`. -/
theorem factorizationHypothesis_def :
    E.FactorizationHypothesis obs ↔
      ∀ x Q2 ν z, obs x Q2 ν z = E.initialState x Q2 * E.finalState x Q2 ν z :=
  (Iff.rfl)

/-- Restates the sealed definition `IsNormalized`. -/
theorem isNormalized_def :
    E.IsNormalized l ↔ ∀ x Q2 z, Tendsto (fun ν => E.finalState x Q2 ν z) l (𝓝 1) :=
  (Iff.rfl)

namespace FactorizationHypothesis

/-- Under the factorisation hypothesis, if the final-state factor tends to one along `l`, the
observable tends to the initial-state factor along `l`. The initial-state factor is therefore read
off the observable. -/
theorem tendsto_initialState (h : E.FactorizationHypothesis obs) {x Q2 z : ℝ}
    (hF : Tendsto (fun ν => E.finalState x Q2 ν z) l (𝓝 1)) :
    Tendsto (fun ν => obs x Q2 ν z) l (𝓝 (E.initialState x Q2)) := by
  simpa [h x Q2] using hF.const_mul (E.initialState x Q2)

/-- Two splits of one observable whose final-state factors tend to one along a nontrivial filter
have the same initial-state factor. -/
theorem initialState_eq [l.NeBot] (h : E.FactorizationHypothesis obs)
    (h' : E'.FactorizationHypothesis obs) {x Q2 z : ℝ}
    (hF : Tendsto (fun ν => E.finalState x Q2 ν z) l (𝓝 1))
    (hF' : Tendsto (fun ν => E'.finalState x Q2 ν z) l (𝓝 1)) :
    E.initialState x Q2 = E'.initialState x Q2 :=
  tendsto_nhds_unique (h.tendsto_initialState hF) (h'.tendsto_initialState hF')

/-- Under the factorisation hypothesis, where the initial-state factor does not vanish, the
final-state factor is the observable divided by the initial-state factor. -/
theorem finalState_eq_div (h : E.FactorizationHypothesis obs) {x Q2 : ℝ}
    (hI : E.initialState x Q2 ≠ 0) (ν z : ℝ) :
    E.finalState x Q2 ν z = obs x Q2 ν z / E.initialState x Q2 := by
  rw [h, mul_div_cancel_left₀ _ hI]

/-- Under the factorisation hypothesis, where the initial-state factor does not vanish, the ratio
of the observable at two energy transfers and hadron momentum fractions equals the ratio of the
final-state factors. The initial-state factor drops out, so this dependence measures the
final-state factor alone. -/
theorem div_eq_finalState_div (h : E.FactorizationHypothesis obs) {x Q2 : ℝ}
    (hI : E.initialState x Q2 ≠ 0) (ν z ν' z' : ℝ) :
    obs x Q2 ν z / obs x Q2 ν' z' = E.finalState x Q2 ν z / E.finalState x Q2 ν' z' := by
  rw [h, h, mul_div_mul_left _ _ hI]

/-- Two splits of one observable whose initial-state factors do not vanish at `(x, Q2)` have
final-state factors that differ there by the factor `E.initialState x Q2 / E'.initialState x Q2`,
which depends neither on the energy transfer nor on the hadron momentum fraction. -/
theorem finalState_eq_mul (h : E.FactorizationHypothesis obs)
    (h' : E'.FactorizationHypothesis obs) {x Q2 : ℝ} (hI' : E'.initialState x Q2 ≠ 0)
    (ν z : ℝ) :
    E'.finalState x Q2 ν z =
      E.initialState x Q2 / E'.initialState x Q2 * E.finalState x Q2 ν z := by
  rw [h'.finalState_eq_div hI', h, div_mul_eq_mul_div]

/-- **Uniqueness of the initial-state / final-state decomposition.** Two nuclear effects that
factorise the same observable, whose final-state factors are normalised along the same nontrivial
filter, and one of whose initial-state factors vanishes nowhere, are equal.

The non-vanishing is needed: where the initial-state factor vanishes the observable vanishes
identically in the energy transfer, and the observable leaves the final-state factor there
undetermined (only the normalisation constrains it). -/
theorem unique [l.NeBot] (h : E.FactorizationHypothesis obs) (h' : E'.FactorizationHypothesis obs)
    (hE : E.IsNormalized l) (hE' : E'.IsNormalized l) (hI : ∀ x Q2, E.initialState x Q2 ≠ 0) :
    E = E' := by
  have hII' : E.initialState = E'.initialState := by
    ext x Q2
    exact h.initialState_eq h' (hE x Q2 0) (hE' x Q2 0)
  have hI' (x Q2 : ℝ) : E'.initialState x Q2 ≠ 0 := hII' ▸ hI x Q2
  ext x Q2 ν z
  · rw [hII']
  · rw [h.finalState_eq_div (hI x Q2), h'.finalState_eq_div (hI' x Q2), hII']

end FactorizationHypothesis

end NuclearEffect

/-! ### Splits without the independence assumption -/

/-- `(I, F)` is a normalised split of the observable `obs` along `l` when `obs = I * F` pointwise
and `F` tends to one along `l` in the energy transfer. Unlike a `NuclearEffect`, both factors may
depend on all four variables: the first factor is not assumed independent of the energy
transfer. -/
def IsNormalizedSplit (obs I F : ℝ → ℝ → ℝ → ℝ → ℝ) (l : Filter ℝ) : Prop :=
  (∀ x Q2 ν z, obs x Q2 ν z = I x Q2 ν z * F x Q2 ν z) ∧
    ∀ x Q2 z, Tendsto (fun ν => F x Q2 ν z) l (𝓝 1)

variable {obs I F I' F' : ℝ → ℝ → ℝ → ℝ → ℝ} {l : Filter ℝ}

/-- The pointwise quotient of two functions tending to one tends to one. -/
private theorem tendsto_div_one {f g : ℝ → ℝ} (hf : Tendsto f l (𝓝 1)) (hg : Tendsto g l (𝓝 1)) :
    Tendsto (fun ν => f ν / g ν) l (𝓝 1) := by
  simpa only [Pi.div_def, div_one] using hf.div hg one_ne_zero

/-- Restates the sealed definition `IsNormalizedSplit`. -/
theorem isNormalizedSplit_def :
    IsNormalizedSplit obs I F l ↔ (∀ x Q2 ν z, obs x Q2 ν z = I x Q2 ν z * F x Q2 ν z) ∧
      ∀ x Q2 z, Tendsto (fun ν => F x Q2 ν z) l (𝓝 1) :=
  (Iff.rfl)

/-- A nuclear effect, read as a pair of functions of all four variables, is a normalised split of an
observable exactly when it factorises the observable and is normalised. -/
theorem NuclearEffect.isNormalizedSplit_iff_factorizationHypothesis_and_isNormalized
    (E : NuclearEffect) :
    IsNormalizedSplit obs (fun x Q2 _ _ => E.initialState x Q2) E.finalState l ↔
      E.FactorizationHypothesis obs ∧ E.IsNormalized l :=
  (Iff.rfl)

/-- Multiplying the first factor of a normalised split by a nowhere-zero `g` that tends to one
along `l` in the energy transfer, and dividing the second factor by it, gives another normalised
split of the same observable. -/
theorem IsNormalizedSplit.mul_div (h : IsNormalizedSplit obs I F l)
    {g : ℝ → ℝ → ℝ → ℝ → ℝ} (hg₀ : ∀ x Q2 ν z, g x Q2 ν z ≠ 0)
    (hg : ∀ x Q2 z, Tendsto (fun ν => g x Q2 ν z) l (𝓝 1)) :
    IsNormalizedSplit obs (fun x Q2 ν z => I x Q2 ν z * g x Q2 ν z)
      (fun x Q2 ν z => F x Q2 ν z / g x Q2 ν z) l := by
  refine ⟨fun x Q2 ν z => ?_, fun x Q2 z => tendsto_div_one (h.2 x Q2 z) (hg x Q2 z)⟩
  rw [h.1]
  field_simp [hg₀ x Q2 ν z]

/-- **The normalised splits without the independence assumption.** Let `(I, F)` be a normalised
split of an observable that vanishes nowhere. Then `(I', F')` is another normalised split of it
exactly when `I' = I * g` and `F' = F / g` for some nowhere-zero `g` that tends to one along `l` in
the energy transfer. Any `g` that depends on the energy transfer gives an `I'` that does too. -/
theorem IsNormalizedSplit.isNormalizedSplit_iff_exists (h : IsNormalizedSplit obs I F l)
    (hobs : ∀ x Q2 ν z, obs x Q2 ν z ≠ 0) :
    IsNormalizedSplit obs I' F' l ↔
      ∃ g : ℝ → ℝ → ℝ → ℝ → ℝ, (∀ x Q2 ν z, g x Q2 ν z ≠ 0) ∧
        (∀ x Q2 z, Tendsto (fun ν => g x Q2 ν z) l (𝓝 1)) ∧
        (∀ x Q2 ν z, I' x Q2 ν z = I x Q2 ν z * g x Q2 ν z) ∧
        ∀ x Q2 ν z, F' x Q2 ν z = F x Q2 ν z / g x Q2 ν z := by
  obtain ⟨hprod, hF⟩ := h
  have hF₀ (x Q2 ν z : ℝ) : F x Q2 ν z ≠ 0 :=
    right_ne_zero_of_mul (hprod x Q2 ν z ▸ hobs x Q2 ν z)
  constructor
  · rintro ⟨hprod', hF'⟩
    have hF'₀ (x Q2 ν z : ℝ) : F' x Q2 ν z ≠ 0 :=
      right_ne_zero_of_mul (hprod' x Q2 ν z ▸ hobs x Q2 ν z)
    refine ⟨fun x Q2 ν z => F x Q2 ν z / F' x Q2 ν z, fun x Q2 ν z => ?_, fun x Q2 z => ?_,
      fun x Q2 ν z => ?_, fun x Q2 ν z => ?_⟩
    · exact div_ne_zero (hF₀ x Q2 ν z) (hF'₀ x Q2 ν z)
    · exact tendsto_div_one (hF x Q2 z) (hF' x Q2 z)
    · rw [mul_div_assoc', ← hprod, hprod', mul_div_cancel_right₀ _ (hF'₀ x Q2 ν z)]
    · rw [div_div_cancel₀ (hF₀ x Q2 ν z)]
  · rintro ⟨g, hg₀, hg, hI', hF'⟩
    obtain rfl : I' = fun x Q2 ν z => I x Q2 ν z * g x Q2 ν z := by ext; exact hI' ..
    obtain rfl : F' = fun x Q2 ν z => F x Q2 ν z / g x Q2 ν z := by ext; exact hF' ..
    exact IsNormalizedSplit.mul_div ⟨hprod, hF⟩ hg₀ hg

/-- **The split is not unique without the independence assumption.** Let `l` eventually avoid the
energy transfer `ν₁`; for `l = atTop` this holds for every `ν₁`. Every normalised split `(I, F)`
whose first factor is nonzero at some point with energy transfer `ν₁` has a second normalised split
`(I', F')` of the same observable with `I' ≠ I`. -/
theorem IsNormalizedSplit.exists_isNormalizedSplit_ne (h : IsNormalizedSplit obs I F l) {ν₁ : ℝ}
    (hν₁ : ∀ᶠ ν in l, ν ≠ ν₁) {x₀ Q2₀ z₀ : ℝ} (hI : I x₀ Q2₀ ν₁ z₀ ≠ 0) :
    ∃ I' F' : ℝ → ℝ → ℝ → ℝ → ℝ, IsNormalizedSplit obs I' F' l ∧ I' ≠ I := by
  let g : ℝ → ℝ := fun ν => if ν = ν₁ then 2 else 1
  have hg₀ (ν : ℝ) : g ν ≠ 0 := by unfold g; split_ifs <;> norm_num
  have hg : g =ᶠ[l] fun _ => 1 := hν₁.mono fun ν hν => by simp [g, hν]
  refine ⟨_, _, h.mul_div (g := fun _ _ ν _ => g ν) (fun _ _ ν _ => hg₀ ν)
    (fun _ _ _ => tendsto_const_nhds.congr' hg.symm), fun hII => ?_⟩
  have := congr_fun (congr_fun (congr_fun (congr_fun hII x₀) Q2₀) ν₁) z₀
  simp only [g, ite_true] at this
  exact hI (by linarith)

end Medium
end Nuclear
end EpsilonEridani
