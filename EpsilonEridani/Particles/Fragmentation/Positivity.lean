/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Fragmentation.MomentumSumRule
public import EpsilonEridani.Particles.Parton.PDF.SpinDensityC

/-!
# Positivity bounds for the fragmentation into a spin-1/2 hadron

At fixed hadron species `h`, parton flavour `i`, momentum fraction `z` and scale `Q²`, the
fragmentation of a quark into a spin-1/2 hadron (a `Λ` hyperon, say) is described by a `4 × 4`
hermitian matrix in the helicity basis `idxPP, idxPM, idxMP, idxMM` of
`EpsilonEridani.Particles.Parton.PDF.SpinDensity`, read with the produced hadron in place of the
nucleon: the index `(Λ, λ)` is the pair of hadron and quark helicity. The diagonal entry at
`(Λ, λ)` is the number density in `z` of hadrons of helicity `Λ` produced by a quark of helicity
`λ`, and the double-helicity-flip entry is the transversity transfer.

The matrix is a sum over the unobserved final states `X` accompanying the hadron of products of
amplitudes `⟨h X| ψ̄ |0⟩`, so it is positive semidefinite: this is
`EpsilonEridani.Particles.Parton.PDF.SpinDensityC.ofAmplitudes`, and conversely every positive
semidefinite helicity matrix is such a sum (`SpinDensityC.exists_eq_ofAmplitudes`). A family of
such matrices is therefore a family of `SpinDensityC`, and the three leading-twist collinear
fragmentation functions are read off it with the normalisations of the distribution case:

* the unpolarized fragmentation function `D₁` (`fragOfSpinDensity`), averaged over the quark
  helicity and summed over the hadron helicity;
* the longitudinal spin transfer `G₁L` (`helicityFragOfSpinDensity`), the helicity-weighted
  combination of the diagonal entries;
* the transverse spin transfer `H₁` (`transversityFragOfSpinDensity`), the double-flip entry,
  complex in general. It is real under parity invariance
  (`SpinDensityC.IsParityInvariant.im_transversity`); no time-reversal argument is available
  here, since in a fragmentation correlator the hadron is an out-state.

Positive semidefiniteness alone gives the fragmentation analogues of the distribution bounds:
`D₁ ≥ 0` (`fragOfSpinDensity_nonneg`), `|G₁L| ≤ D₁` (`abs_helicityFrag_le_frag`), the Soffer-type
bound `2 ‖H₁‖ ≤ D₁ + G₁L` (`soffer_bound_frag`) and `‖H₁‖ ≤ D₁`
(`norm_transversityFrag_le_frag`). Consequently the `nonneg` field of
`EpsilonEridani.Particles.Fragmentation.Assumptions` is a theorem for `D₁`, which satisfies the
bundle exactly when it has the support property (`assumptions_fragOfSpinDensity_iff`); the support
of `D₁` is inherited by `G₁L` and `H₁`
(`helicityFragOfSpinDensity_eq_zero_of_notMem_unitInterval`,
`transversityFragOfSpinDensity_eq_zero_of_notMem_unitInterval`). Under the momentum sum rule for
`D₁`, the first moment of `G₁L` of each hadron species is at most one in absolute value
(`MomentumSumRule.abs_zMoment_one_helicityFrag_le_one`).

Every statement is at fixed `(z, Q²)` or, for the moments, at fixed `Q²`, and nothing here claims
that the bounds survive evolution.

## References

* A. Bacchetta, M. Boglione, A. Henneman and P. J. Mulders, *Bounds on transverse momentum
  dependent distribution and fragmentation functions*, Phys. Rev. Lett. **85** (2000) 712
  (arXiv:hep-ph/9912490).
* A. Metz and A. Vossen, *Parton fragmentation functions*, Prog. Part. Nucl. Phys. **91** (2016)
  136 (arXiv:1607.02521), §2.
* J. Soffer, *Positivity constraints for spin-dependent parton distributions*,
  Phys. Rev. Lett. **74** (1995) 1292 (arXiv:hep-ph/9409254).
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Fragmentation

open Parton.PDF (SpinDensityC)

variable {Hadron Flavor : Type} (ρ : Hadron → Flavor → ℝ → ℝ → SpinDensityC)

/-! ### The leading-twist fragmentation functions of a helicity-matrix family -/

/-- The unpolarized fragmentation function `D₁` of a family of fragmentation helicity matrices,
indexed by hadron species, parton flavour, `z` and `Q²`. -/
def fragOfSpinDensity : Frag Hadron Flavor :=
  fun h i z Q2 => (ρ h i z Q2).f1

/-- The longitudinal spin-transfer fragmentation function `G₁L` of a family of fragmentation
helicity matrices. It has the index conventions of `Frag` but is not non-negative. -/
def helicityFragOfSpinDensity : Frag Hadron Flavor :=
  fun h i z Q2 => (ρ h i z Q2).deltaQ

/-- The transverse spin-transfer fragmentation function `H₁` of a family of fragmentation
helicity matrices, the complex double-helicity-flip entry. -/
def transversityFragOfSpinDensity : Hadron → Flavor → ℝ → ℝ → ℂ :=
  fun h i z Q2 => (ρ h i z Q2).transversity

@[simp]
lemma fragOfSpinDensity_apply (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    fragOfSpinDensity ρ h i z Q2 = (ρ h i z Q2).f1 := (rfl)

@[simp]
lemma helicityFragOfSpinDensity_apply (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    helicityFragOfSpinDensity ρ h i z Q2 = (ρ h i z Q2).deltaQ := (rfl)

@[simp]
lemma transversityFragOfSpinDensity_apply (h : Hadron) (i : Flavor) (z Q2 : ℝ) :
    transversityFragOfSpinDensity ρ h i z Q2 = (ρ h i z Q2).transversity := (rfl)

/-! ### Pointwise positivity bounds -/

section Pointwise

variable (h : Hadron) (i : Flavor) (z Q2 : ℝ)

/-- **Positivity of `D₁`.** The unpolarized fragmentation function of a helicity-matrix family is
non-negative, at every `z`; compare the `nonneg` field of `Assumptions`, which posits it. -/
theorem fragOfSpinDensity_nonneg : 0 ≤ fragOfSpinDensity ρ h i z Q2 :=
  (ρ h i z Q2).f1_nonneg

/-- **Spin-transfer dominance.** `|G₁L| ≤ D₁` at fixed `(z, Q²)`. -/
theorem abs_helicityFrag_le_frag :
    |helicityFragOfSpinDensity ρ h i z Q2| ≤ fragOfSpinDensity ρ h i z Q2 :=
  (ρ h i z Q2).abs_deltaQ_le_f1

/-- **The Soffer-type bound for fragmentation.** `2 ‖H₁‖ ≤ D₁ + G₁L` at fixed `(z, Q²)`, from
positive semidefiniteness alone. -/
theorem soffer_bound_frag :
    2 * ‖transversityFragOfSpinDensity ρ h i z Q2‖ ≤
      fragOfSpinDensity ρ h i z Q2 + helicityFragOfSpinDensity ρ h i z Q2 :=
  (ρ h i z Q2).soffer_bound

/-- The transverse spin transfer is bounded by the unpolarized fragmentation function:
`‖H₁‖ ≤ D₁` at fixed `(z, Q²)`. -/
theorem norm_transversityFrag_le_frag :
    ‖transversityFragOfSpinDensity ρ h i z Q2‖ ≤ fragOfSpinDensity ρ h i z Q2 :=
  (ρ h i z Q2).norm_transversity_le_f1

end Pointwise

/-! ### The assumption bundle and support -/

/-- **`D₁` satisfies `Assumptions` exactly when it has the support property.** The `nonneg` field
is discharged by `fragOfSpinDensity_nonneg`, so the support postulate is the only content of the
bundle for a helicity-matrix family. -/
theorem assumptions_fragOfSpinDensity_iff :
    Assumptions (fragOfSpinDensity ρ) ↔
      ∀ h i z Q2, z < 0 ∨ 1 < z → fragOfSpinDensity ρ h i z Q2 = 0 :=
  ⟨fun hD => hD.support, fun hs =>
    { support := hs
      nonneg := fun h i z Q2 _ _ => fragOfSpinDensity_nonneg ρ h i z Q2 }⟩

variable {ρ}

/-- The longitudinal spin transfer vanishes outside the unit interval when `D₁` satisfies
`Assumptions`. -/
theorem helicityFragOfSpinDensity_eq_zero_of_notMem_unitInterval
    (hD : Assumptions (fragOfSpinDensity ρ)) (h : Hadron) (i : Flavor) {z : ℝ} (Q2 : ℝ)
    (hz : z < 0 ∨ 1 < z) : helicityFragOfSpinDensity ρ h i z Q2 = 0 :=
  (ρ h i z Q2).deltaQ_eq_zero_of_f1_eq_zero (hD.support h i z Q2 hz)

/-- The transverse spin transfer vanishes outside the unit interval when `D₁` satisfies
`Assumptions`. -/
theorem transversityFragOfSpinDensity_eq_zero_of_notMem_unitInterval
    (hD : Assumptions (fragOfSpinDensity ρ)) (h : Hadron) (i : Flavor) {z : ℝ} (Q2 : ℝ)
    (hz : z < 0 ∨ 1 < z) : transversityFragOfSpinDensity ρ h i z Q2 = 0 :=
  (ρ h i z Q2).transversity_eq_zero_of_f1_eq_zero (hD.support h i z Q2 hz)

/-! ### Moments -/

/-- **The first moment of the longitudinal spin transfer is bounded by one.** Under the momentum
sum rule for `D₁`, the first `z`-moment of `G₁L` of each hadron species lies in `[-1, 1]`: it is
dominated by the first moment of `D₁` of that species, which is at most the total momentum of the
fragmenting parton. -/
theorem MomentumSumRule.abs_zMoment_one_helicityFrag_le_one [Fintype Hadron]
    (hsum : MomentumSumRule (fragOfSpinDensity ρ)) (h : Hadron) (i : Flavor) (Q2 : ℝ) :
    |zMoment (helicityFragOfSpinDensity ρ) 1 h i Q2| ≤ 1 := by
  obtain ⟨hint, hone⟩ := (momentumSumRule_iff _).1 hsum i Q2
  refine (abs_zMoment_le (by simpa only [pow_one] using hint h)
    fun z _ => abs_helicityFrag_le_frag ρ h i z Q2).trans ?_
  exact zMoment_one_le_one_of_sum_eq_one hone
    (fun h' => zMoment_nonneg (fun z _ => fragOfSpinDensity_nonneg ρ h' i z Q2) 1) h

end Fragmentation
end Particles
end EpsilonEridani
