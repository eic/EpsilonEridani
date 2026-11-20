/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.StrongLaw

/-!
# The Monte Carlo average of draws with a given law

For draws `X i : Ω → α` that each have law `ν`, and a `ν`-integrable observable `φ` with values
in a Banach space, the Monte Carlo average `(1/n) ∑_{i < n} φ (X i)` estimates `∫ φ dν`:

* `integral_inv_smul_sum`: the average is unbiased for every sample size `n ≥ 1`, whether or not
  the draws are independent.
* `ae_tendsto_inv_smul_sum`: for pairwise independent draws the average converges to `∫ φ dν`
  almost surely. This is Mathlib's strong law of large numbers (`ProbabilityTheory.strong_law_ae`)
  restated through the law of the draws (`ProbabilityTheory.HasLaw`) rather than through
  identically distributed observables.
-/

public section

open MeasureTheory ProbabilityTheory Filter Finset Function
open scoped Topology

namespace EpsilonEridani.MonteCarlo

variable {α Ω E : Type*} [MeasurableSpace α] [MeasurableSpace Ω] {P : Measure Ω}
  {X : ℕ → Ω → α} {ν : Measure α} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : α → E}

/-- **The Monte Carlo average is unbiased for every sample size.** For draws `X i` with law `ν`
and a `ν`-integrable `φ`, the average of `φ` over the first `n ≥ 1` draws has expectation
`∫ φ dν`. No independence is needed. -/
theorem integral_inv_smul_sum (hφ : Integrable φ ν) (hX : ∀ i, HasLaw (X i) ν P) {n : ℕ}
    (hn : n ≠ 0) :
    ∫ ω, (n : ℝ)⁻¹ • ∑ i ∈ range n, φ (X i ω) ∂P = ∫ x, φ x ∂ν := by
  rw [integral_smul, integral_finsetSum _ fun i _ => (hX i).integrable_fun_comp hφ]
  have hi : ∀ i, ∫ ω, φ (X i ω) ∂P = ∫ x, φ x ∂ν := fun i => (hX i).integral_comp hφ.1
  rw [Finset.sum_congr rfl fun i _ => hi i, sum_const, card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

/-- **The Monte Carlo average converges almost surely.** For pairwise independent draws `X i`
with law `ν` and a `ν`-integrable `φ`, the average `(1/n) ∑_{i < n} φ (X i)` converges almost
surely to `∫ φ dν`. This is Mathlib's strong law of large numbers applied to `φ ∘ X i`. -/
theorem ae_tendsto_inv_smul_sum [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (hφ : Integrable φ ν) (hX : ∀ i, HasLaw (X i) ν P) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on X)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ i ∈ range n, φ (X i ω)) atTop
      (𝓝 (∫ x, φ x ∂ν)) := by
  have hφm : ∀ i, AEMeasurable φ (P.map (X i)) := fun i => by
    rw [(hX i).map_eq]
    exact hφ.aemeasurable
  have key := strong_law_ae (fun i => φ ∘ X i) ((hX 0).integrable_comp hφ)
    (fun i j hij => (hindep hij).comp₀ (hX i).aemeasurable (hX j).aemeasurable (hφm i) (hφm j))
    fun i => ((hX i).identDistrib (hX 0)).comp_of_aemeasurable (hφm i)
  rw [(hX 0).integral_comp hφ.1] at key
  simpa only [Function.comp_apply] using key

end EpsilonEridani.MonteCarlo
