/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Particles.Fragmentation.Basic

/-!
# The momentum sum rule for fragmentation functions

A fragmentation function `D_h^i(z, Q²)` is a number density in the momentum fraction `z` of the
observed hadron `h` in the fragmenting parton `i`. Its first moment `∫₀¹ dz z D_h^i(z, Q²)` is the
fraction of the parton's light-cone momentum carried by hadrons of species `h`. The momentum sum
rule states that, summed over all hadron species, this fraction is one:

`∑_h ∫₀¹ dz z D_h^i(z, Q²) = 1` for every flavour `i` and every scale `Q²`.

The Bochner integral `zMoment` assigns `0` to a non-integrable integrand, so a species whose
momentum fraction diverges would contribute `0` to the sum. `MomentumSumRule` therefore also
requires each first-moment integrand `z D_h^i(z, Q²)` to be integrable on `[0, 1]`, which is what
makes the sum of the displayed identity a sum of finite momentum fractions.

The species sum is a `Finset.univ` sum over a `Fintype` species type. The identity is physically
justified only when that type is complete for the final-state sum, and this file does not assume
completeness: `MomentumSumRule` is the identity itself.

## Main definitions

* `Fragmentation.MomentumSumRule D`: the momentum sum rule for the family `D`.
* `Fragmentation.twoSpeciesFrag`, `Fragmentation.powerFrag`: explicit fragmentation families,
  built with `Fragmentation.extendByZero`.

## Main results

* `Fragmentation.MomentumSumRule.zMoment_one_le_one`: under the sum rule, the first moment of each
  species is at most one. This needs only non-negativity, not completeness.
* `Fragmentation.momentumSumRule_twoSpeciesFrag` and
  `Fragmentation.not_momentumSumRule_single_twoSpeciesFrag`: for `D₀(z) = 2z` and
  `D₁(z) = 2(1 - z)` the sum rule holds for the pair and fails for each member alone, so the sum
  rule is not a per-species statement.
* `Fragmentation.exists_momentumSumRule_not_integrableOn`: a family satisfying `Assumptions` and the
  momentum sum rule whose zeroth moment `∫₀¹ dz D(z)` diverges, namely `D(z) = 1/z`. No
  multiplicity sum rule follows from the definitions.
* `Fragmentation.zMoment_zero_powerFrag`: the families `(n + 2) zⁿ` all satisfy the momentum sum
  rule, and their multiplicities `(n + 2)/(n + 1)` are finite but depend on `n`.

## References

* J. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), §12.4.
* A. Metz and A. Vossen, *Parton fragmentation functions*, Prog. Part. Nucl. Phys. 91 (2016) 136,
  `arXiv:1607.02521`, §2.
-/

public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani
namespace Particles
namespace Fragmentation

variable {Hadron Flavor : Type}

/-! ### The momentum sum rule -/

/-- The momentum sum rule: for every parton flavour `i` and scale `Q2`, the first-moment integrand
of every hadron species is integrable on the unit interval, and the first moments of the
fragmentation functions into all hadron species sum to one. -/
def MomentumSumRule [Fintype Hadron] (D : Frag Hadron Flavor) : Prop :=
  ∀ (i : Flavor) (Q2 : ℝ),
    (∀ h, IntegrableOn (fun z => z * D h i z Q2) (Icc 0 1)) ∧ ∑ h, zMoment D 1 h i Q2 = 1

/-- Unfolding lemma for `MomentumSumRule`. -/
@[simp]
lemma momentumSumRule_iff [Fintype Hadron] (D : Frag Hadron Flavor) :
    MomentumSumRule D ↔ ∀ (i : Flavor) (Q2 : ℝ),
      (∀ h, IntegrableOn (fun z => z * D h i z Q2) (Icc 0 1)) ∧ ∑ h, zMoment D 1 h i Q2 = 1 :=
  (Iff.rfl)

/-- For a single species, the momentum sum rule says that its first moment is the integral of an
integrable function and equals one. -/
lemma momentumSumRule_iff_of_unique [Unique Hadron] (D : Frag Hadron Flavor) :
    MomentumSumRule D ↔ ∀ (i : Flavor) (Q2 : ℝ),
      IntegrableOn (fun z => z * D default i z Q2) (Icc 0 1) ∧ zMoment D 1 default i Q2 = 1 := by
  simp [momentumSumRule_iff, Unique.forall_iff]

/-- Under the momentum sum rule, for a family that is non-negative on the unit interval, each
species carries at most the whole momentum of the fragmenting parton. -/
theorem MomentumSumRule.zMoment_one_le_one [Fintype Hadron] {D : Frag Hadron Flavor}
    (hsum : MomentumSumRule D) {i : Flavor} {Q2 : ℝ}
    (hD : ∀ h', ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ D h' i z Q2) (h : Hadron) : zMoment D 1 h i Q2 ≤ 1 :=
  ((momentumSumRule_iff D).1 hsum i Q2).2 ▸ Finset.single_le_sum
    (fun h' _ => zMoment_nonneg (hD h') 1) (Finset.mem_univ h)

/-! ### The sum rule is not a per-species statement -/

/-- The two-species family `D₀(z) = 2z`, `D₁(z) = 2(1 - z)` on the unit interval, extended by
zero, for a single parton flavour. -/
def twoSpeciesFrag : Frag (Fin 2) Unit :=
  extendByZero fun h _ z _ => ![2 * z, 2 * (1 - z)] h

/-- Unfolding lemma for `twoSpeciesFrag`. -/
lemma twoSpeciesFrag_def :
    twoSpeciesFrag = extendByZero fun h _ z _ => ![2 * z, 2 * (1 - z)] h :=
  (rfl)

/-- The two-species family satisfies `Assumptions`. -/
lemma assumptions_twoSpeciesFrag : Assumptions twoSpeciesFrag :=
  assumptions_extendByZero fun h _ z _ hz₀ hz₁ => by
    fin_cases h <;> simp <;> linarith

/-- The species `0` of `twoSpeciesFrag` carries two thirds of the momentum. -/
lemma zMoment_one_twoSpeciesFrag_zero (Q2 : ℝ) : zMoment twoSpeciesFrag 1 0 () Q2 = 2 / 3 := by
  rw [twoSpeciesFrag_def, zMoment_extendByZero, zMoment_eq_intervalIntegral]
  simp only [Matrix.cons_val_zero, pow_one]
  have : ∀ z : ℝ, z * (2 * z) = 2 * z ^ 2 := fun z => by ring
  simp only [this, intervalIntegral.integral_const_mul, integral_pow]
  norm_num

/-- The species `1` of `twoSpeciesFrag` carries one third of the momentum. -/
lemma zMoment_one_twoSpeciesFrag_one (Q2 : ℝ) : zMoment twoSpeciesFrag 1 1 () Q2 = 1 / 3 := by
  rw [twoSpeciesFrag_def, zMoment_extendByZero, zMoment_eq_intervalIntegral]
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, pow_one]
  have : ∀ z : ℝ, z * (2 * (1 - z)) = 2 * z ^ 1 - 2 * z ^ 2 := fun z => by ring
  simp only [this]
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const_mul, integral_pow]
  norm_num

/-- The two-species family satisfies the momentum sum rule: `2/3 + 1/3 = 1`. -/
theorem momentumSumRule_twoSpeciesFrag : MomentumSumRule twoSpeciesFrag := by
  refine (momentumSumRule_iff _).2 fun _ Q2 => ⟨fun h => ?_, ?_⟩
  · rw [twoSpeciesFrag_def, integrableOn_mul_extendByZero_iff]
    fin_cases h <;>
      simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] <;>
      exact Continuous.integrableOn_Icc (by fun_prop)
  · rw [Fin.sum_univ_two, zMoment_one_twoSpeciesFrag_zero, zMoment_one_twoSpeciesFrag_one]
    norm_num

/-- Neither member of the two-species family satisfies the momentum sum rule on its own. -/
theorem not_momentumSumRule_single_twoSpeciesFrag (h : Fin 2) :
    ¬ MomentumSumRule (fun _ : Unit => twoSpeciesFrag h) := by
  have key : ∀ h : Fin 2, zMoment twoSpeciesFrag 1 h () 0 ≠ 1 := by
    rw [Fin.forall_fin_two, zMoment_one_twoSpeciesFrag_zero, zMoment_one_twoSpeciesFrag_one]
    norm_num
  rw [momentumSumRule_iff_of_unique]
  exact fun hsum => key h (hsum () 0).2

/-! ### No multiplicity sum rule -/

/-- The one-species family `D(z) = 1/z` on the unit interval, extended by zero. It carries the
whole momentum of the parton but has a divergent multiplicity. -/
private def invFrag : Frag Unit Unit :=
  extendByZero fun _ _ z _ => z⁻¹

/-- `invFrag` satisfies `Assumptions`. -/
private lemma assumptions_invFrag : Assumptions invFrag :=
  assumptions_extendByZero fun _ _ _ _ hz₀ _ => inv_nonneg.2 hz₀

/-- `invFrag` satisfies the momentum sum rule: `∫₀¹ dz z · z⁻¹ = 1`. -/
private theorem momentumSumRule_invFrag : MomentumSumRule invFrag := by
  rw [momentumSumRule_iff_of_unique]
  refine fun _ Q2 => ⟨?_, ?_⟩
  · rw [invFrag, integrableOn_mul_extendByZero_iff, integrableOn_Icc_iff_integrableOn_Ioc,
      integrableOn_congr_fun (g := fun _ => (1 : ℝ)) (fun z hz => mul_inv_cancel₀ hz.1.ne')
        measurableSet_Ioc]
    exact integrableOn_const measure_Ioc_lt_top.ne
  rw [invFrag, zMoment_extendByZero, zMoment_eq_intervalIntegral]
  calc ∫ z in (0 : ℝ)..1, z ^ 1 * z⁻¹ = ∫ _ in (0 : ℝ)..1, (1 : ℝ) :=
        intervalIntegral.integral_congr_ae <| Filter.Eventually.of_forall fun z hz => by
          rw [uIoc_of_le zero_le_one] at hz
          simp [hz.1.ne']
    _ = 1 := by simp

/-- The zeroth moment of `invFrag` is not the integral of an integrable function: its
multiplicity `∫₀¹ dz / z` diverges. -/
private theorem not_integrableOn_invFrag (Q2 : ℝ) :
    ¬ IntegrableOn (fun z => invFrag () () z Q2) (Icc 0 1) := by
  rw [invFrag, integrableOn_congr_fun (g := fun z : ℝ => z⁻¹)
    (fun z hz => extendByZero_of_mem _ hz () () Q2) measurableSet_Icc,
    integrableOn_Icc_iff_integrableOn_Ioc, ← intervalIntegrable_iff_integrableOn_Ioc_of_le
      zero_le_one, intervalIntegrable_inv_iff]
  simp

/-- No multiplicity sum rule follows from the definitions: some family satisfying `Assumptions`
and the momentum sum rule has a divergent zeroth moment at every scale. -/
theorem exists_momentumSumRule_not_integrableOn :
    ∃ D : Frag Unit Unit, Assumptions D ∧ MomentumSumRule D ∧
      ∀ Q2, ¬ IntegrableOn (fun z => D () () z Q2) (Icc 0 1) :=
  ⟨invFrag, assumptions_invFrag, momentumSumRule_invFrag, not_integrableOn_invFrag⟩

/-! ### Power-law families -/

/-- The one-species family `D(z) = (n + 2) zⁿ` on the unit interval, extended by zero. The
normalisation `n + 2` is the one for which the first moment is one. -/
def powerFrag (n : ℕ) : Frag Unit Unit :=
  extendByZero fun _ _ z _ => (n + 2) * z ^ n

/-- Unfolding lemma for `powerFrag`. -/
lemma powerFrag_def (n : ℕ) : powerFrag n = extendByZero fun _ _ z _ => (n + 2) * z ^ n :=
  (rfl)

/-- `powerFrag n` satisfies `Assumptions`. -/
lemma assumptions_powerFrag (n : ℕ) : Assumptions (powerFrag n) :=
  assumptions_extendByZero fun _ _ _ _ hz₀ _ => by positivity

/-- The `k`-th moment of `powerFrag n` is `(n + 2)/(k + n + 1)`. -/
lemma zMoment_powerFrag (n k : ℕ) (Q2 : ℝ) :
    zMoment (powerFrag n) k () () Q2 = (n + 2) / (k + n + 1) := by
  rw [powerFrag_def, zMoment_extendByZero, zMoment_eq_intervalIntegral]
  have : ∀ z : ℝ, z ^ k * ((n + 2) * z ^ n) = (n + 2) * z ^ (k + n) := fun z => by ring
  simp only [this, intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-- Every `powerFrag n` satisfies the momentum sum rule. -/
theorem momentumSumRule_powerFrag (n : ℕ) : MomentumSumRule (powerFrag n) := by
  rw [momentumSumRule_iff_of_unique]
  refine fun _ Q2 => ⟨?_, ?_⟩
  · rw [powerFrag_def, integrableOn_mul_extendByZero_iff]
    exact Continuous.integrableOn_Icc (by fun_prop)
  rw [zMoment_powerFrag]
  have : (n : ℝ) + 2 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

/-- The multiplicity of `powerFrag n` is `(n + 2)/(n + 1)`: finite, but dependent on `n`, although
every member satisfies the momentum sum rule. -/
theorem zMoment_zero_powerFrag (n : ℕ) (Q2 : ℝ) :
    zMoment (powerFrag n) 0 () () Q2 = (n + 2) / (n + 1) := by
  rw [zMoment_powerFrag]
  push_cast
  ring_nf

end Fragmentation
end Particles
end EpsilonEridani
