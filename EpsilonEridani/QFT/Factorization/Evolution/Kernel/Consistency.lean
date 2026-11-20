/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.HarmonicSum.Asymptotics
public import EpsilonEridani.QFT.Factorization.Evolution.Kernel.LeadingOrder

/-!
# Consistency relations of the leading-order splitting kernels

Two checks on the coefficients of the leading-order kernels `pqq`, `pgq`, `pqgSinglet`, `pgg`
beyond the conservation identities proved with them.

**The supersymmetric relation.** At the supersymmetric point `C_F = C_A = 2 n_f T_F`
(`EpsilonEridani.QFT.QCD.ColorFactors.IsSupersymmetric`) the quark column and the gluon column of
the singlet kernel matrix have the same sum:

  `P_qq + P_gq = 2 n_f P_qg + P_gg`

as distributions on the momentum-fraction interval. The plus coefficients `2 C_F` and `2 C_A`
agree, the delta coefficients `(3/2) C_F` and `β₀ / 2` agree because `β₀ = 3 C_A` there, and the
regular parts add up to the same function. In moment space this is
`γ_qq(N) + γ_gq(N) - γ_qg(N) - γ_gg(N) = 0` at every real `N > 1`. Unlike the momentum identities,
which hold at `N = 2` for every choice of colour factors, it constrains the kernels at every `N`:
changing a single coefficient of one of the four kernels breaks it.

**Large-`N` behaviour of the diagonal moments.** The moments `γ_qq(N)` and `γ_gg(N)` fall like
`-2 C log N`, with `C` the colour charge of the radiating parton, as the coefficients `2 C_F` and
`2 C_A` of `[1 / (1 - z)]₊` dictate:

  `γ_qq(N) = -2 C_F (log N + γ_E) + (3/2) C_F + O(1/N)`,
  `γ_gg(N) = -2 C_A (log N + γ_E) + β₀ / 2 + O(1/N)`,

with `γ_E` the Euler–Mascheroni constant. The growth is only logarithmic, so evolution changes
high moments, which govern the large-momentum-fraction region, slowly.

## Main results

* `pairing_pqq_add_pairing_pgq`: the supersymmetric relation for the pairing with any test
  function `φ` for which `φ z / z` is integrable on `[0, 1]`.
* `moment_pqq_add_moment_pgq`: the supersymmetric relation for the moments, at every real
  `N > 1`.
* `isBigO_moment_pqq_add_log_inv`, `isBigO_moment_pgg_add_log_inv`: the large-`N` expansions
  of the diagonal moments.

## References

* Yu. L. Dokshitzer, *Calculation of the structure functions for deep inelastic scattering and
  e⁺e⁻ annihilation by perturbation theory in quantum chromodynamics*, Sov. Phys. JETP 46 (1977)
  641, for the supersymmetric relation.
* I. Antoniadis and E. G. Floratos, *On the evolution equations of supersymmetric QCD*, Nucl.
  Phys. B 191 (1981) 217.
* R. K. Ellis, W. J. Stirling and B. R. Webber, *QCD and Collider Physics*, Cambridge University
  Press (1996), §4.3, for the large-`N` behaviour.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

open MeasureTheory Set Filter Asymptotics QCD

variable {c : ColorFactors}

/-! ### The supersymmetric relation -/

/-- **The supersymmetric relation as distributions.** At the supersymmetric point
`C_F = C_A = 2 n_f T_F`, `P_qq + P_gq = 2 n_f P_qg + P_gg`: the two pair equally with every test
function `φ` for which `φ z / z` is integrable on `[0, 1]`, which makes the `1 / z` singularities
of `P_gq` and `P_gg` integrable against `φ`. -/
theorem pairing_pqq_add_pairing_pgq (hc : c.IsSupersymmetric) {φ : ℝ → ℝ}
    (hφ : IntervalIntegrable (fun z => φ z / z) volume 0 1) :
    (pqq c).pairing φ + (pgq c).pairing φ = (pqgSinglet c).pairing φ + (pgg c).pairing φ := by
  have hφ' : IntervalIntegrable φ volume 0 1 :=
    (hφ.continuousOn_mul (g := fun z => z) continuousOn_id).congr fun z hz => by
      rw [uIoc_of_le zero_le_one] at hz
      field_simp [hz.1.ne']
  have hqq : IntervalIntegrable (fun z => (pqq c).regular z * φ z) volume 0 1 := by
    simpa only [pqq_regular] using
      hφ'.continuousOn_mul (g := fun z => -c.cF * (1 + z)) (by fun_prop)
  have hgq : IntervalIntegrable (fun z => (pgq c).regular z * φ z) volume 0 1 :=
    (hφ.continuousOn_mul (g := fun z => c.cF * (1 + (1 - z) ^ 2)) (by fun_prop)).congr
      fun z _ => by simp only [pgq_regular]; ring
  have hqg : IntervalIntegrable (fun z => (pqgSinglet c).regular z * φ z) volume 0 1 := by
    simpa only [pqgSinglet_regular] using
      hφ'.continuousOn_mul (g := fun z => 2 * c.nF * c.tF * (z ^ 2 + (1 - z) ^ 2)) (by fun_prop)
  have hgg : IntervalIntegrable (fun z => (pgg c).regular z * φ z) volume 0 1 :=
    ((hφ'.continuousOn_mul (g := fun z => 2 * c.cA * (-1 + z * (1 - z))) (by fun_prop)).add
      (hφ.continuousOn_mul (g := fun z => 2 * c.cA * (1 - z)) (by fun_prop))).congr
      fun z _ => by simp only [pgg_regular]; ring
  -- The regular parts add up to the same function on `(0, 1]`.
  have hreg : (∫ z in (0 : ℝ)..1, (pqq c).regular z * φ z) +
      ∫ z in (0 : ℝ)..1, (pgq c).regular z * φ z =
      (∫ z in (0 : ℝ)..1, (pqgSinglet c).regular z * φ z) +
        ∫ z in (0 : ℝ)..1, (pgg c).regular z * φ z := by
    rw [← intervalIntegral.integral_add hqq hgq, ← intervalIntegral.integral_add hqg hgg]
    refine intervalIntegral.integral_congr_ae (ae_of_all _ fun z hz => ?_)
    rw [uIoc_of_le zero_le_one] at hz
    have hz0 : z ≠ 0 := hz.1.ne'
    simp only [pqq_regular, pgq_regular, pqgSinglet_regular, pgg_regular, hc.cF_eq_cA,
      ← hc.two_mul_nF_mul_tF_eq_cA]
    field_simp
    ring
  -- The delta coefficients agree because `β₀ = 3 C_A` at the supersymmetric point.
  have hdelta : (pgg c).deltaCoeff = (pqq c).deltaCoeff := by
    rw [pgg_deltaCoeff_eq_beta0_div_two, hc.beta0_eq, pqq_deltaCoeff, hc.cF_eq_cA]
    ring
  simp only [KernelForm.pairing_def, hdelta, pqq_plusCoeff, pgq_plusCoeff, pgq_deltaCoeff,
    pqgSinglet_plusCoeff, pqgSinglet_deltaCoeff, pgg_plusCoeff, hc.cF_eq_cA]
  linear_combination hreg

/-- **The supersymmetric relation.** At the supersymmetric point `C_F = C_A = 2 n_f T_F`, the
leading-order moments satisfy `γ_qq(N) + γ_gq(N) = γ_qg(N) + γ_gg(N)` at every real `N > 1`, with
`γ_qg` the singlet-normalised moment. -/
theorem moment_pqq_add_moment_pgq (hc : c.IsSupersymmetric) {N : ℝ} (hN : 1 < N) :
    (pqq c).moment N + (pgq c).moment N = (pqgSinglet c).moment N + (pgg c).moment N := by
  simp only [KernelForm.moment_def]
  refine pairing_pqq_add_pairing_pgq hc ?_
  refine (intervalIntegral.intervalIntegrable_rpow' (r := N - 2) (by linarith)).congr
    fun z hz => ?_
  rw [uIoc_of_le zero_le_one] at hz
  rw [← Real.rpow_sub_one hz.1.ne']
  ring_nf

/-! ### Large-`N` behaviour of the diagonal moments -/

/-- **The large-`N` expansion of `γ_qq`.** `γ_qq(N) = -2 C_F (log N + γ_E) + (3/2) C_F + O(1/N)`,
with `γ_E` the Euler–Mascheroni constant. -/
theorem isBigO_moment_pqq_add_log_inv (c : ColorFactors) :
    (fun N : ℕ => (pqq c).moment N + 2 * c.cF * (Real.log N + Real.eulerMascheroniConstant) -
      3 / 2 * c.cF) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  have hrat : (fun N : ℕ => 1 / ((N : ℝ) * (N + 1))) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul,
      one_div]
    exact inv_anti₀ (by positivity) (by nlinarith)
  refine ((isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_inv.const_mul_left
    (-2 * c.cF)).add (hrat.const_mul_left c.cF)).congr' ?_
    EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with N hN
  rw [moment_pqq c hN]
  ring

/-- **The large-`N` expansion of `γ_gg`.** `γ_gg(N) = -2 C_A (log N + γ_E) + β₀ / 2 + O(1/N)`,
with `γ_E` the Euler–Mascheroni constant and `β₀ / 2 = (11/6) C_A - (2/3) n_f T_F` the delta
coefficient of `P_gg`. -/
theorem isBigO_moment_pgg_add_log_inv (c : ColorFactors) :
    (fun N : ℕ => (pgg c).moment N + 2 * c.cA * (Real.log N + Real.eulerMascheroniConstant) -
      beta0 c / 2) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  -- `1/(N-1) - 1/N + 1/(N+1) - 1/(N+2) = 1/((N-1) N) + 1/((N+1) (N+2))` lies in `[0, 2/N]`.
  have hrat : (fun N : ℕ => 1 / ((N : ℝ) - 1) - 1 / N + 1 / (N + 1) - 1 / (N + 2)) =O[atTop]
      fun N : ℕ => (N : ℝ)⁻¹ := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    have hsplit : 1 / ((N : ℝ) - 1) - 1 / N + 1 / (N + 1) - 1 / (N + 2) =
        1 / ((N - 1) * N) + 1 / ((N + 1) * (N + 2)) := by
      have h1 : (N : ℝ) - 1 ≠ 0 := by linarith
      field_simp
      ring
    have hle₁ : 1 / (((N : ℝ) - 1) * N) ≤ (N : ℝ)⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by nlinarith)
    have hle₂ : 1 / (((N : ℝ) + 1) * (N + 2)) ≤ (N : ℝ)⁻¹ := by
      rw [one_div]
      exact inv_anti₀ (by positivity) (by nlinarith)
    have h₁ : 0 ≤ 1 / (((N : ℝ) - 1) * N) := by
      have : (0 : ℝ) ≤ N - 1 := by linarith
      positivity
    rw [hsplit, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    linarith
  refine ((isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_inv.const_mul_left
    (-2 * c.cA)).add (hrat.const_mul_left (2 * c.cA))).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [moment_pgg c hN, beta0]
  ring

end Evolution
end Factorization
end QFT
end EpsilonEridani
