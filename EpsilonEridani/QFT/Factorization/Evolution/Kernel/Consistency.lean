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
which hold at `N = 2` for every choice of colour factors, it constrains the kernels at every `N`,
though only through the combinations of their coefficients that survive at the supersymmetric
point: it cannot tell `C_F`, `C_A` and `2 n_f T_F` apart.

**Large-`N` behaviour of the diagonal moments.** For any kernel whose regular part has moments
`O(1/N)`, the moment is `-p (log N + γ_E) + d + O(1/N)` as `N → ∞` through the natural numbers,
with `p` and `d` the coefficients of `[1 / (1 - z)]₊` and `δ(1 - z)` and `γ_E` the
Euler–Mascheroni constant. So the moments `γ_qq(N)` and `γ_gg(N)` fall like `-2 C log N`, with
`C` the colour charge of the radiating parton, as the plus coefficients `2 C_F` and `2 C_A`
dictate: at natural `N`,

  `γ_qq(N) = -2 C_F (log N + γ_E) + (3/2) C_F + O(1/N)`,
  `γ_gg(N) = -2 C_A (log N + γ_E) + β₀ / 2 + O(1/N)`,

and in particular `γ_qq(N) = -2 C_F log N + O(1)` and `γ_gg(N) = -2 C_A log N + O(1)`. The growth
is only logarithmic, so evolution changes high moments, which govern the large-momentum-fraction
region, slowly.

## Main results

* `pairing_pqq_add_pairing_pgq_eq_pairing_pqgSinglet_add_pairing_pgg`: the supersymmetric
  relation for the pairing with any test function `φ` for which `φ z / z` is integrable on
  `[0, 1]`.
* `moment_pqq_add_moment_pgq_eq_moment_pqgSinglet_add_moment_pgg`: the supersymmetric relation
  for the moments, at every real `N > 1`.
* `KernelForm.isBigO_moment_add_plusCoeff_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv`:
  the large-`N` expansion of the moments of a kernel, at natural `N`.
  Its leading form `KernelForm.isBigO_moment_add_plusCoeff_mul_log_one`.
* `isBigO_moment_pqq_add_two_mul_cF_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv`,
  `isBigO_moment_pgg_add_two_mul_cA_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv`: the
  large-`N` expansions of the diagonal moments, at natural `N`, and their leading forms
  `isBigO_moment_pqq_add_two_mul_cF_mul_log_one`, `isBigO_moment_pgg_add_two_mul_cA_mul_log_one`.

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
theorem pairing_pqq_add_pairing_pgq_eq_pairing_pqgSinglet_add_pairing_pgg
    (hc : c.IsSupersymmetric) {φ : ℝ → ℝ} (hφ : IntervalIntegrable (fun z => φ z / z) volume 0 1) :
    (pqq c).pairing φ + (pgq c).pairing φ = (pqgSinglet c).pairing φ + (pgg c).pairing φ := by
  have hφ' : IntervalIntegrable φ volume 0 1 := intervalIntegrable_of_one_div_z_integrand hφ
  have hqq := intervalIntegrable_pqq_regular_mul c hφ'
  have hgq := intervalIntegrable_pgq_regular_mul c hφ
  have hqg := intervalIntegrable_pqgSinglet_regular_mul c hφ'
  have hgg := intervalIntegrable_pgg_regular_mul c hφ
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
    rw [pgg_deltaCoeff_eq_beta0_div_two, hc.beta0_eq_three_mul_cA, pqq_deltaCoeff, hc.cF_eq_cA]
    ring
  simp only [KernelForm.pairing_def, hdelta, pqq_plusCoeff, pgq_plusCoeff, pgq_deltaCoeff,
    pqgSinglet_plusCoeff, pqgSinglet_deltaCoeff, pgg_plusCoeff, hc.cF_eq_cA]
  linear_combination hreg

/-- **The supersymmetric relation.** At the supersymmetric point `C_F = C_A = 2 n_f T_F`, the
leading-order moments satisfy `γ_qq(N) + γ_gq(N) = γ_qg(N) + γ_gg(N)` at every real `N > 1`, with
`γ_qg` the singlet-normalised moment. -/
theorem moment_pqq_add_moment_pgq_eq_moment_pqgSinglet_add_moment_pgg (hc : c.IsSupersymmetric)
    {N : ℝ} (hN : 1 < N) :
    (pqq c).moment N + (pgq c).moment N = (pqgSinglet c).moment N + (pgg c).moment N := by
  simp only [KernelForm.moment_def]
  refine pairing_pqq_add_pairing_pgq_eq_pairing_pqgSinglet_add_pairing_pgg hc ?_
  refine (intervalIntegral.intervalIntegrable_rpow' (r := N - 2) (by linarith)).congr
    fun z hz => ?_
  rw [uIoc_of_le zero_le_one] at hz
  rw [← Real.rpow_sub_one hz.1.ne']
  ring_nf

/-! ### Large-`N` behaviour of the diagonal moments -/

namespace KernelForm

/-- **The large-`N` expansion of a kernel's moments.** If the moments `∫₀¹ r z z ^ n dz` of the
regular part `r` are `O(1/n)`, then `P.moment N = -p (log N + γ_E) + d + O(1/N)` as `N → ∞`
through the natural numbers, with `p` the coefficient of `[1 / (1 - z)]₊`, `d` that of
`δ(1 - z)`, and `γ_E` the Euler–Mascheroni constant: the plus part contributes `-p S₁(N - 1)`,
which grows like `-p log N`. -/
theorem isBigO_moment_add_plusCoeff_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    (P : KernelForm)
    (hr : (fun n : ℕ => ∫ z in (0 : ℝ)..1, P.regular z * z ^ n) =O[atTop]
      fun n : ℕ => (n : ℝ)⁻¹) :
    (fun N : ℕ => P.moment N + P.plusCoeff * (Real.log N + Real.eulerMascheroniConstant) -
      P.deltaCoeff) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  -- The regular moment at `N - 1` is `O(1/(N - 1)) = O(1/N)`.
  have hr' : (fun N : ℕ => ∫ z in (0 : ℝ)..1, P.regular z * z ^ (N - 1)) =O[atTop]
      fun N : ℕ => (N : ℝ)⁻¹ := by
    refine (hr.comp_tendsto (tendsto_sub_atTop_nat 1)).trans
      ((isBigO_natCast_add_inv_inv (-1)).congr' ?_ EventuallyEq.rfl)
    filter_upwards [eventually_ge_atTop 1] with N hN
    simp only [Function.comp_apply, Nat.cast_sub hN, Nat.cast_one, sub_eq_add_neg]
  -- `P.moment N = r_{N-1} - p S₁(N - 1) + d` and `S₁(N - 1) = S₁(N) - 1/N`.
  refine ((hr'.sub (isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_inv.const_mul_left
    P.plusCoeff)).add ((isBigO_refl (fun N : ℕ => (N : ℝ)⁻¹) atTop).const_mul_left
    P.plusCoeff)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  rw [Nat.succ_sub_one, integral_regular_mul_pow, harmonic_succ]
  push_cast
  ring

/-- **The leading large-`N` behaviour of a kernel's moments.** If
`P.moment N = -p (log N + γ_E) + d + O(1)` as `N → ∞` through the natural numbers, then
`P.moment N = -p log N + O(1)`. -/
theorem isBigO_moment_add_plusCoeff_mul_log_one (P : KernelForm)
    (h : (fun N : ℕ => P.moment N + P.plusCoeff * (Real.log N + Real.eulerMascheroniConstant) -
      P.deltaCoeff) =O[atTop] fun _ : ℕ => (1 : ℝ)) :
    (fun N : ℕ => P.moment N + P.plusCoeff * Real.log N) =O[atTop] fun _ : ℕ => (1 : ℝ) :=
  (h.add
    (isBigO_const_const (P.deltaCoeff - P.plusCoeff * Real.eulerMascheroniConstant)
      one_ne_zero atTop)).congr_left fun N => by ring

end KernelForm

/-- **The large-`N` expansion of `γ_qq`.** `γ_qq(N) = -2 C_F (log N + γ_E) + (3/2) C_F + O(1/N)`
as `N → ∞` through the natural numbers, with `γ_E` the Euler–Mascheroni constant and
`(3/2) C_F` the delta coefficient of `P_qq`. -/
theorem isBigO_moment_pqq_add_two_mul_cF_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    (c : ColorFactors) :
    (fun N : ℕ => (pqq c).moment N + 2 * c.cF * (Real.log N + Real.eulerMascheroniConstant) -
      (pqq c).deltaCoeff) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  rw [← pqq_plusCoeff]
  refine (pqq c).isBigO_moment_add_plusCoeff_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    ?_
  -- The regular part `-C_F (1 + z)` has moments `-C_F (1/(n + 1) + 1/(n + 2))`.
  refine (((isBigO_natCast_add_inv_inv 1).add (isBigO_natCast_add_inv_inv 2)).const_mul_left
    (-c.cF)).congr' ?_ EventuallyEq.rfl
  filter_upwards with n
  rw [KernelForm.integral_regular_mul_pow, ← Nat.cast_add_one, moment_pqq c n.succ_ne_zero,
    pqq_plusCoeff, pqq_deltaCoeff, harmonic_succ]
  push_cast
  field_simp
  ring

/-- **The large-`N` expansion of `γ_gg`.** `γ_gg(N) = -2 C_A (log N + γ_E) + β₀ / 2 + O(1/N)`
as `N → ∞` through the natural numbers, with `γ_E` the Euler–Mascheroni constant and
`β₀ / 2 = (11/6) C_A - (2/3) n_f T_F` the delta coefficient of `P_gg`. -/
theorem isBigO_moment_pgg_add_two_mul_cA_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    (c : ColorFactors) :
    (fun N : ℕ => (pgg c).moment N + 2 * c.cA * (Real.log N + Real.eulerMascheroniConstant) -
      (pgg c).deltaCoeff) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  rw [← pgg_plusCoeff]
  refine (pgg c).isBigO_moment_add_plusCoeff_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    ?_
  -- The regular part has moments `2 C_A (1/n - 2/(n + 1) + 1/(n + 2) - 1/(n + 3))`.
  refine (((((isBigO_refl _ _).sub ((isBigO_natCast_add_inv_inv 1).const_mul_left 2)).add
    (isBigO_natCast_add_inv_inv 2)).sub (isBigO_natCast_add_inv_inv 3)).const_mul_left
    (2 * c.cA)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with n hn
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [KernelForm.integral_regular_mul_pow, ← Nat.cast_add_one,
    moment_pgg c (Nat.succ_le_succ (Nat.one_le_iff_ne_zero.2 hn)), pgg_plusCoeff, pgg_deltaCoeff,
    harmonic_succ]
  push_cast
  simp only [add_sub_cancel_right]
  field_simp
  ring

/-- **The leading large-`N` behaviour of `γ_qq`.** `γ_qq(N) = -2 C_F log N + O(1)` as `N → ∞`
through the natural numbers. -/
theorem isBigO_moment_pqq_add_two_mul_cF_mul_log_one (c : ColorFactors) :
    (fun N : ℕ => (pqq c).moment N + 2 * c.cF * Real.log N) =O[atTop] fun _ : ℕ => (1 : ℝ) := by
  simpa only [pqq_plusCoeff] using (pqq c).isBigO_moment_add_plusCoeff_mul_log_one (by
    simpa only [pqq_plusCoeff] using
      (isBigO_moment_pqq_add_two_mul_cF_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
        c).trans (tendsto_inv_atTop_nhds_zero_nat.isBigO_one ℝ))

/-- **The leading large-`N` behaviour of `γ_gg`.** `γ_gg(N) = -2 C_A log N + O(1)` as `N → ∞`
through the natural numbers. -/
theorem isBigO_moment_pgg_add_two_mul_cA_mul_log_one (c : ColorFactors) :
    (fun N : ℕ => (pgg c).moment N + 2 * c.cA * Real.log N) =O[atTop] fun _ : ℕ => (1 : ℝ) := by
  simpa only [pgg_plusCoeff] using (pgg c).isBigO_moment_add_plusCoeff_mul_log_one (by
    simpa only [pgg_plusCoeff] using
      (isBigO_moment_pgg_add_two_mul_cA_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
        c).trans (tendsto_inv_atTop_nhds_zero_nat.isBigO_one ℝ))

end Evolution
end Factorization
end QFT
end EpsilonEridani
