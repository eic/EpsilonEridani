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
* `isBigO_moment_pqq_add_const_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv`,
  `isBigO_moment_pgg_add_const_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv`: the
  large-`N` expansions of the diagonal moments, at natural `N`, and their leading forms
  `isBigO_moment_pqq_add_const_mul_log_one`, `isBigO_moment_pgg_add_const_mul_log_one`.

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
  have hφ' : IntervalIntegrable φ volume 0 1 :=
    (hφ.continuousOn_mul (g := fun z => z) (continuousOn_id' _)).congr fun z hz => by
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

/-- **The large-`N` expansion of a kernel's moments.** If the moment
`∫₀¹ r z z ^ (N - 1) dz` of the regular part `r` is `O(1/N)`, then
`P.moment N = -p (log N + γ_E) + d + O(1/N)` as `N → ∞` through the natural numbers, with `p` the
coefficient of `[1 / (1 - z)]₊`, `d` that of `δ(1 - z)`, and `γ_E` the Euler–Mascheroni constant:
the plus part contributes `-p S₁(N - 1)`, which grows like `-p log N`. -/
theorem isBigO_moment_add_plusCoeff_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    (P : KernelForm)
    (hr : (fun N : ℕ => ∫ z in (0 : ℝ)..1, P.regular z * z ^ ((N : ℝ) - 1)) =O[atTop]
      fun N : ℕ => (N : ℝ)⁻¹) :
    (fun N : ℕ => P.moment N + P.plusCoeff * (Real.log N + Real.eulerMascheroniConstant) -
      P.deltaCoeff) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  -- `P.moment N = r_N - p S₁(N - 1) + d` and `S₁(N - 1) = S₁(N) - 1/N`
  refine ((hr.sub (isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_inv.const_mul_left
    P.plusCoeff)).add ((isBigO_refl (fun N : ℕ => (N : ℝ)⁻¹) atTop).const_mul_left
    P.plusCoeff)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  rw [Nat.succ_eq_add_one, Nat.cast_add_one, KernelForm.moment_natCast_add_one,
    KernelForm.pairing_pow, harmonic_succ]
  simp only [add_sub_cancel_right, Real.rpow_natCast]
  push_cast
  ring

end KernelForm

/-- **The large-`N` expansion of `γ_qq`.** `γ_qq(N) = -2 C_F (log N + γ_E) + (3/2) C_F + O(1/N)`
as `N → ∞` through the natural numbers, with `γ_E` the Euler–Mascheroni constant and
`(3/2) C_F` the delta coefficient of `P_qq`. -/
theorem isBigO_moment_pqq_add_const_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    (c : ColorFactors) :
    (fun N : ℕ => (pqq c).moment N + 2 * c.cF * (Real.log N + Real.eulerMascheroniConstant) -
      (pqq c).deltaCoeff) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  rw [← pqq_plusCoeff]
  refine (pqq c).isBigO_moment_add_plusCoeff_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    ?_
  -- The regular part `-C_F (1 + z)` has moment `-C_F (1/N + 1/(N + 1))`.
  refine (((isBigO_inv_natCast_add_inv 0).add (isBigO_inv_natCast_add_inv 1)).const_mul_left
    (-c.cF)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop 0] with N hN
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have h := moment_pqq c hN
  rw [Nat.succ_eq_add_one, Nat.cast_add_one, KernelForm.moment_natCast_add_one,
    KernelForm.pairing_pow, harmonic_succ, pqq_plusCoeff, pqq_deltaCoeff] at h
  simp only [Nat.succ_eq_add_one, Nat.cast_add_one, add_sub_cancel_right, Real.rpow_natCast]
  push_cast at h ⊢
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn' : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  linear_combination (norm := skip) -h
  field_simp
  ring

/-- **The large-`N` expansion of `γ_gg`.** `γ_gg(N) = -2 C_A (log N + γ_E) + β₀ / 2 + O(1/N)`
as `N → ∞` through the natural numbers, with `γ_E` the Euler–Mascheroni constant and
`β₀ / 2 = (11/6) C_A - (2/3) n_f T_F` the delta coefficient of `P_gg`. -/
theorem isBigO_moment_pgg_add_const_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    (c : ColorFactors) :
    (fun N : ℕ => (pgg c).moment N + 2 * c.cA * (Real.log N + Real.eulerMascheroniConstant) -
      (pgg c).deltaCoeff) =O[atTop] fun N : ℕ => (N : ℝ)⁻¹ := by
  rw [← pgg_plusCoeff]
  refine (pgg c).isBigO_moment_add_plusCoeff_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv
    ?_
  -- The regular part has moment `2 C_A (1/(N - 1) - 2/N + 1/(N + 1) - 1/(N + 2))`.
  refine (((((isBigO_inv_natCast_add_inv (-1)).sub
    ((isBigO_inv_natCast_add_inv 0).const_mul_left 2)).add (isBigO_inv_natCast_add_inv 1)).sub
    (isBigO_inv_natCast_add_inv 2)).const_mul_left (2 * c.cA)).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hN0 : N ≠ 0 := by omega
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN0
  have h := moment_pgg c hN
  rw [Nat.succ_eq_add_one, Nat.cast_add_one, KernelForm.moment_natCast_add_one,
    KernelForm.pairing_pow, harmonic_succ, pgg_plusCoeff, pgg_deltaCoeff] at h
  simp only [Nat.succ_eq_add_one, Nat.cast_add_one, add_sub_cancel_right, Real.rpow_natCast]
  have hn₀ : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hn₁ : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn₂ : (n : ℝ) + 1 + 1 ≠ 0 := by positivity
  have hn₃ : (n : ℝ) + 1 + 2 ≠ 0 := by positivity
  push_cast at h ⊢
  linear_combination (norm := skip) -h
  field_simp
  ring

/-- **The leading large-`N` behaviour of `γ_qq`.** `γ_qq(N) = -2 C_F log N + O(1)` as `N → ∞`
through the natural numbers. -/
theorem isBigO_moment_pqq_add_const_mul_log_one (c : ColorFactors) :
    (fun N : ℕ => (pqq c).moment N + 2 * c.cF * Real.log N) =O[atTop] fun _ : ℕ => (1 : ℝ) :=
  (((isBigO_moment_pqq_add_const_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv c).trans
    (tendsto_inv_atTop_nhds_zero_nat.isBigO_one ℝ)).add
    (isBigO_const_const ((pqq c).deltaCoeff - 2 * c.cF * Real.eulerMascheroniConstant)
      one_ne_zero atTop)).congr_left fun N => by ring

/-- **The leading large-`N` behaviour of `γ_gg`.** `γ_gg(N) = -2 C_A log N + O(1)` as `N → ∞`
through the natural numbers. -/
theorem isBigO_moment_pgg_add_const_mul_log_one (c : ColorFactors) :
    (fun N : ℕ => (pgg c).moment N + 2 * c.cA * Real.log N) =O[atTop] fun _ : ℕ => (1 : ℝ) :=
  (((isBigO_moment_pgg_add_const_mul_log_add_eulerMascheroniConstant_sub_deltaCoeff_inv c).trans
    (tendsto_inv_atTop_nhds_zero_nat.isBigO_one ℝ)).add
    (isBigO_const_const ((pgg c).deltaCoeff - 2 * c.cA * Real.eulerMascheroniConstant)
      one_ne_zero atTop)).congr_left fun N => by ring

end Evolution
end Factorization
end QFT
end EpsilonEridani
