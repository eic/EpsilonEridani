/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# Large-`N` asymptotics of the first harmonic sum

The first harmonic sum `S₁(N) = ∑_{i=1}^{N} 1/i` (Mathlib's `harmonic`) satisfies the explicit
two-sided bound

  `log N + γ + 1/(2N) - 1/(8N²) ≤ S₁(N) ≤ log N + γ + 1/(2N)`,  `N ≥ 1`,

with `γ` the Euler–Mascheroni constant. This gives `S₁(N) = log N + γ + O(1/N)` and its
refinement `S₁(N) = log N + γ + 1/(2N) + O(1/N²)`. The bound comes from comparing `log(1 + 1/a)`
with its trapezoidal approximation `1/(2a) + 1/(2(a + 1))` through the series
`log(1 + 1/a) = ∑_k 2/(2k+1) (2a+1)^(-(2k+1))`. These asymptotics are what relate the large-`N`
growth of the anomalous dimensions to the `z → 1` singularities of the splitting kernels.

## Main statements

* `EpsilonEridani.log_one_add_inv_le_inv_two_mul_add_inv_two_mul_add_one` and
  `EpsilonEridani.inv_two_mul_add_inv_two_mul_add_one_sub_log_one_add_inv_le`: the trapezoidal
  estimate for `∫_a^{a+1} dx/x`.
* `EpsilonEridani.harmonic_le_log_add_eulerMascheroniConstant_add_inv_two_mul` and
  `EpsilonEridani.log_add_eulerMascheroniConstant_add_inv_two_mul_sub_inv_eight_mul_sq_le_harmonic`:
  the two-sided bound above.
* `EpsilonEridani.isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_inv`:
  `S₁(N) = log N + γ + O(1/N)`, and its second-order refinement
  `EpsilonEridani.isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_sub_inv_two_mul_inv_sq`.

## References

* J. Blümlein and S. Kurth, *Harmonic sums and Mellin transforms up to two-loop order*,
  Phys. Rev. D 60 (1999) 014018, arXiv:hep-ph/9810241.
* The proof of the auxiliary series bounds uses Mathlib's formalisation of Stirling's
  approximation, following the approach of de Bruijn, *Asymptotic Methods in Analysis* (1981).
-/

@[expose] public section

open Filter Topology Asymptotics

namespace EpsilonEridani

/-- The trapezoidal value `1/(2a) + 1/(2(a+1))` of `∫_a^{a+1} dx/x` exceeds `log(1 + 1/a)`. -/
theorem log_one_add_inv_le_inv_two_mul_add_inv_two_mul_add_one {a : ℝ} (ha : 0 < a) :
    Real.log (1 + a⁻¹) ≤ (2 * a)⁻¹ + (2 * (a + 1))⁻¹ := by
  set u : ℝ := 1 / (2 * a + 1) with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u < 1 := by rw [hu, div_lt_one (by positivity)]; linarith
  have hL := Real.hasSum_log_one_add_inv ha
  rw [← hu] at hL
  have hT : HasSum (fun k : ℕ => 2 * u ^ (2 * k + 1)) ((2 * a)⁻¹ + (2 * (a + 1))⁻¹) := by
    have hg := (hasSum_geometric_of_lt_one (sq_nonneg u) (by nlinarith)).mul_left (2 * u)
    have h1u : 1 - u ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
      rw [hu]
      field_simp
      ring
    convert hg using 1
    · funext k
      ring
    · rw [h1u, hu]
      field_simp
      ring
  refine hasSum_le (fun k => ?_) hL hT
  have hk : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [k.cast_nonneg (α := ℝ)]
  have := pow_pos hu0 (2 * k + 1)
  nlinarith

/-- The trapezoidal value `1/(2a) + 1/(2(a+1))` of `∫_a^{a+1} dx/x` exceeds `log(1 + 1/a)` by at
most `1/(8a²) - 1/(8(a+1)²)`, a bound that telescopes along `a, a + 1, a + 2, …`. -/
theorem inv_two_mul_add_inv_two_mul_add_one_sub_log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    (2 * a)⁻¹ + (2 * (a + 1))⁻¹ - Real.log (1 + a⁻¹) ≤ (8 * a ^ 2)⁻¹ - (8 * (a + 1) ^ 2)⁻¹ := by
  have h0 := le_hasSum (Real.hasSum_log_one_add_inv ha) 0 fun j _ => by positivity
  have key : (8 * a ^ 2)⁻¹ - (8 * (a + 1) ^ 2)⁻¹ - ((2 * a)⁻¹ + (2 * (a + 1))⁻¹ -
      2 * (2 * a + 1)⁻¹) = (8 * a ^ 2 * (a + 1) ^ 2 * (2 * a + 1))⁻¹ := by
    field_simp
    ring
  have : 0 < (8 * a ^ 2 * (a + 1) ^ 2 * (2 * a + 1))⁻¹ := by positivity
  norm_num at h0
  linarith

/-- The error of the second-order expansion `S₁(N) ≈ log N + γ + 1/(2N)`. -/
private noncomputable def secondOrderError (n : ℕ) : ℝ :=
  (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant - (2 * (n : ℝ))⁻¹

private theorem secondOrderError_succ_sub {n : ℕ} (hn : n ≠ 0) :
    secondOrderError (n + 1) - secondOrderError n =
      (2 * (n : ℝ))⁻¹ + (2 * ((n : ℝ) + 1))⁻¹ - Real.log (1 + (n : ℝ)⁻¹) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  rw [show 1 + (n : ℝ)⁻¹ = (n + 1) / n by field_simp,
    Real.log_div (by positivity) hn'.ne', secondOrderError, secondOrderError, harmonic_succ]
  push_cast
  field_simp
  ring

private theorem tendsto_secondOrderError : Tendsto secondOrderError atTop (𝓝 0) := by
  have h := (Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant).sub
    ((tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (2⁻¹ : ℝ))
  simp only [sub_self, mul_zero] at h
  refine h.congr fun n => ?_
  simp [secondOrderError, mul_comm]

/-- Along the telescoping sum, the error increases, by at most the telescoping bound. -/
private theorem secondOrderError_le_add_and_sub_le {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    secondOrderError n ≤ secondOrderError (n + j) ∧
      secondOrderError (n + j) - secondOrderError n ≤
        (8 * (n : ℝ) ^ 2)⁻¹ - (8 * ((n + j : ℕ) : ℝ) ^ 2)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hnj : n + j ≠ 0 := by omega
    have hpos : (0 : ℝ) < (n + j : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hnj
    have hd₁ := log_one_add_inv_le_inv_two_mul_add_inv_two_mul_add_one hpos
    have hd₂ := inv_two_mul_add_inv_two_mul_add_one_sub_log_one_add_inv_le hpos
    have hd := secondOrderError_succ_sub hnj
    rw [← add_assoc]
    push_cast at hd₁ hd₂ hd ih ⊢
    constructor <;> linarith [ih.1, ih.2]

/-- **The second-order upper bound** `S₁(N) ≤ log N + γ + 1/(2N)` for `N ≥ 1`. -/
theorem harmonic_le_log_add_eulerMascheroniConstant_add_inv_two_mul {n : ℕ} (hn : n ≠ 0) :
    (harmonic n : ℝ) ≤ Real.log n + Real.eulerMascheroniConstant + (2 * (n : ℝ))⁻¹ := by
  have : secondOrderError n ≤ 0 := by
    refine ge_of_tendsto tendsto_secondOrderError ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact (secondOrderError_le_add_and_sub_le hn j).1
  rw [secondOrderError] at this
  linarith

/-- **The second-order lower bound** `log N + γ + 1/(2N) - 1/(8N²) ≤ S₁(N)` for `N ≥ 1`. -/
theorem log_add_eulerMascheroniConstant_add_inv_two_mul_sub_inv_eight_mul_sq_le_harmonic
    {n : ℕ} (hn : n ≠ 0) :
    Real.log n + Real.eulerMascheroniConstant + (2 * (n : ℝ))⁻¹ - (8 * (n : ℝ) ^ 2)⁻¹ ≤
      (harmonic n : ℝ) := by
  have : 0 - secondOrderError n ≤ (8 * (n : ℝ) ^ 2)⁻¹ := by
    refine le_of_tendsto (tendsto_secondOrderError.sub_const _) ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    have := (secondOrderError_le_add_and_sub_le hn j).2
    have : (0 : ℝ) ≤ (8 * ((n + j : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
    linarith
  rw [secondOrderError] at this
  linarith

/-- **The second-order large-`N` asymptotics of the first harmonic sum**,
`S₁(N) = log N + γ + 1/(2N) + O(1/N²)`. -/
theorem isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_sub_inv_two_mul_inv_sq :
    (fun n : ℕ => (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant - (2 * (n : ℝ))⁻¹)
      =O[atTop] (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  refine IsBigO.of_bound 8⁻¹ ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h₁ := harmonic_le_log_add_eulerMascheroniConstant_add_inv_two_mul hn
  have h₂ := log_add_eulerMascheroniConstant_add_inv_two_mul_sub_inv_eight_mul_sq_le_harmonic hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (a := ((n : ℝ) ^ 2)⁻¹) (by positivity),
    abs_le, ← mul_inv]
  constructor <;> linarith

/-- **The large-`N` asymptotics of the first harmonic sum**, `S₁(N) = log N + γ + O(1/N)`. -/
theorem isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_inv :
    (fun n : ℕ => (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  -- `1/N² = O(1/N)` and `1/(2N) = O(1/N)`, so the second-order expansion gives the first-order one
  have h₁ : (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), one_mul]
    exact inv_anti₀ (by positivity) (by nlinarith)
  have h₂ : (fun n : ℕ => (2 * (n : ℝ))⁻¹) =O[atTop] (fun n : ℕ => (n : ℝ)⁻¹) := by
    simp_rw [mul_inv]
    exact isBigO_const_mul_self _ _ _
  refine ((isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_sub_inv_two_mul_inv_sq.trans
    h₁).add h₂).congr_left fun n => ?_
  ring

end EpsilonEridani
