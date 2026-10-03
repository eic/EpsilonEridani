/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Asymptotics.Defs

/-!
# The analytic continuation of the first harmonic sum

The first harmonic sum `S₁(N) = ∑_{i=1}^{N} 1/i` (`EpsilonEridani.harmonicSum [1]`, which is
Mathlib's `harmonic`) is defined for natural `N` only. Through the digamma function
`ψ = Γ'/Γ` (`Complex.digamma`) it continues to the meromorphic function

  `S₁(s) = ψ(s + 1) + γ`,

with `γ` the Euler–Mascheroni constant. This file defines that continuation, `complexHarmonic`,
and develops its basic theory:

* it restricts to `harmonic` on the natural numbers;
* it satisfies the recurrence `S₁(s + 1) = S₁(s) + 1/(s + 1)` and the reflection formula
  `S₁(-s) = S₁(s - 1) + π cot(π s)`;
* it is meromorphic on `ℂ`, analytic away from the negative integers, and has a simple pole with
  residue `-1` at each negative integer `-(m + 1)`.

The continuation matters because the Mellin moments of the splitting kernels are rational
functions of the moment variable `N` and harmonic sums of `N`; the inversion contour of the
Mellin transform runs through complex `N`, and the pole structure of the moments in the complex
plane is what controls the behaviour of the densities in momentum-fraction space.

The file also proves the large-`N` asymptotics of `S₁` along the positive integers, from the
explicit two-sided bound

  `log N + γ + 1/(2N) - 1/(8N²) ≤ S₁(N) ≤ log N + γ + 1/(2N)`,  `N ≥ 1`,

which gives `S₁(N) = log N + γ + O(1/N)`, its refinement `S₁(N) = log N + γ + 1/(2N) + O(1/N²)`,
and the corresponding expansion `ψ(N) = log N - 1/(2N) + O(1/N²)` of the digamma function. The
bound comes from comparing `log(1 + 1/N)` with its trapezoidal approximation through the series
`log(1 + 1/a) = ∑_k 2/(2k+1) (2a+1)^(-(2k+1))`. These asymptotics are what relate the large-`N`
growth of the anomalous dimensions to the `z → 1` singularities of the kernels.

## Main definitions

* `EpsilonEridani.complexHarmonic`: the continuation `s ↦ ψ(s + 1) + γ` of `S₁`.

## Main statements

* `EpsilonEridani.complexHarmonic_natCast`: `complexHarmonic n = harmonic n`.
* `EpsilonEridani.complexHarmonic_add_one`: the recurrence `S₁(s + 1) = S₁(s) + 1/(s + 1)`.
* `EpsilonEridani.complexHarmonic_neg`: the reflection formula.
* `EpsilonEridani.analyticAt_complexHarmonic`: analyticity away from the negative integers.
* `EpsilonEridani.meromorphicOrderAt_complexHarmonic_neg_nat_sub_one` and
  `EpsilonEridani.tendsto_mul_complexHarmonic_neg_nat_sub_one`: a simple pole with residue `-1`
  at each negative integer.
* `EpsilonEridani.harmonic_le_log_add_eulerMascheroniConstant_add_inv_two_mul` and
  `EpsilonEridani.log_add_eulerMascheroniConstant_add_inv_two_mul_sub_le_harmonic`: the
  two-sided bound above.
* `EpsilonEridani.isBigO_harmonic_sub_log_sub_eulerMascheroniConstant`:
  `S₁(N) = log N + γ + O(1/N)`, and its second-order refinement
  `EpsilonEridani.isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_sub_inv_two_mul`.
* `EpsilonEridani.isBigO_digamma_natCast_sub_log_add_inv_two_mul`:
  `ψ(N) = log N - 1/(2N) + O(1/N²)`.

## References

* J. Blümlein and S. Kurth, *Harmonic sums and Mellin transforms up to two-loop order*,
  Phys. Rev. D 60 (1999) 014018, arXiv:hep-ph/9810241.
* J. Blümlein, *Analytic continuation of Mellin transforms up to two-loop order*,
  Comput. Phys. Commun. 133 (2000) 76, arXiv:hep-ph/0003100.
-/

public section

open Complex Filter Topology Asymptotics
open scoped Real

namespace EpsilonEridani

/-- The analytic continuation of the first harmonic sum `S₁(N) = harmonic N` to complex
argument, `S₁(s) = ψ(s + 1) + γ`, with `ψ` the digamma function and `γ` the Euler–Mascheroni
constant. It is meromorphic, with simple poles at the negative integers. -/
noncomputable def complexHarmonic (s : ℂ) : ℂ :=
  digamma (s + 1) + Real.eulerMascheroniConstant

theorem complexHarmonic_def (s : ℂ) :
    complexHarmonic s = digamma (s + 1) + Real.eulerMascheroniConstant :=
  (rfl)

/-- The continuation restricts to the harmonic numbers on the natural numbers. -/
@[simp]
theorem complexHarmonic_natCast (n : ℕ) : complexHarmonic n = harmonic n := by
  rw [complexHarmonic_def, digamma_nat_add_one, sub_add_cancel]

@[simp]
theorem complexHarmonic_zero : complexHarmonic 0 = 0 := by
  simpa using complexHarmonic_natCast 0

@[simp]
theorem complexHarmonic_one : complexHarmonic 1 = 1 := by
  simpa using complexHarmonic_natCast 1

/-- Away from the negative integers, `s + 1` avoids the poles `0, -1, -2, …` of `ψ`. -/
private theorem add_one_ne_neg_natCast {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m + 1)) (m : ℕ) :
    s + 1 ≠ -(m : ℂ) := fun h => hs m (by linear_combination h)

/-- **The recurrence** `S₁(s + 1) = S₁(s) + 1/(s + 1)`, away from the negative integers. -/
theorem complexHarmonic_add_one {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m + 1)) :
    complexHarmonic (s + 1) = complexHarmonic s + (s + 1)⁻¹ := by
  rw [complexHarmonic_def, complexHarmonic_def,
    digamma_apply_add_one _ (add_one_ne_neg_natCast hs)]
  ring

/-- **The iterated recurrence** `S₁(s + n) = S₁(s) + ∑_{k=1}^{n} 1/(s + k)`, away from the
negative integers. -/
theorem complexHarmonic_add_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m + 1)) (n : ℕ) :
    complexHarmonic (s + n) = complexHarmonic s + ∑ k ∈ Finset.range n, (s + k + 1)⁻¹ := by
  rw [complexHarmonic_def, complexHarmonic_def, add_right_comm,
    digamma_apply_add_nat (add_one_ne_neg_natCast hs)]
  simp_rw [add_right_comm s 1]
  ring

/-- **The reflection formula** `S₁(-s) = S₁(s - 1) + π cot(π s)`, for non-integer `s`. -/
theorem complexHarmonic_neg {s : ℂ} (hs : ∀ n : ℤ, s ≠ n) :
    complexHarmonic (-s) = complexHarmonic (s - 1) + π * cot (π * s) := by
  rw [complexHarmonic_def, complexHarmonic_def, neg_add_eq_sub, digamma_one_sub hs, sub_add_cancel]
  ring

/-- The continuation is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_complexHarmonic : Meromorphic complexHarmonic := by
  have h : Meromorphic fun s => digamma (s + 1) :=
    Meromorphic.meromorphic_fun_comp_add_const_iff_meromorphic.2 meromorphic_digamma
  rw [show complexHarmonic = fun s => digamma (s + 1) + Real.eulerMascheroniConstant from
    funext complexHarmonic_def]
  fun_prop

/-- The continuation is analytic away from the negative integers. -/
theorem analyticAt_complexHarmonic {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m + 1)) :
    AnalyticAt ℂ complexHarmonic s := by
  have hs' := add_one_ne_neg_natCast hs
  -- `Γ` is the reciprocal of the entire function `1/Γ`, which does not vanish at `s + 1`.
  have hΓ : AnalyticAt ℂ Gamma (s + 1) := by
    have h := (differentiable_one_div_Gamma.analyticAt (s + 1)).inv
      (inv_ne_zero (Gamma_ne_zero hs'))
    rwa [show (fun z => (Gamma z)⁻¹)⁻¹ = Gamma from funext fun z => inv_inv (Gamma z)] at h
  have hψ : AnalyticAt ℂ digamma (s + 1) := by
    rw [digamma_def]
    exact hΓ.deriv.div hΓ (Gamma_ne_zero hs')
  rw [show complexHarmonic = fun z => digamma (z + 1) + Real.eulerMascheroniConstant from
    funext complexHarmonic_def]
  exact (hψ.comp_of_eq (f := fun z => z + 1) (by fun_prop) rfl).add analyticAt_const

theorem continuousAt_complexHarmonic {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m + 1)) :
    ContinuousAt complexHarmonic s :=
  (analyticAt_complexHarmonic hs).continuousAt

/-- Near a negative integer `-(m + 1)`, every other point avoids the negative integers. -/
private theorem eventually_ne_neg_nat_sub_one (m : ℕ) :
    ∀ᶠ s in 𝓝[≠] (-(m + 1 : ℂ)), ∀ j : ℕ, s ≠ -(j + 1 : ℂ) := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds (-(m + 1 : ℂ)) one_pos)] with s hne hball j hj
  subst hj
  rw [Metric.mem_ball, dist_eq_norm] at hball
  have hre := (abs_re_le_norm _).trans_lt hball
  simp only [sub_re, neg_re, add_re, natCast_re, one_re] at hre
  have h₁ : (m : ℝ) < j + 1 := by linarith [(abs_lt.1 hre).2]
  have h₂ : (j : ℝ) < m + 1 := by linarith [(abs_lt.1 hre).1]
  have : j = m := by
    have h₁' : m < j + 1 := by exact_mod_cast h₁
    have h₂' : j < m + 1 := by exact_mod_cast h₂
    omega
  exact hne (by simp [this])

/-- The regular part at the negative integer `-(m + 1)`: the function
`s ↦ S₁(s + m + 1) - ∑_{k<m} 1/(s + k + 1)`, which differs from `S₁` by the polar term
`1/(s + m + 1)` and is analytic at `-(m + 1)`. -/
private noncomputable def regularPart (m : ℕ) (s : ℂ) : ℂ :=
  complexHarmonic (s + (m + 1 : ℕ)) - ∑ k ∈ Finset.range m, (s + k + 1)⁻¹

private theorem eventually_complexHarmonic_eq_regularPart (m : ℕ) :
    ∀ᶠ s in 𝓝[≠] (-(m + 1 : ℂ)),
      complexHarmonic s = regularPart m s - (s + (m + 1))⁻¹ := by
  filter_upwards [eventually_ne_neg_nat_sub_one m] with s hs
  rw [regularPart, complexHarmonic_add_nat hs, Finset.sum_range_succ]
  ring

private theorem analyticAt_regularPart (m : ℕ) :
    AnalyticAt ℂ (regularPart m) (-(m + 1 : ℂ)) := by
  refine AnalyticAt.sub ?_ (Finset.analyticAt_fun_sum _ fun k hk => ?_)
  · refine (analyticAt_complexHarmonic (s := 0) fun j => ?_).comp_of_eq (by fun_prop)
      (by push_cast; ring)
    rw [ne_eq, zero_eq_neg]
    exact_mod_cast Nat.succ_ne_zero j
  · refine AnalyticAt.inv (f := fun s : ℂ => s + k + 1) (by fun_prop) ?_
    rw [show -(m + 1 : ℂ) + k + 1 = k - m by ring, sub_ne_zero]
    exact_mod_cast (Finset.mem_range.1 hk).ne

/-- **The pole structure**: the continuation has a simple pole at every negative integer. -/
theorem meromorphicOrderAt_complexHarmonic_neg_nat_sub_one (m : ℕ) :
    meromorphicOrderAt complexHarmonic (-(m + 1 : ℂ)) = -1 := by
  rw [← WithTop.coe_one, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
    meromorphicOrderAt_eq_int_iff (meromorphic_complexHarmonic _)]
  refine ⟨fun s => (s + (m + 1)) * regularPart m s - 1, ?_, ?_, ?_⟩
  · exact ((analyticAt_id.add analyticAt_const).mul (analyticAt_regularPart m)).sub
      analyticAt_const
  · simp
  · filter_upwards [eventually_complexHarmonic_eq_regularPart m, self_mem_nhdsWithin]
      with s hs hne
    have hne' : s + (m + 1) ≠ 0 := by
      rwa [← sub_neg_eq_add, sub_ne_zero]
    rw [hs, sub_neg_eq_add, zpow_neg_one, smul_eq_mul]
    field_simp

/-- **The residue** of the continuation at every negative integer is `-1`:
`(s + m + 1) S₁(s) → -1` as `s → -(m + 1)`. -/
theorem tendsto_mul_complexHarmonic_neg_nat_sub_one (m : ℕ) :
    Tendsto (fun s => (s + (m + 1)) * complexHarmonic s) (𝓝[≠] (-(m + 1 : ℂ))) (𝓝 (-1)) := by
  have hcont : ContinuousAt (fun s => (s + (m + 1)) * regularPart m s - 1) (-(m + 1 : ℂ)) :=
    ((continuousAt_id.add continuousAt_const).mul
      (analyticAt_regularPart m).continuousAt).sub continuousAt_const
  have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {-(m + 1 : ℂ)}ᶜ))
  simp only [neg_add_cancel, zero_mul, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [eventually_complexHarmonic_eq_regularPart m, self_mem_nhdsWithin]
    with s hs hne
  have hne' : s + (m + 1) ≠ 0 := by
    rwa [← sub_neg_eq_add, sub_ne_zero]
  rw [hs, mul_sub, mul_inv_cancel₀ hne']

/-! ### Large-`N` asymptotics -/

/-- The trapezoidal estimate for `∫_a^{a+1} dx/x`: the trapezoidal value
`1/(2a) + 1/(2(a+1))` exceeds `log(1 + 1/a)` by at most `1/(8a²) - 1/(8(a+1)²)`. Proved from the
series `log(1 + 1/a) = ∑_k 2/(2k+1) u^(2k+1)` with `u = 1/(2a+1)`, whose trapezoidal counterpart
is the geometric series `∑_k 2 u^(2k+1)`. -/
private theorem trapezoid_sub_log_one_add_inv_mem {a : ℝ} (ha : 0 < a) :
    0 ≤ (2 * a)⁻¹ + (2 * (a + 1))⁻¹ - Real.log (1 + a⁻¹) ∧
      (2 * a)⁻¹ + (2 * (a + 1))⁻¹ - Real.log (1 + a⁻¹) ≤
        (8 * a ^ 2)⁻¹ - (8 * (a + 1) ^ 2)⁻¹ := by
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
  refine ⟨sub_nonneg.2 (hasSum_le (fun k => ?_) hL hT), ?_⟩
  · have hk : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [k.cast_nonneg (α := ℝ)]
    have := pow_pos hu0 (2 * k + 1)
    nlinarith
  · have h0 := le_hasSum hL 0 fun j _ => by positivity
    have key : (8 * a ^ 2)⁻¹ - (8 * (a + 1) ^ 2)⁻¹ - ((2 * a)⁻¹ + (2 * (a + 1))⁻¹ - 2 * u) =
        (8 * a ^ 2 * (a + 1) ^ 2 * (2 * a + 1))⁻¹ := by
      rw [hu]
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
private theorem secondOrderError_add_mem {n : ℕ} (hn : n ≠ 0) (j : ℕ) :
    secondOrderError n ≤ secondOrderError (n + j) ∧
      secondOrderError (n + j) - secondOrderError n ≤
        (8 * (n : ℝ) ^ 2)⁻¹ - (8 * ((n + j : ℕ) : ℝ) ^ 2)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hnj : n + j ≠ 0 := by omega
    have hpos : (0 : ℝ) < (n + j : ℕ) := by exact_mod_cast Nat.pos_of_ne_zero hnj
    have hd := trapezoid_sub_log_one_add_inv_mem hpos
    rw [← secondOrderError_succ_sub hnj] at hd
    rw [← add_assoc]
    push_cast at hd ih ⊢
    constructor <;> linarith [ih.1, ih.2, hd.1, hd.2]

/-- **The second-order upper bound** `S₁(N) ≤ log N + γ + 1/(2N)` for `N ≥ 1`. -/
theorem harmonic_le_log_add_eulerMascheroniConstant_add_inv_two_mul {n : ℕ} (hn : n ≠ 0) :
    (harmonic n : ℝ) ≤ Real.log n + Real.eulerMascheroniConstant + (2 * (n : ℝ))⁻¹ := by
  have : secondOrderError n ≤ 0 := by
    refine ge_of_tendsto tendsto_secondOrderError ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact (secondOrderError_add_mem hn j).1
  rw [secondOrderError] at this
  linarith

/-- **The second-order lower bound** `log N + γ + 1/(2N) - 1/(8N²) ≤ S₁(N)` for `N ≥ 1`. -/
theorem log_add_eulerMascheroniConstant_add_inv_two_mul_sub_le_harmonic {n : ℕ} (hn : n ≠ 0) :
    Real.log n + Real.eulerMascheroniConstant + (2 * (n : ℝ))⁻¹ - (8 * (n : ℝ) ^ 2)⁻¹ ≤
      (harmonic n : ℝ) := by
  have : 0 - secondOrderError n ≤ (8 * (n : ℝ) ^ 2)⁻¹ := by
    refine le_of_tendsto (tendsto_secondOrderError.sub_const _) ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hm
    have := (secondOrderError_add_mem hn j).2
    have : (0 : ℝ) ≤ (8 * ((n + j : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
    linarith
  rw [secondOrderError] at this
  linarith

/-- **The second-order large-`N` asymptotics of the first harmonic sum**,
`S₁(N) = log N + γ + 1/(2N) + O(1/N²)`. -/
theorem isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_sub_inv_two_mul :
    (fun n : ℕ => (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant - (2 * (n : ℝ))⁻¹)
      =O[atTop] (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  refine IsBigO.of_bound 8⁻¹ ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h₁ := harmonic_le_log_add_eulerMascheroniConstant_add_inv_two_mul hn
  have h₂ := log_add_eulerMascheroniConstant_add_inv_two_mul_sub_le_harmonic hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (a := ((n : ℝ) ^ 2)⁻¹) (by positivity),
    abs_le, ← mul_inv]
  constructor <;> linarith

/-- **The large-`N` asymptotics of the first harmonic sum**, `S₁(N) = log N + γ + O(1/N)`. -/
theorem isBigO_harmonic_sub_log_sub_eulerMascheroniConstant :
    (fun n : ℕ => (harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant) =O[atTop]
      (fun n : ℕ => (n : ℝ)⁻¹) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ne_atTop 0] with n hn
  have h₁ := harmonic_le_log_add_eulerMascheroniConstant_add_inv_two_mul hn
  have h₂ := log_add_eulerMascheroniConstant_add_inv_two_mul_sub_le_harmonic hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
  -- both `1/(2N)` and `1/(8N²)` are at most `1/N`
  have h₃ : (2 * (n : ℝ))⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ (by positivity) (by linarith)
  have h₄ : (8 * (n : ℝ) ^ 2)⁻¹ ≤ (n : ℝ)⁻¹ := inv_anti₀ (by positivity) (by nlinarith)
  have h₅ : (0 : ℝ) ≤ (2 * (n : ℝ))⁻¹ := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (a := (n : ℝ)⁻¹) (by positivity), one_mul,
    abs_le]
  constructor <;> linarith

/-- **The large-`N` asymptotics of the digamma function**, `ψ(N) = log N - 1/(2N) + O(1/N²)`
along the positive integers. -/
theorem isBigO_digamma_natCast_sub_log_add_inv_two_mul :
    (fun n : ℕ => digamma n - Real.log n + (2 * (n : ℂ))⁻¹) =O[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  refine IsBigO.of_norm_left
    (isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_sub_inv_two_mul.norm_left.congr' ?_
      EventuallyEq.rfl)
  filter_upwards [eventually_ne_atTop 0] with n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [← Complex.norm_real]
  congr 1
  -- `ψ(k + 1) = S₁(k) - γ = S₁(k + 1) - 1/(k + 1) - γ`
  rw [harmonic_succ]
  push_cast
  rw [digamma_nat_add_one, mul_inv]
  ring

end EpsilonEridani
