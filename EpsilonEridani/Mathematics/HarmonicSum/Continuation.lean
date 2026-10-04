/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import EpsilonEridani.Mathematics.HarmonicSum.Asymptotics

/-!
# The meromorphic continuation of the first harmonic sum

The first harmonic sum `S₁(N) = ∑_{i=1}^{N} 1/i` (Mathlib's `harmonic`) is defined for natural `N`
only. Through the digamma function `ψ = Γ'/Γ` (`Complex.digamma`) it continues to the meromorphic
function

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

From the large-`N` bounds on `harmonic` in `EpsilonEridani.Mathematics.HarmonicSum.Asymptotics`,
the file also derives the expansion `ψ(N) = log N - 1/(2N) + O(1/N²)` of the digamma function
along the positive integers.

## Main definitions

* `EpsilonEridani.complexHarmonic`: the continuation `s ↦ ψ(s + 1) + γ` of `S₁`.

## Main statements

* `EpsilonEridani.complexHarmonic_natCast`: `complexHarmonic n = harmonic n`.
* `EpsilonEridani.complexHarmonic_add_one`: the recurrence `S₁(s + 1) = S₁(s) + 1/(s + 1)`.
* `EpsilonEridani.complexHarmonic_neg`: the reflection formula.
* `EpsilonEridani.analyticAt_Gamma` and `EpsilonEridani.analyticAt_digamma`: analyticity of `Γ`
  and `ψ` away from the non-positive integers.
* `EpsilonEridani.analyticAt_complexHarmonic`: analyticity away from the negative integers.
* `EpsilonEridani.meromorphicOrderAt_complexHarmonic_neg_nat_sub_one` and
  `EpsilonEridani.tendsto_mul_complexHarmonic_neg_nat_sub_one`: a simple pole with residue `-1`
  at each negative integer.
* `EpsilonEridani.isBigO_digamma_natCast_sub_log_add_inv_two_mul_inv_sq`:
  `ψ(N) = log N - 1/(2N) + O(1/N²)`.

## References

* J. Blümlein and S. Kurth, *Harmonic sums and Mellin transforms up to two-loop order*,
  Phys. Rev. D 60 (1999) 014018, arXiv:hep-ph/9810241.
* J. Blümlein, *Analytic continuation of Mellin transforms up to two-loop order*,
  Comput. Phys. Commun. 133 (2000) 76, arXiv:hep-ph/0003100.
-/

@[expose] public section

open Complex Filter Topology Asymptotics
open scoped Real

namespace EpsilonEridani

/-- `Γ` is analytic away from its poles `0, -1, -2, …`. -/
@[fun_prop]
theorem analyticAt_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : AnalyticAt ℂ Gamma s := by
  -- `Γ` is the reciprocal of the entire function `1/Γ`, which does not vanish at `s`.
  have h := (differentiable_one_div_Gamma.analyticAt s).inv (inv_ne_zero (Gamma_ne_zero hs))
  simpa only [Pi.inv_def, inv_inv] using h

/-- The digamma function `ψ = Γ'/Γ` is analytic away from its poles `0, -1, -2, …`. -/
@[fun_prop]
theorem analyticAt_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -m) : AnalyticAt ℂ digamma s := by
  have hΓ := analyticAt_Gamma hs
  rw [digamma_def, logDeriv]
  exact hΓ.deriv.div hΓ (Gamma_ne_zero hs)

/-- The meromorphic continuation of the first harmonic sum `S₁(N) = harmonic N` to complex
argument via the digamma function, `S₁(s) = ψ(s + 1) + γ`, with `γ` the Euler–Mascheroni
constant. It is meromorphic, with simple poles at the negative integers.

This is the standard continuation used in the literature, not the unique one: the naturals have
no accumulation point in `ℂ`, so the values `harmonic n` alone do not determine an analytic
extension. It agrees with `harmonic` on `ℕ` (`complexHarmonic_natCast`) and inherits the
recurrence of `ψ` (`complexHarmonic_add_one`). -/
noncomputable def complexHarmonic (s : ℂ) : ℂ :=
  digamma (s + 1) + Real.eulerMascheroniConstant

theorem complexHarmonic_def (s : ℂ) :
    complexHarmonic s = digamma (s + 1) + Real.eulerMascheroniConstant :=
  (rfl)

theorem complexHarmonic_eq :
    complexHarmonic = fun s => digamma (s + 1) + Real.eulerMascheroniConstant :=
  funext complexHarmonic_def

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
  rw [complexHarmonic_def, complexHarmonic_def, add_right_comm s (n : ℂ) 1,
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
  rw [complexHarmonic_eq]
  fun_prop

/-- The continuation is analytic away from the negative integers. -/
@[fun_prop]
theorem analyticAt_complexHarmonic {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m + 1)) :
    AnalyticAt ℂ complexHarmonic s := by
  rw [complexHarmonic_eq]
  exact ((analyticAt_digamma (add_one_ne_neg_natCast hs)).comp_of_eq
    (f := fun z => z + 1) (by fun_prop) rfl).add analyticAt_const

@[fun_prop]
theorem continuousAt_complexHarmonic {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m + 1)) :
    ContinuousAt complexHarmonic s :=
  (analyticAt_complexHarmonic hs).continuousAt

/-- Near a negative integer `-(m + 1)`, every other point avoids the negative integers. -/
theorem eventually_ne_neg_nat_sub_one (m : ℕ) :
    ∀ᶠ s in 𝓝[≠] (-(m + 1 : ℂ)), ∀ j : ℕ, s ≠ -(j + 1 : ℂ) := by
  -- the integers other than `-(m + 1)` form a closed subset of `ℂ`
  have hc := isClosedEmbedding_intCast.isClosedMap _ (isClosed_discrete {n : ℤ | n ≠ -(m + 1)})
  have hm : -(m + 1 : ℂ) ∈ (((↑) : ℤ → ℂ) '' {n : ℤ | n ≠ -(m + 1)})ᶜ := by
    rintro ⟨n, hn, hn'⟩
    exact hn (by exact_mod_cast hn')
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hc.isOpen_compl.mem_nhds hm)]
    with s hne hs j hj
  subst hj
  refine hs ⟨-(j + 1), fun h => hne ?_, by push_cast; rfl⟩
  simp [show j = m by omega]

/-- The regular part at the negative integer `-(m + 1)`: the function
`s ↦ S₁(s + m + 1) - ∑_{k<m} 1/(s + k + 1)`, which differs from `S₁` by the polar term
`1/(s + m + 1)` and is analytic at `-(m + 1)`. -/
private noncomputable def regularPart (m : ℕ) (s : ℂ) : ℂ :=
  complexHarmonic (s + (m + 1 : ℕ)) - ∑ k ∈ Finset.range m, (s + k + 1)⁻¹

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

/-- The Laurent presentation of the continuation at the negative integer `-(m + 1)`:
`S₁(s) = (s + m + 1)⁻¹ g(s)` with `g` analytic and `g(-(m + 1)) = -1`. -/
private theorem complexHarmonic_presentation (m : ℕ) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g (-(m + 1 : ℂ)) ∧ g (-(m + 1 : ℂ)) = -1 ∧
      complexHarmonic =ᶠ[𝓝[≠] (-(m + 1 : ℂ))]
        fun s => (s - -(m + 1 : ℂ)) ^ (-1 : ℤ) • g s := by
  refine ⟨fun s => (s + (m + 1)) * regularPart m s - 1, ?_, by simp, ?_⟩
  · exact ((analyticAt_id.add analyticAt_const).mul (analyticAt_regularPart m)).sub
      analyticAt_const
  · filter_upwards [eventually_ne_neg_nat_sub_one m, self_mem_nhdsWithin] with s hs hne
    have hne' : s + (m + 1) ≠ 0 := by
      rwa [← sub_neg_eq_add, sub_ne_zero]
    have hr : complexHarmonic s = regularPart m s - (s + (m + 1))⁻¹ := by
      rw [regularPart, complexHarmonic_add_nat hs, Finset.sum_range_succ]
      ring
    rw [hr, sub_neg_eq_add, zpow_neg_one, smul_eq_mul]
    field_simp

/-- **The pole structure**: the continuation has a simple pole at every negative integer. -/
theorem meromorphicOrderAt_complexHarmonic_neg_nat_sub_one (m : ℕ) :
    meromorphicOrderAt complexHarmonic (-(m + 1 : ℂ)) = -1 := by
  obtain ⟨g, hg, hg₁, h⟩ := complexHarmonic_presentation m
  rw [← WithTop.coe_one, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
    meromorphicOrderAt_eq_int_iff (meromorphic_complexHarmonic _)]
  exact ⟨g, hg, by rw [hg₁]; exact neg_ne_zero.2 one_ne_zero, h⟩

/-- **The residue** of the continuation at every negative integer is `-1`:
`(s + m + 1) S₁(s) → -1` as `s → -(m + 1)`. -/
theorem tendsto_mul_complexHarmonic_neg_nat_sub_one (m : ℕ) :
    Tendsto (fun s => (s + (m + 1)) * complexHarmonic s) (𝓝[≠] (-(m + 1 : ℂ))) (𝓝 (-1)) := by
  obtain ⟨g, hg, hg₁, h⟩ := complexHarmonic_presentation m
  have ht := MeromorphicAt.tendsto_nhds_meromorphicTrailingCoeffAt
    (meromorphic_complexHarmonic (-(m + 1 : ℂ)))
  rw [meromorphicOrderAt_complexHarmonic_neg_nat_sub_one,
    hg.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
      (by rw [hg₁]; exact neg_ne_zero.2 one_ne_zero) h, hg₁] at ht
  -- the order `-1` turns `(· + (m + 1)) ^ (-order) • S₁` into `(· + (m + 1)) * S₁`
  refine ht.congr fun s => ?_
  simp only [Pi.smul_apply', Pi.pow_apply, smul_eq_mul]
  rw [← WithTop.coe_one, ← WithTop.LinearOrderedAddCommGroup.coe_neg, WithTop.untop₀_coe,
    neg_neg, zpow_one, sub_neg_eq_add]

/-- **The large-`N` asymptotics of the digamma function**, `ψ(N) = log N - 1/(2N) + O(1/N²)`
along the positive integers. -/
theorem isBigO_digamma_natCast_sub_log_add_inv_two_mul_inv_sq :
    (fun n : ℕ => digamma n - Real.log n + (2 * (n : ℂ))⁻¹) =O[atTop]
      (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
  refine IsBigO.of_norm_left
    (isBigO_harmonic_sub_log_sub_eulerMascheroniConstant_sub_inv_two_mul_inv_sq.norm_left.congr'
      ?_ EventuallyEq.rfl)
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
