/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Truncated expansions that are small at the origin

A polynomial `∑_{k ≤ n} x ^ k • a k` of degree at most `n` in `x`, with coefficients `a k` in a
normed space, that is `o(x ^ n)` as `x → 0` has all its coefficients equal to zero. This is the
uniqueness of a truncated expansion at the origin: two expansions to order `n` whose difference is
of higher order have the same coefficients.

The statement only asks for smallness along a nontrivial filter `l` (`[l.NeBot]`) on the punctured
neighbourhoods of `0`, for instance `𝓝[>] 0` on `ℝ`, so a one-sided expansion already determines
its coefficients. The uniqueness of power series, `HasFPowerSeriesAt.eq_formalMultilinearSeries`,
instead compares two expansions that both converge on a whole neighbourhood of the origin.

## Main results

* `Asymptotics.coeff_zero_eq_zero_of_isLittleO_sum_range_pow_smul_pow`: the constant term of a
  polynomial of degree at most `n` that is `o(x ^ n)` along a nontrivial filter on the
  neighbourhoods of `0`, punctured or not, vanishes.
* `Asymptotics.isLittleO_sum_range_pow_smul_pow_iff`: a polynomial of degree at most `n` is
  `o(x ^ n)` along `l` exactly when all its coefficients vanish.
* `Asymptotics.isBigO_sum_range_pow_smul_pow_succ_iff`: the same with the remainder `O(x ^ (n + 1))`
  that a truncated expansion carries.
* `Asymptotics.eq_zero_of_isBigO_pow_smul_pow_succ`: the one-monomial case, a monomial `x ^ n • c`
  that is `O(x ^ (n + 1))` has vanishing coefficient.
* `Asymptotics.isBigO_pow_pow`: near `0` a higher power is dominated by a lower one, so a
  truncated expansion to a higher order is also one to every lower order.
-/

public section

open Filter Finset Topology

namespace Asymptotics

section PowPow

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-- Near `0` a higher power is dominated by a lower one: the non-strict companion of Mathlib's
`Asymptotics.isLittleO_pow_pow`, from which it is derived. -/
theorem isBigO_pow_pow {m n : ℕ} (h : m ≤ n) : (fun x : 𝕜 => x ^ n) =O[𝓝 0] fun x => x ^ m := by
  rcases h.eq_or_lt with rfl | h
  · exact isBigO_refl _ _
  · exact (isLittleO_pow_pow h).isBigO

end PowPow

variable {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {l : Filter 𝕜} [l.NeBot]

/-- The constant term of a polynomial of degree at most `n` that is `o(x ^ n)` along a nontrivial
filter on the neighbourhoods of `0` vanishes. The filter need not be punctured, so this applies
along `𝓝 0` itself, where only the constant term is determined. -/
theorem coeff_zero_eq_zero_of_isLittleO_sum_range_pow_smul_pow (hl₀ : l ≤ 𝓝 0) {n : ℕ}
    {a : ℕ → E} (h : (fun x => ∑ k ∈ range (n + 1), x ^ k • a k) =o[l] fun x => x ^ n) :
    a 0 = 0 := by
  have hc : Continuous fun x : 𝕜 => ∑ k ∈ range (n + 1), x ^ k • a k := by fun_prop
  have hlim : Tendsto (fun x : 𝕜 => ∑ k ∈ range (n + 1), x ^ k • a k) l (𝓝 (a 0)) := by
    simpa [sum_range_succ'] using hc.continuousAt.tendsto.mono_left hl₀
  have hpow : (fun x : 𝕜 => x ^ n) =O[l] fun _ => (1 : 𝕜) :=
    ((continuous_pow n).continuousAt.tendsto.mono_left hl₀).isBigO_one 𝕜
  exact tendsto_nhds_unique hlim ((isLittleO_one_iff 𝕜).1 (h.trans_isBigO hpow))

/-- A polynomial of degree at most `n` with vanishing coefficients vanishes identically. -/
private theorem sum_range_pow_smul_eq_zero {n : ℕ} {a : ℕ → E} (h : ∀ k ≤ n, a k = 0) (x : 𝕜) :
    ∑ k ∈ range (n + 1), x ^ k • a k = 0 :=
  sum_eq_zero fun k hk => by rw [h k (Nat.lt_succ_iff.1 (mem_range.1 hk)), smul_zero]

/-- A polynomial of degree at most `n` that is `o(x ^ n)` along a nontrivial filter on the
punctured neighbourhoods of `0` has vanishing coefficients. -/
private theorem eq_zero_of_isLittleO_sum_range_pow_smul_pow (hl : l ≤ 𝓝[≠] 0) {n : ℕ}
    {a : ℕ → E} (h : (fun x => ∑ k ∈ range (n + 1), x ^ k • a k) =o[l] fun x => x ^ n) :
    ∀ k ≤ n, a k = 0 := by
  have hl₀ : l ≤ 𝓝 0 := hl.trans nhdsWithin_le_nhds
  induction n generalizing a with
  | zero =>
    intro k hk
    rw [Nat.le_zero.1 hk]
    exact coeff_zero_eq_zero_of_isLittleO_sum_range_pow_smul_pow hl₀ h
  | succ m ih =>
    have ha₀ := coeff_zero_eq_zero_of_isLittleO_sum_range_pow_smul_pow hl₀ h
    -- divide off the vanishing constant term: the sum is `x` times a polynomial of degree `≤ m`
    have hsplit : ∀ x : 𝕜, ∑ k ∈ range (m + 1 + 1), x ^ k • a k =
        x • ∑ k ∈ range (m + 1), x ^ k • a (k + 1) := fun x => by
      rw [sum_range_succ', smul_sum]
      simp [ha₀, pow_succ', mul_smul]
    have hx : ∀ᶠ x in l, x ≠ 0 := hl self_mem_nhdsWithin
    have hdiv : (fun x => ∑ k ∈ range (m + 1), x ^ k • a (k + 1)) =o[l] fun x => x ^ m := by
      refine ((isBigO_refl (fun x : 𝕜 => x⁻¹) l).smul_isLittleO h).congr' ?_ ?_ <;>
        filter_upwards [hx] with x hx
      · rw [hsplit, smul_smul, inv_mul_cancel₀ hx, one_smul]
      · rw [smul_eq_mul, pow_succ', ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
    intro k hk
    rcases k with _ | k
    · exact ha₀
    · exact ih hdiv k (Nat.le_of_succ_le_succ hk)

/-- **Uniqueness of a truncated expansion at the origin.** A polynomial of degree at most `n` is
`o(x ^ n)` along a nontrivial filter on the punctured neighbourhoods of `0` exactly when all its
coefficients vanish. -/
theorem isLittleO_sum_range_pow_smul_pow_iff (hl : l ≤ 𝓝[≠] 0) {n : ℕ} {a : ℕ → E} :
    ((fun x => ∑ k ∈ range (n + 1), x ^ k • a k) =o[l] fun x => x ^ n) ↔ ∀ k ≤ n, a k = 0 := by
  refine ⟨eq_zero_of_isLittleO_sum_range_pow_smul_pow hl, fun h => ?_⟩
  simpa only [sum_range_pow_smul_eq_zero h] using isLittleO_zero (fun x : 𝕜 => x ^ n) l

/-- A polynomial of degree at most `n` is `O(x ^ (n + 1))` along a nontrivial filter on the
punctured neighbourhoods of `0` exactly when all its coefficients vanish. -/
theorem isBigO_sum_range_pow_smul_pow_succ_iff (hl : l ≤ 𝓝[≠] 0) {n : ℕ} {a : ℕ → E} :
    ((fun x => ∑ k ∈ range (n + 1), x ^ k • a k) =O[l] fun x => x ^ (n + 1)) ↔
      ∀ k ≤ n, a k = 0 := by
  refine ⟨fun h => (isLittleO_sum_range_pow_smul_pow_iff hl).1 <| h.trans_isLittleO <|
    (isLittleO_pow_pow n.lt_succ_self).mono (hl.trans nhdsWithin_le_nhds), fun h => ?_⟩
  simpa only [sum_range_pow_smul_eq_zero h] using isBigO_zero (fun x : 𝕜 => x ^ (n + 1)) l

/-- A monomial `x ^ n • c` that is `O(x ^ (n + 1))` along a nontrivial filter on the punctured
neighbourhoods of `0` has vanishing coefficient. -/
theorem eq_zero_of_isBigO_pow_smul_pow_succ (hl : l ≤ 𝓝[≠] 0) {n : ℕ} {c : E}
    (h : (fun x => x ^ n • c) =O[l] fun x => x ^ (n + 1)) : c = 0 := by
  have hsum : ∀ x : 𝕜, ∑ k ∈ range (n + 1), x ^ k • Pi.single n c k = x ^ n • c := fun x => by
    simp [Pi.single_apply]
  have := (isBigO_sum_range_pow_smul_pow_succ_iff hl (a := Pi.single n c)).1
    (h.congr_left fun x => (hsum x).symm) n le_rfl
  rwa [Pi.single_eq_same] at this

end Asymptotics
