/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
import EpsilonEridani.Mathematics.Analysis.Asymptotics.TruncatedExpansion

/-!
# Approximations to a given order in a small positive parameter

An expansion in a small positive parameter `λ`, such as a power-counting ratio of a factorization
theorem or the velocity of an effective field theory, is accurate to order `n` when it reproduces
the expanded function up to a remainder `O(λ ^ n)` as `λ → 0⁺`. This module names that relation,
`ApproximatesToOrder`, records that it weakens as the order decreases and is reflexive, symmetric
and transitive, and proves that the coefficient of a correction to such an approximation is
unique: two coefficients that each improve an approximation from order `n` to order `n + 1` are
equal, and a nonvanishing one is detectable in the accuracy of the approximation without it.

The limit is taken from *above*, along `𝓝[>] 0`: the parameter is positive, and it is positivity
that makes `λ ^ n` nonvanishing along the filter, on which the uniqueness of the coefficients of
such expansions depends.

## Main definitions

* `ApproximatesToOrder W Wapp n`: `W λ - Wapp λ = O(λ ^ n)` as `λ → 0⁺`
  (`approximatesToOrder_def`).

## Main results

* `ApproximatesToOrder.mono`: an approximation accurate to order `n` is accurate to every lower
  order.
* `ApproximatesToOrder.refl`, `ApproximatesToOrder.symm`, `ApproximatesToOrder.trans`: the
  relation to a fixed order is reflexive, symmetric and transitive.
* `ApproximatesToOrder.congr_sub`: it depends on the two functions only through their difference.
* `ApproximatesToOrder.coeff_unique`: the coefficient of a correction that improves an
  approximation from order `n` to order `n + 1` is unique: it is fixed by the expanded function
  and its lower-order approximation, and is not a convention.
* `ApproximatesToOrder.of_add_mul_pow`: a correction is genuinely subleading: without it, the
  approximation is still accurate to order `n`.
* `ApproximatesToOrder.not_succ_of_coeff_ne_zero`: a nonvanishing correction
  is detectable: without it, the approximation is not accurate to order `n + 1`.
-/

public section

open Filter Topology Asymptotics

namespace EpsilonEridani

/-- `ApproximatesToOrder W Wapp n` states that `Wapp` reproduces `W` with a remainder
bounded by `λ ^ n` as the small parameter `λ` tends to zero from above,
`W λ - Wapp λ = O(λ ^ n)`. -/
def ApproximatesToOrder (W Wapp : ℝ → ℝ) (n : ℕ) : Prop :=
  (fun lam => W lam - Wapp lam) =O[𝓝[>] 0] fun lam => lam ^ n

/-- Unfolding `ApproximatesToOrder` into its remainder bound. -/
theorem approximatesToOrder_def {W Wapp : ℝ → ℝ} {n : ℕ} :
    ApproximatesToOrder W Wapp n ↔ (fun lam => W lam - Wapp lam) =O[𝓝[>] 0] fun lam => lam ^ n :=
  Iff.rfl

/-- Every function approximates itself to every order. -/
lemma ApproximatesToOrder.refl (W : ℝ → ℝ) (n : ℕ) : ApproximatesToOrder W W n := by
  simpa only [ApproximatesToOrder, sub_self] using isBigO_zero (fun lam : ℝ => lam ^ n) (𝓝[>] 0)

/-- An approximation accurate to order `n` is accurate to every lower order. -/
lemma ApproximatesToOrder.mono {W Wapp : ℝ → ℝ} {m n : ℕ}
    (h : ApproximatesToOrder W Wapp n) (hmn : m ≤ n) :
    ApproximatesToOrder W Wapp m :=
  Asymptotics.IsBigO.trans h ((isBigO_pow_pow hmn).mono nhdsWithin_le_nhds)

/-- An approximation accurate to order `n` stays so when the functions are changed without
changing their difference. -/
lemma ApproximatesToOrder.congr_sub {W Wapp W' Wapp' : ℝ → ℝ} {n : ℕ}
    (h : ApproximatesToOrder W Wapp n) (he : ∀ lam, W lam - Wapp lam = W' lam - Wapp' lam) :
    ApproximatesToOrder W' Wapp' n :=
  Asymptotics.IsBigO.congr_left h he

/-- Approximation is symmetric in the two functions: negating the remainder preserves its
bound. -/
lemma ApproximatesToOrder.symm {W Wapp : ℝ → ℝ} {n : ℕ} (h : ApproximatesToOrder W Wapp n) :
    ApproximatesToOrder Wapp W n :=
  (IsBigO.neg_left h).congr_left fun lam => neg_sub (W lam) (Wapp lam)

/-- If `W₂` approximates `W₁` and `W₃` approximates `W₂` to order `n`, then `W₃` approximates `W₁`
to order `n`. -/
lemma ApproximatesToOrder.trans {W₁ W₂ W₃ : ℝ → ℝ} {n : ℕ}
    (h₁₂ : ApproximatesToOrder W₁ W₂ n) (h₂₃ : ApproximatesToOrder W₂ W₃ n) :
    ApproximatesToOrder W₁ W₃ n :=
  (Asymptotics.IsBigO.add h₁₂ h₂₃).congr_left fun _ => sub_add_sub_cancel _ _ _

/-! ### Uniqueness of the coefficient of a correction -/

/-- **The coefficient of a correction at a given order is unique.** If two coefficients each
improve an approximation from order `n` to order `n + 1`, they are equal.

The coefficient is therefore a determination made by the expanded function together with its
lower-order approximation, and not a convention of whoever writes the expansion down. -/
lemma ApproximatesToOrder.coeff_unique {W Wlp : ℝ → ℝ} {n : ℕ} {c₁ c₂ : ℝ}
    (h₁ : ApproximatesToOrder W (fun lam => Wlp lam + c₁ * lam ^ n) (n + 1))
    (h₂ : ApproximatesToOrder W (fun lam => Wlp lam + c₂ * lam ^ n) (n + 1)) :
    c₁ = c₂ := by
  have hdiff : (fun lam : ℝ => (c₂ - c₁) * lam ^ n) =O[𝓝[>] 0]
      fun lam : ℝ => lam ^ (n + 1) :=
    (approximatesToOrder_def.1 (h₂.symm.trans h₁)).congr_left fun lam => by ring
  have hz := eq_zero_of_isBigO_pow_smul_pow_succ (nhdsGT_le_nhdsNE 0)
    (hdiff.congr_left fun lam => by rw [smul_eq_mul, mul_comm])
  linarith

/-- **The lower-order approximation keeps its own accuracy.** If including the order-`n`
coefficient gives an approximation accurate to order `n + 1`, then the lower-order approximation
on its own is accurate to order `n`: the correction is genuinely subleading. -/
lemma ApproximatesToOrder.of_add_mul_pow {W Wlp : ℝ → ℝ} {n : ℕ} {c : ℝ}
    (h : ApproximatesToOrder W (fun lam => Wlp lam + c * lam ^ n) (n + 1)) :
    ApproximatesToOrder W Wlp n := by
  have hlow : (fun lam : ℝ => W lam - (Wlp lam + c * lam ^ n)) =O[𝓝[>] 0]
      fun lam : ℝ => lam ^ n := approximatesToOrder_def.1 (h.mono (Nat.le_succ n))
  have hcorr : (fun lam : ℝ => c * lam ^ n) =O[𝓝[>] 0] fun lam : ℝ => lam ^ n :=
    (isBigO_refl (fun lam : ℝ => lam ^ n) (𝓝[>] 0)).const_mul_left c
  have hsum : (fun lam : ℝ => W lam - Wlp lam) =O[𝓝[>] 0] fun lam : ℝ => lam ^ n := by
    refine (hlow.add hcorr).congr_left ?_
    intro lam
    ring
  exact approximatesToOrder_def.2 hsum

/-- **A nonvanishing correction is detectable.** If the order-`n` coefficient is nonzero then the
lower-order approximation alone is *not* accurate to order `n + 1`.

Together with `ApproximatesToOrder.coeff_unique` this is what keeps an interface of correction
coefficients from being vacuous: the correction can neither be dropped nor be chosen. -/
lemma ApproximatesToOrder.not_succ_of_coeff_ne_zero {W Wlp : ℝ → ℝ} {n : ℕ}
    {c : ℝ} (h : ApproximatesToOrder W (fun lam => Wlp lam + c * lam ^ n) (n + 1))
    (hc : c ≠ 0) : ¬ ApproximatesToOrder W Wlp (n + 1) := by
  intro hlp
  have hzero : ApproximatesToOrder W (fun lam => Wlp lam + 0 * lam ^ n) (n + 1) :=
    hlp.congr_sub fun lam => by ring
  exact hc (h.coeff_unique hzero)

end EpsilonEridani
