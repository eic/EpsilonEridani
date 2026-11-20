/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Approximations to a given order in a small positive parameter

An expansion in a small positive parameter `λ`, such as a power-counting ratio of a factorization
theorem or the velocity of an effective field theory, is accurate to order `n` when it reproduces
the expanded function up to a remainder `O(λ ^ n)` as `λ → 0⁺`. This module names that relation,
`ApproximatesToOrder`, and records that it weakens as the order decreases and is reflexive and
transitive.

The limit is taken from *above*, along `𝓝[>] 0`: the parameter is positive, and it is positivity
that makes `λ ^ n` nonvanishing along the filter, on which the uniqueness of the coefficients of
such expansions depends.

## Main definitions

* `ApproximatesToOrder W Wapp n`: `W λ - Wapp λ = O(λ ^ n)` as `λ → 0⁺`.

## Main results

* `ApproximatesToOrder.mono`: an approximation accurate to order `n` is accurate to every lower
  order.
* `ApproximatesToOrder.refl`, `ApproximatesToOrder.trans`: the relation to a fixed order is
  reflexive and transitive.
-/

@[expose] public section

open Filter Topology Asymptotics

namespace EpsilonEridani

/-- `ApproximatesToOrder W Wapp n` states that `Wapp` reproduces `W` with a remainder
bounded by `λ ^ n` as the small parameter `λ` tends to zero from above,
`W λ - Wapp λ = O(λ ^ n)`. -/
def ApproximatesToOrder (W Wapp : ℝ → ℝ) (n : ℕ) : Prop :=
  (fun lam => W lam - Wapp lam) =O[𝓝[>] 0] fun lam => lam ^ n

/-- Every function approximates itself to every order. -/
lemma ApproximatesToOrder.refl (W : ℝ → ℝ) (n : ℕ) : ApproximatesToOrder W W n := by
  simpa only [ApproximatesToOrder, sub_self] using isBigO_zero (fun lam : ℝ => lam ^ n) (𝓝[>] 0)

/-- Near `0⁺` a higher power of the small parameter is dominated by a lower one. -/
lemma isBigO_pow_of_le {m n : ℕ} (hmn : m ≤ n) :
    (fun lam : ℝ => lam ^ n) =O[𝓝[>] 0] fun lam : ℝ => lam ^ m :=
  hmn.lt_or_eq.elim (fun h => (isLittleO_pow_pow h).isBigO.mono nhdsWithin_le_nhds)
    fun h => h ▸ isBigO_refl _ _

/-- An approximation accurate to order `n` is accurate to every lower order. -/
lemma ApproximatesToOrder.mono {W Wapp : ℝ → ℝ} {m n : ℕ}
    (h : ApproximatesToOrder W Wapp n) (hmn : m ≤ n) :
    ApproximatesToOrder W Wapp m :=
  Asymptotics.IsBigO.trans h (isBigO_pow_of_le hmn)

/-- If `W₂` approximates `W₁` and `W₃` approximates `W₂` to order `n`, then `W₃` approximates `W₁`
to order `n`. -/
lemma ApproximatesToOrder.trans {W₁ W₂ W₃ : ℝ → ℝ} {n : ℕ}
    (h₁₂ : ApproximatesToOrder W₁ W₂ n) (h₂₃ : ApproximatesToOrder W₂ W₃ n) :
    ApproximatesToOrder W₁ W₃ n :=
  (Asymptotics.IsBigO.add h₁₂ h₂₃).congr_left fun _ => sub_add_sub_cancel _ _ _

end EpsilonEridani
