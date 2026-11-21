/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import EpsilonEridani.Mathematics.HarmonicSum.Asymptotics

/-!
# Large-`N` asymptotics of the digamma function

Mathlib's digamma function `ψ = Γ'/Γ` (`Complex.digamma`) satisfies `ψ(N + 1) = S₁(N) - γ` at
the natural numbers (`Complex.digamma_nat_add_one`), with `S₁ = harmonic` the first harmonic sum
and `γ` the Euler–Mascheroni constant. From the large-`N` asymptotics of `harmonic` in
`EpsilonEridani.Mathematics.HarmonicSum.Asymptotics`, this file derives the expansion of `ψ`
along the positive integers:

* `EpsilonEridani.isBigO_digamma_natCast_sub_log_add_inv_two_mul_inv_sq`:
  `ψ(N) = log N - 1/(2N) + O(1/N²)`.
-/

@[expose] public section

open Complex Filter Asymptotics

namespace EpsilonEridani

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
