/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SelectionRules

/-!
# The triangle rule as triangle inequalities

`PhyslibAlpha.Sl2.TriangleRule k m p` is the angular-momentum triangle rule in doubled units, so
that half-integral angular momenta are natural numbers. When the doubled values have even sum, the
rule reduces to the three triangle inequalities `|k - m| ≤ p ≤ k + m`
(`PhyslibAlpha.Sl2.triangleRule_iff_of_even`). The even-sum case covers every coupling of two
integral angular momenta to an integral one, every coupling of two half-integral angular momenta
to an integral one, such as the two nucleon spins to the total spin, and every coupling of a
half-integral and an integral angular momentum to a half-integral one, such as a half-integral
spin and an orbital angular momentum; it is the parity condition `(k + m + p) % 2 = 0` that every
coupling allowed by the triangle rule satisfies. For three integral angular momenta `a`, `b`, `c`
the doubled values are `2 * a`, `2 * b`, `2 * c` (`PhyslibAlpha.Sl2.triangleRule_two_mul_iff`);
this is the form in which orbital angular momenta and the total spin of two spin-`1/2` particles
couple.
-/

public section

namespace PhyslibAlpha.Sl2

/-- When the doubled angular momenta have even sum, the triangle rule is the three triangle
inequalities `p ≤ k + m`, `k ≤ m + p` and `m ≤ k + p`. -/
theorem triangleRule_iff_of_even {k m p : ℕ} (h : (k + m + p) % 2 = 0) :
    TriangleRule k m p ↔ p ≤ k + m ∧ k ≤ m + p ∧ m ≤ k + p := by
  unfold TriangleRule
  omega

/-- For integral angular momenta, the triangle rule in doubled units is the three triangle
inequalities `c ≤ a + b`, `a ≤ b + c` and `b ≤ a + c`. -/
theorem triangleRule_two_mul_iff {a b c : ℕ} :
    TriangleRule (2 * a) (2 * b) (2 * c) ↔ c ≤ a + b ∧ a ≤ b + c ∧ b ≤ a + c := by
  rw [triangleRule_iff_of_even (by omega)]
  omega

end PhyslibAlpha.Sl2
