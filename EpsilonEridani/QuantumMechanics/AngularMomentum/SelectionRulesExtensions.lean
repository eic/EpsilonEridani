/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import PhyslibAlpha.QuantumMechanics.AngularMomentum.SelectionRules

/-!
# The triangle rule for integral angular momenta

`PhyslibAlpha.Sl2.TriangleRule k m p` is the angular-momentum triangle rule in doubled units, so
that half-integral angular momenta are natural numbers. For integral angular momenta `a`, `b`, `c`
the doubled values `2 * a`, `2 * b`, `2 * c` have even sum, and the rule reduces to the three
triangle inequalities `|a - b| ≤ c ≤ a + b` (`PhyslibAlpha.Sl2.triangleRule_two_mul_iff`). This is
the form in which orbital angular momenta and the total spin of two spin-`1/2` particles couple.
-/

public section

namespace PhyslibAlpha.Sl2

/-- For integral angular momenta, the triangle rule in doubled units is the three triangle
inequalities `c ≤ a + b`, `a ≤ b + c` and `b ≤ a + c`. -/
theorem triangleRule_two_mul_iff {a b c : ℕ} :
    TriangleRule (2 * a) (2 * b) (2 * c) ↔ c ≤ a + b ∧ a ≤ b + c ∧ b ≤ a + c := by
  unfold TriangleRule
  omega

end PhyslibAlpha.Sl2
