/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# Diffractive DIS Kinematics (Layer 0.2)

This module introduces diffractive kinematic quantities: the target-elastic `t`-boundary,
the `β` variable and its kinematic bounds.

-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive

/-! ## Layer 0.2: kinematic boundaries -/

/-- **Layer 0.2**: the kinematic boundary in `t` at fixed `ξ` in the target-elastic case, with
`M` the target mass.  At `t = tMinElastic M ξ` the process is elastic; `t > tMinElastic M ξ` is
the physical region.

The formula follows from the standard two-body kinematics of exclusive diffractive production:
the minimum momentum transfer for a given `(M, ξ)` is achieved when the struck system is the
massive target itself.

See `tMinElastic_nonpos` for the sign property. -/
noncomputable def tMinElastic (M xi : ℝ) : ℝ := -(xi ^ 2 * M ^ 2) / (1 - xi)

/-- **Layer 0.2**: `tMinElastic M xi ≤ 0` for all physical `ξ ∈ [0, 1)` and `M ≥ 0`.

The expression `ξ²M²/(1-ξ)` is non-negative in the stated range, so its negative is ≤ 0. -/
theorem tMinElastic_nonpos (M xi : ℝ) (hM : 0 ≤ M) (hxi1 : xi < 1) (hxi0 : 0 ≤ xi) :
    tMinElastic M xi ≤ 0 := by
  dsimp [tMinElastic]
  have hsqM : 0 ≤ M ^ 2 := pow_two_nonneg M
  have hsqxi : 0 ≤ xi ^ 2 := pow_two_nonneg xi
  have hnum : 0 ≤ xi ^ 2 * M ^ 2 := mul_nonneg hsqxi hsqM
  have hden : 0 ≤ 1 - xi := by linarith
  have hdiv : 0 ≤ (xi ^ 2 * M ^ 2) / (1 - xi) :=
    div_nonneg hnum hden
  linarith

/-! ## Layer 0.2: the `β` variable -/

/-- The Bjorken-like variable `β` for diffractive scattering:
`x = ξ β`, so `β = x / ξ` when `ξ ≠ 0`. This captures the momentum fraction
of the struck parton relative to the Pomeron momentum. -/
def beta (x xi : ℝ) : ℝ := x / xi

/-- For `ξ ≠ 0`, `β = x/ξ`. -/
lemma beta_eq_div {x xi : ℝ} (hxi : xi ≠ 0) : beta x xi = x / xi := rfl

/-- **Layer 0.2**: fundamental relation `x = ξ β` holds by definition. -/
lemma x_eq_xi_beta (x xi : ℝ) : x = xi * beta x xi := by
  dsimp [beta]
  by_cases hxi : xi = 0
  · subst hxi; ring
  · field_simp [hxi]

/-- For `β ∈ [0, 1]` at fixed `ξ ≥ 0`, `x ≤ ξ`.

The standard diffractive kinematic bound: when `x` is expressed as `ξ β` with `β ∈ [0,1]`,
the momentum fraction of the struck parton is bounded by `ξ`. -/
lemma x_le_xi_of_beta_le_one {x xi beta : ℝ} (hbeta : beta ≤ 1) (hxi_nonneg : 0 ≤ xi)
    (hx_eq : x = xi * beta) : x ≤ xi := by
  nlinarith

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
