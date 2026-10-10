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
theorem tMinElastic_nonpos (M xi : ℝ) (hM : 0 ≤ M) (h : xi < 1) (h0 : 0 ≤ xi) :
    tMinElastic M xi ≤ 0 := by
  rw [tMinElastic, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (pow_nonneg h0 2) (pow_nonneg hM 2)) (sub_nonneg.mpr h.le)

/-! ## Layer 0.2: the `β` variable -/

/-- The Bjorken-like variable `β` for diffractive scattering:
`x = ξ β`, so `β = x / ξ` when `ξ ≠ 0`. This captures the momentum fraction
of the struck parton relative to the Pomeron momentum. -/
noncomputable def beta (x xi : ℝ) : ℝ := x / xi

/-- **Layer 0.2**: the fundamental relation `x = ξ β`, valid for `ξ ≠ 0`. -/
lemma x_eq_xi_beta {x xi : ℝ} (hxi : xi ≠ 0) : x = xi * beta x xi := by
  rw [beta, mul_div_cancel₀ x hxi]

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
