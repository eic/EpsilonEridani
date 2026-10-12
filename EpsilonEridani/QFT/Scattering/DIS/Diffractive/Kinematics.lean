/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
/-!

# Diffractive DIS Kinematics (Layers 0.1 and 0.2)

This module introduces the kinematics of diffractive DIS: the invariant scalar products of a
diffractive event (Layer 0.1), from which the momentum fractions `x`, `ξ` and `β` are derived, and
the target-elastic boundary of the physical region in `t` (Layer 0.2).

The kinematics are carried by the invariant scalar products rather than by the momentum
fractions, so that the fundamental relation `x = ξ β` is a theorem about the definitions and not a
definition that assumes itself.

-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive

/-! ## Layer 0.1: the diffractive invariants -/

/-- The invariants of a diffractive event, with `Pq = P · q`, `Dq = Δ · q` for `Δ = P - P'`,
`Q2 = -q²` and `t = Δ²`. Carrying the scalar products rather than the momentum fractions is what
makes `x = ξ β` provable rather than true by definition: the momentum fractions are derived from
these fields, so the identity between them is a cancellation of `P · q`, not a stipulation. -/
structure Invariants where
  /-- `P · q`, positive in the physical region. -/
  Pq : ℝ
  /-- `Δ · q` with `Δ = P - P'`, positive in the physical region. -/
  Dq : ℝ
  /-- Photon virtuality `Q² = -q²`. -/
  Q2 : ℝ
  /-- Invariant momentum transfer to the target, non-positive throughout (Convention 2). -/
  t : ℝ
  /-- Positivity of `P · q` in the physical region. -/
  Pq_pos : 0 < Pq
  /-- Positivity of `Δ · q` in the physical region. -/
  Dq_pos : 0 < Dq
  /-- Positivity of the photon virtuality. -/
  Q2_pos : 0 < Q2
  /-- Non-positivity of the momentum transfer, per Convention 2. -/
  t_nonpos : t ≤ 0

namespace Invariants

/-- The inclusive Bjorken variable, `x = Q² / (2 P·q)`. -/
noncomputable def x (i : Invariants) : ℝ := i.Q2 / (2 * i.Pq)

/-- The momentum fraction lost by the target, `ξ = Δ·q / P·q`. -/
noncomputable def xi (i : Invariants) : ℝ := i.Dq / i.Pq

/-- The parton's fraction of the exchanged momentum, `β = Q² / (2 Δ·q)`. -/
noncomputable def beta (i : Invariants) : ℝ := i.Q2 / (2 * i.Dq)

/-- **Layer 0.1**: the fundamental relation `x = ξ β`, the identity that licenses calling `β` a
momentum fraction of the exchange. Exact, with no mass or high-energy approximation: the proof
cancels the `P·q` shared by the two denominators,
`Q² / (2 P·q) = (Δ·q / P·q) · (Q² / (2 Δ·q))`. -/
theorem x_eq_xi_mul_beta (i : Invariants) : i.x = i.xi * i.beta := by
  have hPq : i.Pq ≠ 0 := ne_of_gt i.Pq_pos
  have hDq : i.Dq ≠ 0 := ne_of_gt i.Dq_pos
  rw [x, xi, beta]
  field_simp

/-- **Layer 0.2**: the diffractive kinematic bound `x ≤ ξ` when `β ≤ 1`.

The bound is derived from the proved identity `x_eq_xi_mul_beta` together with the
non-negativity of `ξ` in the physical region (both `Δ·q` and `P·q` are positive): `x = ξ β`
and `β ≤ 1` give `x = ξ β ≤ ξ`. -/
theorem x_le_xi_of_beta_le_one (i : Invariants) (h : i.beta ≤ 1) : i.x ≤ i.xi := by
  rw [x_eq_xi_mul_beta i]
  exact mul_le_of_le_one_right (div_nonneg i.Dq_pos.le i.Pq_pos.le) h

end Invariants

/-! ## Layer 0.2: the target-elastic boundary in `t` -/

/-- **Layer 0.2**: the kinematic boundary in `t` at fixed `ξ` in the target-elastic case
(`M_Y = M`), with `M` the target mass: `tMinElastic M ξ = -ξ²M²/(1-ξ)`.

The accessible momentum transfers of the target-elastic physical region are
`t ≤ tMinElastic M ξ`, equivalently `|t| ≥ ξ²M²/(1-ξ)` (with `t ≤ 0` throughout, per
Convention 2); the boundary value is attained in the forward configuration, which is the point
of minimum `|t|`.

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

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
