/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
public import EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic
/-!

# Diffractive DIS Kinematics

This module introduces the kinematics of diffractive DIS: the invariant scalar products of a
diffractive event, from which the momentum fractions `x`, `ξ` and `β` are derived, and the
target-elastic boundary of the physical region in `t`.

The kinematics are carried by the invariant scalar products rather than by the momentum
fractions, so that the fundamental relation `x = ξ β` is a theorem about the definitions and not
a definition that assumes itself. An event described by the exclusive kinematics of
`EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic` enters through the bridge
`Invariants.ofExcl`, on which the diffractive Bjorken variable `Invariants.x` agrees with the
inclusive `DisKinematics.xBj` of the same momenta (`Invariants.ofExcl_x`).

## References

* R. Abdul Khalek et al., *Science Requirements and Detector Concepts for the Electron-Ion
  Collider: EIC Yellow Report*, Nucl. Phys. A **1026** (2022) 122447, §7.1.6 "Inclusive and hard
  diffraction", for the diffractive variables and their physical region.
* G. Wolf, *Review of high energy diffraction in real and virtual photon proton scattering at
  HERA*, Rept. Prog. Phys. **73** (2010) 116202, §2, for the `ξ`–`β` kinematics and the
  target-elastic boundary in `t`.
* V. Barone and E. Predazzi, *High-Energy Particle Diffraction*, Springer, 2002, ch. 1–2, for
  the kinematics of the diffractive final state.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)
open EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics (ExclKinematics)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-! ## The diffractive invariants -/

/-- The invariants of a diffractive event, with `Pq = P · q`, `Dq = Δ · q` for `Δ = P - P'`,
`Q2 = -q²` and `t = Δ²`. Carrying the scalar products rather than the momentum fractions is what
makes `x = ξ β` provable rather than true by definition: the momentum fractions are derived from
these fields, so the identity between them is a theorem, not a stipulation.

Only the sign conditions of the physical region are imposed as fields; the remaining
physical-region conditions `ξ ≤ 1` and `β ≤ 1` are not, so an inhabitant need not lie in the
physical region, which is why `x_le_xi_of_beta_le_one` takes `β ≤ 1` as a hypothesis. -/
@[ext]
structure Invariants where
  /-- `P · q`, positive in the physical region. -/
  Pq : ℝ
  /-- `Δ · q` with `Δ = P - P'`, positive in the physical region. -/
  Dq : ℝ
  /-- Photon virtuality `Q² = -q²`. -/
  Q2 : ℝ
  /-- Invariant momentum transfer `t = Δ²` to the target; non-positive throughout, so
  `|t| = -t`. -/
  t : ℝ
  /-- Positivity of `P · q` in the physical region. -/
  Pq_pos : 0 < Pq
  /-- Positivity of `Δ · q` in the physical region. -/
  Dq_pos : 0 < Dq
  /-- Positivity of the photon virtuality. -/
  Q2_pos : 0 < Q2
  /-- Non-positivity of the momentum transfer. -/
  t_nonpos : t ≤ 0

namespace Invariants

/-- The inclusive Bjorken variable, `x = Q² / (2 P·q)`. -/
def x (i : Invariants) : ℝ := i.Q2 / (2 * i.Pq)

/-- Defining expression for `Invariants.x`. -/
theorem x_def (i : Invariants) : i.x = i.Q2 / (2 * i.Pq) := (rfl)

/-- The momentum fraction lost by the target, `ξ = Δ·q / P·q`. -/
def xi (i : Invariants) : ℝ := i.Dq / i.Pq

/-- Defining expression for `Invariants.xi`. -/
theorem xi_def (i : Invariants) : i.xi = i.Dq / i.Pq := (rfl)

/-- The parton's fraction of the exchanged momentum, `β = Q² / (2 Δ·q)`. -/
def beta (i : Invariants) : ℝ := i.Q2 / (2 * i.Dq)

/-- Defining expression for `Invariants.beta`. -/
theorem beta_def (i : Invariants) : i.beta = i.Q2 / (2 * i.Dq) := (rfl)

/-- The positive magnitude `|t| = -t` of the momentum transfer, per Convention 2 of the Diffraction
roadmap: every exponential or power law in the momentum transfer is written in terms of `absT`,
never with the sign of `t` carried through by hand. -/
def absT (i : Invariants) : ℝ := -i.t

/-- Defining expression for `Invariants.absT`. -/
theorem absT_eq_neg_t (i : Invariants) : i.absT = -i.t := (rfl)

/-- The magnitude of the momentum transfer is non-negative. -/
theorem absT_nonneg (i : Invariants) : 0 ≤ i.absT := neg_nonneg.mpr i.t_nonpos

/-- The Bjorken variable is positive in the physical region. -/
theorem x_pos (i : Invariants) : 0 < i.x :=
  div_pos i.Q2_pos (mul_pos two_pos i.Pq_pos)

/-- The momentum fraction lost by the target is positive in the physical region. -/
theorem xi_pos (i : Invariants) : 0 < i.xi := div_pos i.Dq_pos i.Pq_pos

/-- The parton's fraction of the exchanged momentum is positive in the physical region. -/
theorem beta_pos (i : Invariants) : 0 < i.beta :=
  div_pos i.Q2_pos (mul_pos two_pos i.Dq_pos)

/-- The momentum fraction lost by the target is non-negative in the physical region. -/
theorem xi_nonneg (i : Invariants) : 0 ≤ i.xi := (xi_pos i).le

/-- The fundamental relation `x = ξ β`: the inclusive Bjorken variable factors as the momentum
fraction lost by the target times the parton's fraction of the exchanged momentum, which is the
identity that licenses calling `β` a momentum fraction of the exchange. Exact, with no mass or
high-energy approximation. -/
theorem x_eq_xi_mul_beta (i : Invariants) : i.x = i.xi * i.beta := by
  have hPq : i.Pq ≠ 0 := ne_of_gt i.Pq_pos
  have hDq : i.Dq ≠ 0 := ne_of_gt i.Dq_pos
  rw [x_def, xi_def, beta_def]
  field_simp

/-- The diffractive kinematic bound `x ≤ ξ` when `β ≤ 1`: the kinematic ordering of the inclusive
and diffractive momentum fractions, used to bound the diffractive region. -/
theorem x_le_xi_of_beta_le_one (i : Invariants) (h : i.beta ≤ 1) : i.x ≤ i.xi := by
  rw [x_eq_xi_mul_beta i]
  exact mul_le_of_le_one_right i.xi_nonneg h

/-- The diffractive invariants of an event described by `ExclKinematics`: `Pq = P · q` from the
incoming target momentum, `Dq = Δ · q` with `Δ = P - P'` the negative of the exclusive
`ExclKinematics.delta = P' - P`, `Q2` the photon virtuality `Q² = -q²`, and `t = Δ²`. The
positivity and sign hypotheses are the necessary sign conditions of the physical region under
which the momentum fractions of `Invariants` are meaningful; see `Invariants` for the conditions
of the physical region that are not imposed. -/
def ofExcl (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) : Invariants where
  Pq := g K.p K.q
  Dq := -g K.delta K.q
  Q2 := K.Q2 g
  t := K.tMom g
  Pq_pos := hPq
  Dq_pos := hDq
  Q2_pos := hQ2
  t_nonpos := ht

/-- The `P · q` of an exclusive event is the scalar product of the incoming target momentum with
the photon momentum. -/
@[simp]
theorem ofExcl_Pq (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExcl g K hPq hDq hQ2 ht).Pq = g K.p K.q := (rfl)

/-- The `Δ · q` of an exclusive event, with `Δ = P - P'` the negative of
`ExclKinematics.delta = P' - P`. -/
@[simp]
theorem ofExcl_Dq (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExcl g K hPq hDq hQ2 ht).Dq = -g K.delta K.q := (rfl)

/-- The photon virtuality of an exclusive event is `ExclKinematics.Q2`. -/
@[simp]
theorem ofExcl_Q2 (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExcl g K hPq hDq hQ2 ht).Q2 = K.Q2 g := (rfl)

/-- The momentum transfer of an exclusive event is `ExclKinematics.tMom`: `t = Δ²` is insensitive
to the sign of `Δ`. -/
@[simp]
theorem ofExcl_t (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExcl g K hPq hDq hQ2 ht).t = K.tMom g := (rfl)

/-- The diffractive Bjorken variable of an exclusive event is the inclusive Bjorken variable of
the same momenta: `Invariants.x` agrees with `DisKinematics.xBj` on the inclusive record built
from `K.p`, `K.pPrime`, `K.k`, `K.kPrime`, `K.q` and `K.hqLepton`. -/
theorem ofExcl_x (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExcl g K hPq hDq hQ2 ht).x =
      DisKinematics.xBj g
        { p := K.p
          pPrime := K.pPrime
          k := K.k
          kPrime := K.kPrime
          q := K.q
          hq := K.hqLepton } := by
  simp [x_def, ofExcl, DisKinematics.xBj, DisKinematics.Q2, ExclKinematics.Q2]

end Invariants

/-! ## The target-elastic boundary in `t` -/

/-- The kinematic boundary in `t` at fixed `ξ` in the target-elastic case (`M_Y = M`), with `M`
the target mass: `tMinElastic M ξ = -ξ²M²/(1-ξ)`.

The argument `xi` is the momentum fraction lost by the target, the `ξ = Δ·q / P·q` of
`Invariants.xi`; it is not the skewness `ExclKinematics.xiSkew` (Belitsky-Müller-Kirchner's `η`),
a different variable that also carries a `ξ` in the exclusive kinematics and for which the
target-elastic boundary is a different function.

The accessible momentum transfers of the target-elastic physical region are
`t ≤ tMinElastic M ξ`, equivalently `|t| ≥ ξ²M²/(1-ξ)` (with `t ≤ 0` throughout); the boundary
value is attained in the forward configuration, which is the point of minimum `|t|`.

The boundary is obtained from the two-body threshold condition at fixed `(ξ, M, M_Y)`, and in
the target-elastic case `M_Y = M` it reduces to `ξ²M²/(1-ξ)`; see Wolf, *Rept. Prog. Phys.*
**73** (2010) 116202, §2.

See `tMinElastic_def` for the defining expression and `tMinElastic_nonpos` for the sign
property. -/
def tMinElastic (M xi : ℝ) : ℝ := -(xi ^ 2 * M ^ 2) / (1 - xi)

/-- Defining expression for `tMinElastic`. -/
theorem tMinElastic_def (M xi : ℝ) : tMinElastic M xi = -(xi ^ 2 * M ^ 2) / (1 - xi) := (rfl)

/-- At vanishing momentum loss `ξ = 0` the target-elastic boundary degenerates to `t = 0`. -/
@[simp]
theorem tMinElastic_xi_zero (M : ℝ) : tMinElastic M 0 = 0 := by
  rw [tMinElastic_def]
  norm_num

/-- The target-elastic boundary lies on the non-positive side of zero whenever `xi < 1`, in
particular throughout the physical range `ξ ∈ [0, 1)`: the boundary of the physical region is on
the same side of zero as the region it bounds. -/
theorem tMinElastic_nonpos (M xi : ℝ) (h : xi < 1) : tMinElastic M xi ≤ 0 := by
  rw [tMinElastic_def, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (sq_nonneg xi) (sq_nonneg M)) (sub_nonneg.mpr h.le)

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
