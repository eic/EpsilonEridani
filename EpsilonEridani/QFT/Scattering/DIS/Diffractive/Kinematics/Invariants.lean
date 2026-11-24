/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic
public import EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic
/-!

# The invariants of diffractive DIS

This module introduces the invariant scalar products of a diffractive event, from which the
momentum fractions `x`, `ξ` and `β` are derived. The invariant fraction `ξ = Δ·q / P·q` of
`Invariants.xi` is not the light-cone momentum fraction lost by the target that parametrizes the
boundaries `tMin` and `tMinElastic` in `t` (in `Diffractive.Kinematics.Boundary`): the two agree
only in the Bjorken limit.

The kinematics are carried by the invariant scalar products rather than by the momentum
fractions, so that the fundamental relation `x = ξ β` is a theorem about the definitions and not
a definition that assumes itself. An event described by the exclusive kinematics of
`EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic` enters through the bridge
`Invariants.ofExclKinematics`, on which the diffractive Bjorken variable `Invariants.x` agrees
with the inclusive `DisKinematics.xBj` of the same momenta (`Invariants.ofExclKinematics_x`).

## References

* R. Abdul Khalek et al., *Science Requirements and Detector Concepts for the Electron-Ion
  Collider: EIC Yellow Report*, Nucl. Phys. A **1026** (2022) 122447, §7.1.6 "Inclusive and hard
  diffraction", for the diffractive variables and their physical region.
* G. Wolf, *Review of high energy diffraction in real and virtual photon proton scattering at
  HERA*, Rept. Prog. Phys. **73** (2010) 116202, §2, for the `ξ`–`β` kinematics.
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

Only the sign conditions of the physical region are imposed as fields; the other
physical-region conditions, among them `ξ ≤ 1`, `β ≤ 1` and the boundary condition in `t`, are
not, so an inhabitant need not lie in the physical region, which is why
`x_le_xi_of_beta_le_one` takes `β ≤ 1` as a hypothesis. -/
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

/-- The momentum fraction lost by the target, `ξ = Δ·q / P·q`. This is the invariant fraction;
it is not the light-cone fraction `xiLC` taken by `tMinElastic`, a different variable that agrees
with it only in the Bjorken limit. -/
def xi (i : Invariants) : ℝ := i.Dq / i.Pq

/-- Defining expression for `Invariants.xi`. -/
theorem xi_def (i : Invariants) : i.xi = i.Dq / i.Pq := (rfl)

/-- The parton's fraction of the exchanged momentum, `β = Q² / (2 Δ·q)`. -/
def beta (i : Invariants) : ℝ := i.Q2 / (2 * i.Dq)

/-- Defining expression for `Invariants.beta`. -/
theorem beta_def (i : Invariants) : i.beta = i.Q2 / (2 * i.Dq) := (rfl)

/-- The non-negative magnitude `|t| = -t` of the momentum transfer (`absT_nonneg`, from
`t_nonpos`). -/
def absT (i : Invariants) : ℝ := -i.t

/-- Defining expression for `Invariants.absT`. -/
theorem absT_def (i : Invariants) : i.absT = -i.t := (rfl)

/-- The magnitude of the momentum transfer is non-negative. -/
theorem absT_nonneg (i : Invariants) : 0 ≤ i.absT := neg_nonneg.mpr i.t_nonpos

/-- The magnitude `absT` of the momentum transfer is its absolute value `|t|`. -/
theorem absT_eq_abs_t (i : Invariants) : i.absT = |i.t| := (abs_of_nonpos i.t_nonpos).symm

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
def ofExclKinematics (g : Bilin V) (K : ExclKinematics V)
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
theorem ofExclKinematics_Pq (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).Pq = g K.p K.q := (rfl)

/-- The `Δ · q` of an exclusive event, with `Δ = P - P'` the negative of
`ExclKinematics.delta = P' - P`. -/
@[simp]
theorem ofExclKinematics_Dq (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).Dq = -g K.delta K.q := (rfl)

/-- The photon virtuality of an exclusive event is `ExclKinematics.Q2`. -/
@[simp]
theorem ofExclKinematics_Q2 (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).Q2 = K.Q2 g := (rfl)

/-- The momentum transfer of an exclusive event is `ExclKinematics.tMom`: `t = Δ²` is insensitive
to the sign of `Δ`. -/
@[simp]
theorem ofExclKinematics_t (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).t = K.tMom g := (rfl)

/-- The diffractive Bjorken variable of an exclusive event is the inclusive Bjorken variable of
the same momenta: `Invariants.x` agrees with `DisKinematics.xBj` on
`ExclKinematics.toDisKinematics`. -/
@[simp]
theorem ofExclKinematics_x (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).x = K.toDisKinematics.xBj g := by
  simp [x_def, DisKinematics.xBj]

/-- The momentum fraction lost by the target in an exclusive event, `ξ = Δ·q / P·q` with
`Δ = P - P'` the negative of `ExclKinematics.delta = P' - P`. -/
@[simp]
theorem ofExclKinematics_xi (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).xi = -g K.delta K.q / g K.p K.q := by
  rw [xi_def, ofExclKinematics_Dq, ofExclKinematics_Pq]

/-- The parton's fraction of the exchanged momentum in an exclusive event,
`β = Q² / (2 Δ·q)` with `Δ = P - P'`. -/
@[simp]
theorem ofExclKinematics_beta (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).beta = K.Q2 g / (2 * -g K.delta K.q) := by
  rw [beta_def, ofExclKinematics_Q2, ofExclKinematics_Dq]

/-- The magnitude of the momentum transfer of an exclusive event is `-ExclKinematics.tMom`. -/
@[simp]
theorem ofExclKinematics_absT (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExclKinematics g K hPq hDq hQ2 ht).absT = -K.tMom g := by
  rw [absT_def, ofExclKinematics_t]

end Invariants

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
