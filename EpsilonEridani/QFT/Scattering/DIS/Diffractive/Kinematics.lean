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

/-- The momentum fraction lost by the target, `ξ = Δ·q / P·q`. -/
def xi (i : Invariants) : ℝ := i.Dq / i.Pq

/-- Defining expression for `Invariants.xi`. -/
theorem xi_def (i : Invariants) : i.xi = i.Dq / i.Pq := (rfl)

/-- The parton's fraction of the exchanged momentum, `β = Q² / (2 Δ·q)`. -/
def beta (i : Invariants) : ℝ := i.Q2 / (2 * i.Dq)

/-- Defining expression for `Invariants.beta`. -/
theorem beta_def (i : Invariants) : i.beta = i.Q2 / (2 * i.Dq) := (rfl)

/-- The positive magnitude `|t| = -t` of the momentum transfer, non-negative by `t_nonpos`
(`absT_nonneg`). -/
def absT (i : Invariants) : ℝ := -i.t

/-- Defining expression for `Invariants.absT`. -/
theorem absT_eq_neg_t (i : Invariants) : i.absT = -i.t := (rfl)

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
the same momenta: `Invariants.x` agrees with `DisKinematics.xBj` on
`ExclKinematics.toDisKinematics`. -/
@[simp]
theorem ofExcl_x (g : Bilin V) (K : ExclKinematics V)
    (hPq : 0 < g K.p K.q) (hDq : 0 < -g K.delta K.q)
    (hQ2 : 0 < K.Q2 g) (ht : K.tMom g ≤ 0) :
    (ofExcl g K hPq hDq hQ2 ht).x = K.toDisKinematics.xBj g := by
  rw [x_def, ofExcl_Q2, ofExcl_Pq, DisKinematics.xBj, ExclKinematics.Q2_toDisKinematics,
    ExclKinematics.toDisKinematics_p, ExclKinematics.toDisKinematics_q]

end Invariants

/-! ## The target-elastic boundary in `t` -/

/-- The kinematic boundary in `t` at fixed light-cone momentum fraction in the target-elastic
case (`M_Y = M`), with `M` the target mass: `tMinElastic M ξ = -ξ²M²/(1-ξ)`.

The argument `xiLC` is the light-cone momentum fraction `ξ = Δ⁺/P⁺` lost by the target, named
apart from the invariant `Invariants.xi = Δ·q / P·q`, with which it agrees only up to relative
corrections of order `Q²M²/(P·q)²`, so exactly only in the Bjorken limit; at finite energy the
target-elastic boundary is not exactly `tMinElastic M (Invariants.xi i)`. Nor is `xiLC` the
skewness `ExclKinematics.xiSkew` (Belitsky-Müller-Kirchner's `η`), a different variable that also
carries a `ξ` in the exclusive kinematics and for which the target-elastic boundary is a different
function.

For a light-cone fraction `ξ < 1`, the accessible momentum transfers of the target-elastic physical
region are `t ≤ tMinElastic M ξ`, equivalently `|t| ≥ ξ²M²/(1-ξ)` (`le_tMinElastic_iff`, with
`t ≤ 0` throughout); the boundary value is attained in the forward configuration, which is the
point of minimum `|t|`. At the pole `ξ = 1` the true boundary diverges, whereas, like any real
division in Lean, `tMinElastic M 1` is `0`; the characterisation is therefore stated only for
`ξ < 1`.

The boundary is obtained from the two-body threshold condition at fixed `(ξ, M, M_Y)`, and in
the target-elastic case `M_Y = M` it reduces to `ξ²M²/(1-ξ)`; see Wolf, *Rept. Prog. Phys.*
**73** (2010) 116202, §2.

See `tMinElastic_def` for the defining expression and `tMinElastic_nonpos` for the sign
property. -/
def tMinElastic (M xiLC : ℝ) : ℝ := -(xiLC ^ 2 * M ^ 2) / (1 - xiLC)

/-- Defining expression for `tMinElastic`. -/
theorem tMinElastic_def (M xiLC : ℝ) :
    tMinElastic M xiLC = -(xiLC ^ 2 * M ^ 2) / (1 - xiLC) := (rfl)

/-- The magnitude of the target-elastic boundary, `-tMinElastic M ξ = ξ²M²/(1-ξ)`. -/
theorem neg_tMinElastic (M xiLC : ℝ) : -tMinElastic M xiLC = xiLC ^ 2 * M ^ 2 / (1 - xiLC) := by
  rw [tMinElastic_def, neg_div, neg_neg]

/-- The boundary condition `t ≤ tMinElastic M ξ` for a real momentum transfer `t`, in terms of its
magnitude: `-t ≥ ξ²M²/(1-ξ)`. Here `M` and `xiLC` are arbitrary parameters, `xiLC` being the
light-cone fraction of `tMinElastic`, and the equivalence holds for any choice of them. -/
theorem le_tMinElastic_iff (M xiLC t : ℝ) :
    t ≤ tMinElastic M xiLC ↔ xiLC ^ 2 * M ^ 2 / (1 - xiLC) ≤ -t := by
  rw [← neg_tMinElastic, neg_le_neg_iff]

/-- The boundary condition `t ≤ tMinElastic M ξ` for the momentum transfer of `i`, in terms of
`Invariants.absT`: `|t| ≥ ξ²M²/(1-ξ)`. Here `M` and `xiLC` are arbitrary parameters unrelated to
`i`; in particular `xiLC` is the light-cone fraction of `tMinElastic`, not `i.xi`. -/
theorem Invariants.t_le_tMinElastic_iff (i : Invariants) (M xiLC : ℝ) :
    i.t ≤ tMinElastic M xiLC ↔ xiLC ^ 2 * M ^ 2 / (1 - xiLC) ≤ i.absT := by
  rw [Invariants.absT_eq_neg_t]
  exact le_tMinElastic_iff M xiLC i.t

/-- At vanishing momentum loss `ξ = 0` the target-elastic boundary degenerates to `t = 0`. -/
@[simp]
theorem tMinElastic_xiLC_zero (M : ℝ) : tMinElastic M 0 = 0 := by
  rw [tMinElastic_def]
  norm_num

/-- The target-elastic boundary lies on the non-positive side of zero whenever `xiLC < 1`, in
particular throughout the physical range `ξ ∈ [0, 1)`: the boundary of the physical region is on
the same side of zero as the region it bounds. -/
theorem tMinElastic_nonpos (M xiLC : ℝ) (h : xiLC < 1) : tMinElastic M xiLC ≤ 0 := by
  rw [tMinElastic_def, neg_div, neg_nonpos]
  exact div_nonneg (mul_nonneg (sq_nonneg xiLC) (sq_nonneg M)) (sub_nonneg.mpr h.le)

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
