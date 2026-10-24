/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.AccessMethods

/-!
# Radiative events and the shift of the reconstructed invariants

When the lepton of `e(k) + N(p) → e(k') + X` radiates a real photon `ℓ`, the invariants of the
hard scattering differ from the invariants an experiment computes from the measured momenta, and
the difference depends on which momenta are used. This module makes that statement precise for
the covariant reconstruction methods of `Kinematics.AccessMethods`.

The invariants of the hard scattering and the invariants computed from a measurement are carried
by two distinct types, `TrueInvariants` and `ReconstructedInvariants`, so that one cannot be used
for the other by accident; the only passage between them is the explicit
`TrueInvariants.toReconstructedInvariants`, and their difference is the shift
`ReconstructedInvariants.shiftXQ2` (or `ReconstructedInvariants.shiftXY`).

## Main definitions

* `RadiativeEvent`: the momenta `k, p, k', ℓ, p_X` of a radiative event, with momentum
  conservation `k + p = k' + ℓ + p_X`.
* `EmissionLine`: whether the photon was radiated by the incoming or by the outgoing lepton. This
  is a label on the amplitude, not a property of the photon momentum, so it is data supplied
  alongside the event.
* `RadiativeEvent.hardKinematics`, `RadiativeEvent.trueInvariants`: the kinematics of the hard
  scattering, whose lepton enters with `k - ℓ` after initial-state emission and leaves with
  `k' + ℓ` after final-state emission, and its invariants.
* `ReconstructedInvariants.shiftXQ2`, `ReconstructedInvariants.shiftXY`: the shift of
  reconstructed from true invariants, componentwise in `(x, Q²)` or in `(x, y)`.

## Main statements

* `RadiativeEvent.electronMethod_eq_trueInvariants_of_photon_eq_zero` and its analogues: without
  a photon, every method returns the true invariants.
* `RadiativeEvent.shiftXQ2_hadronicMethod_eq_zero`: the hadronic method recovers `x` and `Q²`
  whichever line radiates, and `RadiativeEvent.hadronicMethod_eq_trueInvariants_finalState` it is
  exact for final-state radiation, while after collinear final-state emission the electron method
  rescales the virtuality by the fraction `z` of the hard outgoing lepton momentum retained by the
  measured `k'`, `Q²_e = z Q²` for a massless incoming lepton
  (`RadiativeEvent.electronMethod_Q2_of_collinear_finalState`).
* `RadiativeEvent.sigmaMethod_y_eq_trueInvariants_y_initialState`: the Sigma method recovers the
  true inelasticity after any initial-state emission, and
  `RadiativeEvent.shiftXY_sigmaMethod_eq_zero_of_collinear_initialState` it is exact in `(x, y)`
  after an exactly collinear one.
* `RadiativeEvent.electronMethod_x_of_collinear_initialState`,
  `RadiativeEvent.electronMethod_x_ne_trueInvariants_x_of_collinear_initialState`: after collinear
  initial-state emission of energy fraction `1 - z` the electron method returns
  `x_e = x y / (1 - z (1 - y))` in terms of the true `x` and `y`, which differs from a nonzero `x`
  for `z < 1` and `0 < y < 1`, and `Q² = z Q²_e` for massless leptons
  (`RadiativeEvent.trueInvariants_Q2_of_collinear_initialState`).

The scalar products are those of an arbitrary bilinear form `g` on the momentum space, as for
`DisKinematics`. An on-shell photon exactly collinear with a lepton forces that lepton to be
massless, `k² = 0` for initial-state and `k'² = 0` for final-state emission, and the collinear
statements take that condition as a hypothesis. The mass of the other lepton is assumed to vanish
only where exactness needs it, for the Bjorken variable after initial-state emission; elsewhere it
appears as an explicit remainder.

## References

* F. Jacquet and A. Blondel, in *Proceedings of the Study of an ep Facility for Europe*,
  ed. U. Amaldi, DESY 79/48 (1979) 391, for the hadronic method.
* S. Bentvelsen, J. Engelen and P. Kooijman, *Reconstruction of (x, Q²) and extraction of
  structure functions in neutral current scattering at HERA*, Proceedings of the Workshop
  Physics at HERA, vol. 1 (1992) 23.
* U. Bassler and G. Bernardi, *On the kinematic reconstruction of deep inelastic scattering at
  HERA: the Σ method*, Nucl. Instrum. Meth. A **361** (1995) 197, arXiv:hep-ex/9412004.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- The invariants of the hard lepton–hadron scattering of an event: the Bjorken variable `x`,
the photon virtuality `Q² = -q²` and the inelasticity `y`. -/
@[ext] structure TrueInvariants where
  /-- The Bjorken variable `x = Q² / (2 p·q)`, with `q` the momentum transferred to the
  hadrons. -/
  x : ℝ
  /-- The photon virtuality `Q² = -q²`. -/
  Q2 : ℝ
  /-- The inelasticity `y = (p·q) / (p·k_hard)`, where `k_hard` is the lepton momentum entering
  the hard scattering (`k - ℓ` after initial-state emission). -/
  y : ℝ

/-- The reconstruction returned by an exact measurement of the true invariants `t`. -/
@[simps]
def TrueInvariants.toReconstructedInvariants (t : TrueInvariants) : ReconstructedInvariants where
  x := t.x
  Q2 := t.Q2
  y := t.y

namespace ReconstructedInvariants

/-- The shift `r - t` of the reconstructed invariants `r` from the true invariants `t`,
componentwise in `(x, Q²)`. -/
def shiftXQ2 (r : ReconstructedInvariants) (t : TrueInvariants) : ℝ × ℝ :=
  (r.x - t.x, r.Q2 - t.Q2)

/-- The shift `r - t` of the reconstructed invariants `r` from the true invariants `t`,
componentwise in `(x, y)`. -/
def shiftXY (r : ReconstructedInvariants) (t : TrueInvariants) : ℝ × ℝ :=
  (r.x - t.x, r.y - t.y)

/-- The `(x, Q²)` shift vanishes exactly when `x` and `Q²` are reconstructed exactly. -/
theorem shiftXQ2_eq_zero_iff {r : ReconstructedInvariants} {t : TrueInvariants} :
    r.shiftXQ2 t = 0 ↔ r.x = t.x ∧ r.Q2 = t.Q2 := by
  simp [shiftXQ2, Prod.ext_iff, sub_eq_zero]

/-- The `(x, y)` shift vanishes exactly when `x` and `y` are reconstructed exactly. -/
theorem shiftXY_eq_zero_iff {r : ReconstructedInvariants} {t : TrueInvariants} :
    r.shiftXY t = 0 ↔ r.x = t.x ∧ r.y = t.y := by
  simp [shiftXY, Prod.ext_iff, sub_eq_zero]

end ReconstructedInvariants

/-- The lepton line from which the photon of a radiative event is emitted. -/
inductive EmissionLine
  /-- Initial-state radiation, from the incoming lepton. -/
  | initialState
  /-- Final-state radiation, from the outgoing lepton. -/
  | finalState
  deriving DecidableEq

/-- A radiative event `e(k) + N(p) → e(k') + γ(ℓ) + X(p_X)`: the incoming lepton and target, the
scattered lepton, the radiated photon and the hadronic final state, subject to momentum
conservation. -/
@[ext] structure RadiativeEvent (V : Type) [AddCommGroup V] where
  /-- The incoming lepton momentum `k`. -/
  k : V
  /-- The target momentum `p`. -/
  p : V
  /-- The scattered lepton momentum `k'`. -/
  kPrime : V
  /-- The radiated photon momentum `ℓ`. -/
  photon : V
  /-- The momentum `p_X` of the hadronic final state. -/
  pX : V
  /-- Momentum conservation `k + p = k' + ℓ + p_X`. -/
  conservation : k + p = kPrime + photon + pX

/-- The expansion of `-(z u - v)²` about `-(u - v)²`, which holds without any mass-shell
condition on `u` or `v`. -/
private theorem neg_apply_smul_sub (g : Bilin V) (u v : V) (z : ℝ) :
    -g (z • u - v) (z • u - v) =
      z * -g (u - v) (u - v) + (1 - z) * (z * g u u - g v v) := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

namespace RadiativeEvent

variable (e : RadiativeEvent V)

/-! ### The hard scattering and the true invariants -/

/-- The lepton momentum entering the hard scattering: `k - ℓ` after initial-state emission and
`k` after final-state emission. -/
def leptonIn : EmissionLine → V
  | .initialState => e.k - e.photon
  | .finalState => e.k

/-- The lepton momentum leaving the hard scattering: `k'` after initial-state emission and
`k' + ℓ` after final-state emission. -/
def leptonOut : EmissionLine → V
  | .initialState => e.kPrime
  | .finalState => e.kPrime + e.photon

omit [Module ℝ V] in
@[simp] theorem leptonIn_initialState : e.leptonIn .initialState = e.k - e.photon := (rfl)

omit [Module ℝ V] in
@[simp] theorem leptonIn_finalState : e.leptonIn .finalState = e.k := (rfl)

omit [Module ℝ V] in
@[simp] theorem leptonOut_initialState : e.leptonOut .initialState = e.kPrime := (rfl)

omit [Module ℝ V] in
@[simp] theorem leptonOut_finalState : e.leptonOut .finalState = e.kPrime + e.photon := (rfl)

omit [Module ℝ V] in
/-- The momentum transferred to the hadrons, `p_X - p`, is what the leptons lose besides the
photon. -/
theorem pX_sub_p : e.pX - e.p = e.k - e.kPrime - e.photon :=
  calc e.pX - e.p = e.kPrime + e.photon + e.pX - e.kPrime - e.photon - e.p := by abel
    _ = e.k + e.p - e.kPrime - e.photon - e.p := by rw [e.conservation]
    _ = e.k - e.kPrime - e.photon := by abel

omit [Module ℝ V] in
/-- Whichever line radiates, the hard lepton line transfers `p_X - p` to the hadrons. -/
theorem leptonIn_sub_leptonOut (l : EmissionLine) :
    e.leptonIn l - e.leptonOut l = e.pX - e.p := by
  rw [pX_sub_p]
  cases l <;> simp only [leptonIn, leptonOut] <;> abel

/-- The kinematics of the hard scattering of a radiative event: the target, the hard lepton line
of `leptonIn` and `leptonOut`, the hadronic final state, and the momentum transfer `p_X - p`. -/
@[simps]
def hardKinematics (l : EmissionLine) : DisKinematics V where
  p := e.p
  pPrime := e.pX
  k := e.leptonIn l
  kPrime := e.leptonOut l
  q := e.pX - e.p
  hq := (e.leptonIn_sub_leptonOut l).symm

/-- The true invariants of a radiative event whose photon was radiated by the line `l`: the
invariants of its hard scattering. -/
@[simps]
def trueInvariants (g : Bilin V) (l : EmissionLine) : TrueInvariants where
  x := (e.hardKinematics l).xBj g
  Q2 := (e.hardKinematics l).Q2 g
  y := (e.hardKinematics l).yInel g

/-- The true virtuality is `-(p_X - p)²`. -/
theorem trueInvariants_Q2_eq (g : Bilin V) (l : EmissionLine) :
    (e.trueInvariants g l).Q2 = -g (e.pX - e.p) (e.pX - e.p) :=
  rfl

/-- The true Bjorken variable is `Q² / (2 p·(p_X - p))`. -/
theorem trueInvariants_x_eq (g : Bilin V) (l : EmissionLine) :
    (e.trueInvariants g l).x = (e.trueInvariants g l).Q2 / (2 * g e.p (e.pX - e.p)) :=
  rfl

/-- The true inelasticity is `p·(p_X - p) / p·k_hard`, with `k_hard` the lepton momentum
entering the hard scattering. -/
theorem trueInvariants_y_eq (g : Bilin V) (l : EmissionLine) :
    (e.trueInvariants g l).y = g e.p (e.pX - e.p) / g e.p (e.leptonIn l) :=
  rfl

/-! ### The hadronic method -/

section Hadronic

variable (g : Bilin V)

/-- The hadronic method reconstructs the true virtuality whichever line radiates. -/
theorem hadronicMethod_Q2_eq_trueInvariants_Q2 (l : EmissionLine) :
    (hadronicMethod g e.k e.p e.pX).Q2 = (e.trueInvariants g l).Q2 :=
  rfl

/-- The hadronic method reconstructs the true Bjorken variable whichever line radiates. -/
theorem hadronicMethod_x_eq_trueInvariants_x (l : EmissionLine) :
    (hadronicMethod g e.k e.p e.pX).x = (e.trueInvariants g l).x :=
  rfl

/-- The `(x, Q²)` shift of the hadronic method vanishes whichever line radiates. -/
theorem shiftXQ2_hadronicMethod_eq_zero (l : EmissionLine) :
    (hadronicMethod g e.k e.p e.pX).shiftXQ2 (e.trueInvariants g l) = 0 :=
  ReconstructedInvariants.shiftXQ2_eq_zero_iff.2
    ⟨e.hadronicMethod_x_eq_trueInvariants_x g l, e.hadronicMethod_Q2_eq_trueInvariants_Q2 g l⟩

/-- The hadronic method is exact for final-state radiation. -/
theorem hadronicMethod_eq_trueInvariants_finalState :
    hadronicMethod g e.k e.p e.pX =
      (e.trueInvariants g .finalState).toReconstructedInvariants := by
  ext
  · exact e.hadronicMethod_x_eq_trueInvariants_x g .finalState
  · exact e.hadronicMethod_Q2_eq_trueInvariants_Q2 g .finalState
  · rfl

end Hadronic

/-! ### The Sigma inelasticity -/

section SigmaInelasticity

variable {e} (g : Bilin V)

omit [Module ℝ V] in
/-- Initial-state emission leaves the hard lepton line with the momentum `k - ℓ` that the target
and the measured final state `p_X`, `k'` balance. -/
theorem p_add_leptonIn_initialState : e.p + e.leptonIn .initialState = e.pX + e.kPrime := by
  rw [leptonIn_initialState, ← add_sub_assoc, add_comm e.p, e.conservation]
  abel

/-- The Sigma method recovers the true inelasticity after any initial-state emission: the
denominator `p·(p_X - p) + p·k'` of `y_Σ` is `p·(k - ℓ)`, the projection of the lepton momentum
that enters the hard scattering. -/
theorem sigmaMethod_y_eq_trueInvariants_y_initialState :
    (sigmaMethod g e.k e.p e.kPrime e.pX).y = (e.trueInvariants g .initialState).y :=
  SigmaMethodData.ySigma_eq_yInel ⟨e.pX, e.kPrime, e.p⟩ g (e.hardKinematics .initialState) rfl
    rfl e.p_add_leptonIn_initialState

end SigmaInelasticity

/-! ### Without a photon, every method is exact -/

section BornLimit

variable {e} (g : Bilin V) (l : EmissionLine)

omit [Module ℝ V] in
/-- Without a photon, the hard scattering is entered by the beam lepton `k`. -/
theorem leptonIn_of_photon_eq_zero (h : e.photon = 0) : e.leptonIn l = e.k := by
  cases l <;> simp [h]

omit [Module ℝ V] in
/-- Without a photon, the hard scattering is left by the scattered lepton `k'`. -/
theorem leptonOut_of_photon_eq_zero (h : e.photon = 0) : e.leptonOut l = e.kPrime := by
  cases l <;> simp [h]

omit [Module ℝ V] in
/-- Without a photon, the hard scattering does not depend on the emission line. -/
theorem hardKinematics_eq_of_photon_eq_zero (h : e.photon = 0) :
    e.hardKinematics l = e.hardKinematics .finalState := by
  simp only [hardKinematics, leptonIn_of_photon_eq_zero l h, leptonOut_of_photon_eq_zero l h,
    leptonIn_of_photon_eq_zero .finalState h, leptonOut_of_photon_eq_zero .finalState h]

/-- Without a photon, the true invariants do not depend on the emission line. -/
theorem trueInvariants_eq_of_photon_eq_zero (h : e.photon = 0) :
    e.trueInvariants g l = e.trueInvariants g .finalState := by
  rw [trueInvariants, trueInvariants, hardKinematics_eq_of_photon_eq_zero l h]

/-- Without a photon, the electron method returns the true invariants. -/
theorem electronMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0) :
    electronMethod g e.k e.p e.kPrime = (e.trueInvariants g l).toReconstructedInvariants := by
  have hK := electronMethod_disKinematics g (e.hardKinematics l)
  rwa [hardKinematics_k, hardKinematics_p, hardKinematics_kPrime, leptonIn_of_photon_eq_zero l h,
    leptonOut_of_photon_eq_zero l h] at hK

/-- Without a photon, the hadronic method returns the true invariants. -/
theorem hadronicMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0) :
    hadronicMethod g e.k e.p e.pX = (e.trueInvariants g l).toReconstructedInvariants := by
  rw [trueInvariants_eq_of_photon_eq_zero g l h]
  exact e.hadronicMethod_eq_trueInvariants_finalState g

/-- Without a photon, the Sigma method returns the true invariants. -/
theorem sigmaMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0)
    (hpk : g e.p e.k ≠ 0) :
    sigmaMethod g e.k e.p e.kPrime e.pX = (e.trueInvariants g l).toReconstructedInvariants := by
  have hQ := congrArg ReconstructedInvariants.Q2
    (electronMethod_eq_trueInvariants_of_photon_eq_zero g l h)
  have hy : (sigmaMethod g e.k e.p e.kPrime e.pX).y = (e.trueInvariants g l).y := by
    rw [trueInvariants_eq_of_photon_eq_zero g l h,
      ← trueInvariants_eq_of_photon_eq_zero g .initialState h]
    exact sigmaMethod_y_eq_trueInvariants_y_initialState g
  ext
  · rw [sigmaMethod_x, ← sigmaMethod_y g e.k, hy, hQ, TrueInvariants.toReconstructedInvariants_Q2,
      TrueInvariants.toReconstructedInvariants_x, trueInvariants_x_eq, trueInvariants_y_eq,
      leptonIn_of_photon_eq_zero l h, mul_assoc, mul_div_cancel₀ _ hpk]
  · exact hQ
  · exact hy

/-- Without a photon, the mixed method returns the true invariants. -/
theorem mixedMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0) :
    mixedMethod g e.k e.p e.kPrime e.pX = (e.trueInvariants g l).toReconstructedInvariants := by
  have hQ := congrArg ReconstructedInvariants.Q2
    (electronMethod_eq_trueInvariants_of_photon_eq_zero g l h)
  have hy := congrArg ReconstructedInvariants.y
    (hadronicMethod_eq_trueInvariants_of_photon_eq_zero g l h)
  ext
  · rw [mixedMethod_x, hQ]
    rfl
  · exact hQ
  · exact hy

end BornLimit

/-! ### Initial-state radiation -/

section InitialState

variable {e} (g : Bilin V) {z : ℝ}

/-- After initial-state emission of the fraction `1 - z` of the incoming lepton momentum, the
hard lepton enters with `z k`. -/
theorem leptonIn_of_collinear_initialState (hcol : e.photon = (1 - z) • e.k) :
    e.leptonIn .initialState = z • e.k := by
  rw [leptonIn_initialState, hcol, sub_smul, one_smul, sub_sub_cancel]

/-- After initial-state emission of the fraction `1 - z` of the incoming lepton momentum, the
momentum transferred to the hadrons is `z k - k'`. -/
theorem pX_sub_p_of_collinear_initialState (hcol : e.photon = (1 - z) • e.k) :
    e.pX - e.p = z • e.k - e.kPrime := by
  rw [← e.leptonIn_sub_leptonOut .initialState, leptonIn_of_collinear_initialState hcol,
    leptonOut_initialState]

private theorem apply_pX_sub_p_of_collinear_initialState (hcol : e.photon = (1 - z) • e.k) :
    g e.p (e.pX - e.p) = z * g e.p e.k - g e.p e.kPrime := by
  rw [pX_sub_p_of_collinear_initialState hcol, map_sub, map_smul, smul_eq_mul]

private theorem trueInvariants_y_of_collinear_initialState (hcol : e.photon = (1 - z) • e.k) :
    (e.trueInvariants g .initialState).y =
      (z * g e.p e.k - g e.p e.kPrime) / (z * g e.p e.k) := by
  rw [trueInvariants_y_eq, apply_pX_sub_p_of_collinear_initialState g hcol,
    leptonIn_of_collinear_initialState hcol, map_smul, smul_eq_mul]

/-- After exactly collinear initial-state emission of the fraction `1 - z` of the momentum of a
massless incoming lepton, the true virtuality is `Q² = z Q²_e - (1 - z) k'²` in terms of the
electron-method one; for a massless scattered lepton, `Q² = z Q²_e`. -/
theorem trueInvariants_Q2_of_collinear_initialState (hk : g e.k e.k = 0)
    (hcol : e.photon = (1 - z) • e.k) :
    (e.trueInvariants g .initialState).Q2 =
      z * (electronMethod g e.k e.p e.kPrime).Q2 - (1 - z) * g e.kPrime e.kPrime := by
  rw [trueInvariants_Q2_eq, pX_sub_p_of_collinear_initialState hcol, neg_apply_smul_sub, hk,
    electronMethod_Q2]
  ring

/-- After exactly collinear initial-state emission, the electron method overestimates the
virtuality, `Q² < Q²_e`, for a scattered lepton of nonnegative mass squared. -/
theorem trueInvariants_Q2_lt_electronMethod_Q2_of_collinear_initialState (hk : g e.k e.k = 0)
    (hk' : 0 ≤ g e.kPrime e.kPrime) (hcol : e.photon = (1 - z) • e.k) (hz0 : 0 < z)
    (hz1 : z < 1) (hQ : 0 < (e.trueInvariants g .initialState).Q2) :
    (e.trueInvariants g .initialState).Q2 < (electronMethod g e.k e.p e.kPrime).Q2 := by
  have h := trueInvariants_Q2_of_collinear_initialState g hk hcol
  nlinarith

/-- After exactly collinear initial-state emission, the electron-method inelasticity satisfies
`1 - y_e = z (1 - y)` in terms of the true inelasticity `y`. -/
theorem one_sub_electronMethod_y_of_collinear_initialState (hcol : e.photon = (1 - z) • e.k)
    (hz : z ≠ 0) (hpk : g e.p e.k ≠ 0) :
    1 - (electronMethod g e.k e.p e.kPrime).y =
      z * (1 - (e.trueInvariants g .initialState).y) := by
  rw [trueInvariants_y_of_collinear_initialState g hcol, electronMethod_y, map_sub]
  field_simp
  ring

/-- After exactly collinear initial-state emission, the electron method returns the Bjorken
variable `x_e = x y / (1 - z (1 - y))` in terms of the true `x` and `y`. -/
theorem electronMethod_x_of_collinear_initialState (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) (hpk : g e.p e.k ≠ 0)
    (hy : (e.trueInvariants g .initialState).y ≠ 0) :
    (electronMethod g e.k e.p e.kPrime).x =
      (e.trueInvariants g .initialState).x * (e.trueInvariants g .initialState).y /
        (1 - z * (1 - (e.trueInvariants g .initialState).y)) := by
  rw [trueInvariants_y_of_collinear_initialState g hcol] at hy
  have hz : z ≠ 0 := by
    rintro rfl
    exact hy (by rw [zero_mul, div_zero])
  -- `p·(z k - k') ≠ 0`, in the orientation `field_simp` normalises products to.
  have hzk : g e.p e.k * z - g e.p e.kPrime ≠ 0 := by
    rw [mul_comm]
    exact (div_ne_zero_iff.mp hy).1
  rw [← one_sub_electronMethod_y_of_collinear_initialState g hcol hz hpk, sub_sub_cancel,
    trueInvariants_x_eq, trueInvariants_Q2_of_collinear_initialState g hk hcol, hk',
    apply_pX_sub_p_of_collinear_initialState g hcol,
    trueInvariants_y_of_collinear_initialState g hcol, electronMethod_x, electronMethod_y,
    electronMethod_Q2, map_sub (g e.p)]
  rcases eq_or_ne (g e.p e.k - g e.p e.kPrime) 0 with h | h
  · -- Here `p·q_e = 0`, so `x_e` and `y_e` both divide by zero and both sides are the junk
    -- value `0` of Lean's division.
    simp [h]
  · field_simp
    ring

/-- After exactly collinear initial-state emission of the fraction `1 - z > 0` of the lepton
momentum, the electron-method Bjorken variable differs from a nonvanishing true one, in the
physical region `0 < y < 1` of the true inelasticity. -/
theorem electronMethod_x_ne_trueInvariants_x_of_collinear_initialState (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) (hz1 : z < 1)
    (hpk : g e.p e.k ≠ 0) (hy0 : 0 < (e.trueInvariants g .initialState).y)
    (hy1 : (e.trueInvariants g .initialState).y < 1)
    (hx : (e.trueInvariants g .initialState).x ≠ 0) :
    (electronMethod g e.k e.p e.kPrime).x ≠ (e.trueInvariants g .initialState).x := by
  rw [electronMethod_x_of_collinear_initialState g hk hk' hcol hpk hy0.ne']
  set x := (e.trueInvariants g .initialState).x
  set y := (e.trueInvariants g .initialState).y
  have hd : y < 1 - z * (1 - y) := by nlinarith
  rw [Ne, div_eq_iff (by linarith), mul_right_inj' hx]
  exact hd.ne

/-- The Sigma method recovers the true Bjorken variable after exactly collinear initial-state
emission. With `sigmaMethod_y_eq_trueInvariants_y_initialState`, the Sigma method is exact in
`(x, y)` (`shiftXY_sigmaMethod_eq_zero_of_collinear_initialState`); its virtuality is the electron
one, `Q² = z Q²_e`. -/
theorem sigmaMethod_x_eq_trueInvariants_x_of_collinear_initialState (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) (hpk : g e.p e.k ≠ 0) :
    (sigmaMethod g e.k e.p e.kPrime e.pX).x = (e.trueInvariants g .initialState).x := by
  rw [sigmaMethod_x, ← sigmaMethod_y g e.k, sigmaMethod_y_eq_trueInvariants_y_initialState g,
    trueInvariants_x_eq, trueInvariants_Q2_of_collinear_initialState g hk hcol, hk',
    apply_pX_sub_p_of_collinear_initialState g hcol,
    trueInvariants_y_of_collinear_initialState g hcol]
  field_simp
  ring

/-- After exactly collinear initial-state emission, the `(x, y)` shift of the Sigma method
vanishes. -/
theorem shiftXY_sigmaMethod_eq_zero_of_collinear_initialState (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) (hpk : g e.p e.k ≠ 0) :
    (sigmaMethod g e.k e.p e.kPrime e.pX).shiftXY (e.trueInvariants g .initialState) = 0 :=
  ReconstructedInvariants.shiftXY_eq_zero_iff.2
    ⟨sigmaMethod_x_eq_trueInvariants_x_of_collinear_initialState g hk hk' hcol hpk,
      sigmaMethod_y_eq_trueInvariants_y_initialState g⟩

end InitialState

/-! ### Final-state radiation -/

/-- After exactly collinear final-state emission, in which the photon carries the fraction
`1 - z` of the outgoing hard lepton momentum `k' + ℓ`, the electron method rescales the
virtuality by `z`, up to the mass of the incoming lepton: `Q²_e = z Q² - (1 - z) k²`, and
`Q²_e = z Q²` for a massless incoming lepton. -/
theorem electronMethod_Q2_of_collinear_finalState (g : Bilin V) {z : ℝ}
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • (e.kPrime + e.photon))
    (hz : z ≠ 0) :
    (electronMethod g e.k e.p e.kPrime).Q2 =
      z * (e.trueInvariants g .finalState).Q2 - (1 - z) * g e.k e.k := by
  have hq : e.pX - e.p = e.k - (e.kPrime + e.photon) := by rw [pX_sub_p]; abel
  rw [electronMethod_Q2, trueInvariants_Q2_eq, hq]
  generalize hw : e.kPrime + e.photon = w at hcol
  have hkw : e.kPrime = z • w := by
    rw [eq_sub_of_add_eq hw, hcol, sub_smul, one_smul, sub_sub_cancel]
  have hww : g w w = 0 := by
    simpa [hkw, hz] using hk'
  rw [hkw, ← neg_sub (z • w), ← neg_sub w]
  simp only [map_neg, LinearMap.neg_apply, neg_neg]
  rw [neg_apply_smul_sub, hww]
  ring

end RadiativeEvent

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
