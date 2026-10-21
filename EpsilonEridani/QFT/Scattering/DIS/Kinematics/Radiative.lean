/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.AccessMethods

/-!
# Radiative events, reconstruction methods, and the shift of the invariants

When the lepton of `e(k) + N(p) → e(k') + X` radiates a real photon `ℓ`, the invariants of the
hard scattering differ from the invariants an experiment computes from the measured momenta, and
the difference depends on which momenta are used. This module makes that statement precise.

The invariants of the hard scattering and the invariants computed from a measurement are carried
by two distinct types, `TrueInvariants` and `ReconstructedInvariants`, so that one cannot be used
for the other by accident; the only passage between them is the explicit
`TrueInvariants.toReconstructed`.

## Main definitions

* `RadiativeEvent`: the momenta `k, p, k', ℓ, p_X` of a radiative event, with momentum
  conservation `k + p = k' + ℓ + p_X`.
* `EmissionLine`: whether the photon was radiated by the incoming or by the outgoing lepton. This
  is a label on the amplitude, not a property of the photon momentum, so it is data supplied
  alongside the event.
* `RadiativeEvent.hardKinematics`, `RadiativeEvent.trueInvariants`: the kinematics of the hard
  scattering, whose lepton enters with `k - ℓ` after initial-state emission and leaves with
  `k' + ℓ` after final-state emission, and its invariants.
* `electronMethod`, `hadronicMethod`, `sigmaMethod`, `mixedMethod`: the reconstruction methods,
  each defined covariantly from the momenta it measures.

## Main statements

* `RadiativeEvent.electronMethod_eq_trueInvariants_of_photon_eq_zero` and its analogues: without
  a photon, every method returns the true invariants.
* `RadiativeEvent.hadronicMethod_eq_trueInvariants_finalState`: the hadronic method is exact for
  final-state radiation, while the electron method rescales the virtuality by the photon energy
  fraction (`RadiativeEvent.electronMethod_Q2_of_collinear_finalState`).
* `RadiativeEvent.sigmaMethod_y_eq_trueInvariants_y_initialState`: the Sigma method recovers the
  true inelasticity after any initial-state emission, and
  `RadiativeEvent.sigmaMethod_x_eq_trueInvariants_x_of_collinear` the true Bjorken variable after
  an exactly collinear one.
* `RadiativeEvent.electronMethod_x_of_collinear`,
  `RadiativeEvent.electronMethod_x_ne_trueInvariants_x_of_collinear`: after collinear
  initial-state emission of energy fraction `1 - z` the electron method returns
  `x_e = x y / (1 - z (1 - y))` in terms of the true `x` and `y`, which differs from `x`, and
  `Q²_e = Q² / z` (`RadiativeEvent.trueInvariants_Q2_of_collinear_initialState`).

The scalar products are those of an arbitrary bilinear form `g` on the momentum space, as for
`DisKinematics`. Exact collinearity of an on-shell photon with a lepton forces the lepton to be
massless, so the collinear statements take `k² = k'² = 0` as hypotheses; no other mass-shell
condition is used.

## References

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
  /-- The Bjorken variable `x = Q² / (2 p·q)`. -/
  x : ℝ
  /-- The photon virtuality `Q² = -q²`. -/
  Q2 : ℝ
  /-- The inelasticity `y = (p·q) / (p·k)`. -/
  y : ℝ

/-- The invariants `x`, `Q²` and `y` computed from a measurement by a reconstruction method. -/
@[ext] structure ReconstructedInvariants where
  /-- The reconstructed Bjorken variable. -/
  x : ℝ
  /-- The reconstructed photon virtuality. -/
  Q2 : ℝ
  /-- The reconstructed inelasticity. -/
  y : ℝ

/-- The reconstruction returned by an exact measurement of the true invariants `t`. -/
@[simps]
def TrueInvariants.toReconstructed (t : TrueInvariants) : ReconstructedInvariants where
  x := t.x
  Q2 := t.Q2
  y := t.y

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
structure RadiativeEvent (V : Type) [AddCommGroup V] where
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

/-! ### Reconstruction methods -/

/-- The electron method, from the incoming lepton `k`, the target `p` and the scattered lepton
`k'`: with `q_e = k - k'`, it returns `Q²_e = -q_e²`, `y_e = (p·q_e) / (p·k)` and
`x_e = Q²_e / (2 p·q_e)`. -/
@[simps]
def electronMethod (g : Bilin V) (k p kPrime : V) : ReconstructedInvariants where
  x := -g (k - kPrime) (k - kPrime) / (2 * g p (k - kPrime))
  Q2 := -g (k - kPrime) (k - kPrime)
  y := g p (k - kPrime) / g p k

/-- The hadronic method, from the incoming lepton `k`, the target `p` and the hadronic final state
`p_X`: with `q_h = p_X - p`, it returns `Q²_h = -q_h²`, `y_h = (p·q_h) / (p·k)` and
`x_h = Q²_h / (2 p·q_h)`. -/
@[simps]
def hadronicMethod (g : Bilin V) (k p pX : V) : ReconstructedInvariants where
  x := -g (pX - p) (pX - p) / (2 * g p (pX - p))
  Q2 := -g (pX - p) (pX - p)
  y := g p (pX - p) / g p k

/-- The Sigma method, from all four measured momenta: the virtuality `Q²_e` of the electron
method, the inelasticity `y_Σ = (p·q_h) / (p·q_h + p·k')` of Bassler and Bernardi
(`SigmaMethodData.ySigma`), in which the incoming lepton does not appear, and
`x_Σ = Q²_e / (2 (p·k) y_Σ)`. Bassler and Bernardi build their own virtuality from the
transverse momentum of the scattered lepton; it is not used here. -/
@[simps]
def sigmaMethod (g : Bilin V) (k p kPrime pX : V) : ReconstructedInvariants where
  x := -g (k - kPrime) (k - kPrime) / (2 * g p k * SigmaMethodData.ySigma ⟨pX, kPrime, p⟩ g)
  Q2 := -g (k - kPrime) (k - kPrime)
  y := SigmaMethodData.ySigma ⟨pX, kPrime, p⟩ g

/-- The mixed method, from all four measured momenta: the virtuality `Q²_e` of the electron
method, the inelasticity `y_h` of the hadronic method, and `x = Q²_e / (2 (p·k) y_h)`. -/
@[simps]
def mixedMethod (g : Bilin V) (k p kPrime pX : V) : ReconstructedInvariants where
  x := -g (k - kPrime) (k - kPrime) / (2 * g p k * (g p (pX - p) / g p k))
  Q2 := -g (k - kPrime) (k - kPrime)
  y := g p (pX - p) / g p k

/-- The electron method applied to the lepton momenta of a DIS kinematic record returns its
canonical invariants. -/
theorem electronMethod_disKinematics (g : Bilin V) (K : DisKinematics V) :
    electronMethod g K.k K.p K.kPrime = ⟨K.xBj g, K.Q2 g, K.yInel g⟩ := by
  simp [electronMethod, DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel, ← K.hq]

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

/-! ### Without a photon, every method is exact -/

section BornLimit

variable {e} (g : Bilin V) (l : EmissionLine)

/-- Without a photon, the electron method returns the true invariants. -/
theorem electronMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0) :
    electronMethod g e.k e.p e.kPrime = (e.trueInvariants g l).toReconstructed := by
  have hq : e.pX - e.p = e.k - e.kPrime := by rw [pX_sub_p, h, sub_zero]
  cases l <;> ext <;> simp [DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel, hq, h]

/-- Without a photon, the hadronic method returns the true invariants. -/
theorem hadronicMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0) :
    hadronicMethod g e.k e.p e.pX = (e.trueInvariants g l).toReconstructed := by
  cases l <;> ext <;> simp [DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel, h]

/-- Without a photon, the Sigma method returns the true invariants. -/
theorem sigmaMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0)
    (hpk : g e.p e.k ≠ 0) :
    sigmaMethod g e.k e.p e.kPrime e.pX = (e.trueInvariants g l).toReconstructed := by
  have hq : e.pX - e.p = e.k - e.kPrime := by rw [pX_sub_p, h, sub_zero]
  have hy : SigmaMethodData.ySigma ⟨e.pX, e.kPrime, e.p⟩ g =
      g e.p (e.k - e.kPrime) / g e.p e.k := by
    rw [SigmaMethodData.ySigma, hq, ← map_add, sub_add_cancel]
  cases l <;> ext <;> simp only [sigmaMethod_x, sigmaMethod_Q2, sigmaMethod_y, hy] <;>
    simp [DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel, hq, h]
  all_goals congr 1; field_simp

/-- Without a photon, the mixed method returns the true invariants. -/
theorem mixedMethod_eq_trueInvariants_of_photon_eq_zero (h : e.photon = 0)
    (hpk : g e.p e.k ≠ 0) :
    mixedMethod g e.k e.p e.kPrime e.pX = (e.trueInvariants g l).toReconstructed := by
  have hq : e.pX - e.p = e.k - e.kPrime := by rw [pX_sub_p, h, sub_zero]
  cases l <;> ext <;>
    simp [DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel, hq, h]
  all_goals congr 1; field_simp

end BornLimit

/-! ### The hadronic method -/

section Hadronic

variable (g : Bilin V)

/-- The hadronic method reconstructs the true virtuality whichever line radiates. -/
theorem hadronicMethod_Q2_eq_trueInvariants_Q2 (l : EmissionLine) :
    (hadronicMethod g e.k e.p e.pX).Q2 = (e.trueInvariants g l).Q2 := by
  simp [DisKinematics.Q2]

/-- The hadronic method reconstructs the true Bjorken variable whichever line radiates. -/
theorem hadronicMethod_x_eq_trueInvariants_x (l : EmissionLine) :
    (hadronicMethod g e.k e.p e.pX).x = (e.trueInvariants g l).x := by
  simp [DisKinematics.xBj, DisKinematics.Q2]

/-- The hadronic method is exact for final-state radiation. -/
theorem hadronicMethod_eq_trueInvariants_finalState :
    hadronicMethod g e.k e.p e.pX = (e.trueInvariants g .finalState).toReconstructed := by
  ext <;> simp [DisKinematics.xBj, DisKinematics.Q2, DisKinematics.yInel]

end Hadronic

/-! ### Initial-state radiation -/

section InitialState

variable {e} (g : Bilin V)

/-- The Sigma method recovers the true inelasticity after any initial-state emission: the
denominator `p·(p_X - p) + p·k'` of `y_Σ` is `p·(k - ℓ)`, the projection of the lepton momentum
that enters the hard scattering. -/
theorem sigmaMethod_y_eq_trueInvariants_y_initialState :
    (sigmaMethod g e.k e.p e.kPrime e.pX).y = (e.trueInvariants g .initialState).y := by
  have h : e.pX - e.p + e.kPrime = e.k - e.photon := by rw [pX_sub_p]; abel
  rw [sigmaMethod_y, SigmaMethodData.ySigma, ← map_add, h]
  simp [DisKinematics.yInel]

variable {z : ℝ}

/-- After initial-state emission of the fraction `1 - z` of the incoming lepton momentum, the
hard lepton enters with `z k`. -/
private theorem leptonIn_of_collinear (hcol : e.photon = (1 - z) • e.k) :
    e.k - e.photon = z • e.k := by
  rw [hcol, sub_smul, one_smul, sub_sub_cancel]

private theorem pX_sub_p_of_collinear (hcol : e.photon = (1 - z) • e.k) :
    e.pX - e.p = z • e.k - e.kPrime := by
  rw [pX_sub_p, sub_right_comm, leptonIn_of_collinear hcol]

/-- After exactly collinear initial-state emission of the fraction `1 - z` of the incoming
lepton momentum, the true virtuality is `z` times the electron-method one, `Q² = z Q²_e`. -/
theorem trueInvariants_Q2_of_collinear_initialState (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) :
    (e.trueInvariants g .initialState).Q2 = z * (electronMethod g e.k e.p e.kPrime).Q2 := by
  simp only [trueInvariants_Q2, DisKinematics.Q2, hardKinematics_q, pX_sub_p_of_collinear hcol,
    electronMethod_Q2, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, hk, hk']
  ring

/-- After exactly collinear initial-state emission, the electron method overestimates the
virtuality: `Q² < Q²_e = Q² / z`. -/
theorem trueInvariants_Q2_lt_electronMethod_Q2_of_collinear (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) (hz0 : 0 < z)
    (hz1 : z < 1) (hQ : 0 < (e.trueInvariants g .initialState).Q2) :
    (e.trueInvariants g .initialState).Q2 < (electronMethod g e.k e.p e.kPrime).Q2 := by
  have h := trueInvariants_Q2_of_collinear_initialState g hk hk' hcol
  nlinarith

/-- After exactly collinear initial-state emission, the electron-method inelasticity satisfies
`1 - y_e = z (1 - y)` in terms of the true inelasticity `y`. -/
theorem one_sub_electronMethod_y_of_collinear (hcol : e.photon = (1 - z) • e.k) (hz : z ≠ 0)
    (hpk : g e.p e.k ≠ 0) :
    1 - (electronMethod g e.k e.p e.kPrime).y =
      z * (1 - (e.trueInvariants g .initialState).y) := by
  simp only [electronMethod_y, trueInvariants_y, DisKinematics.yInel, hardKinematics_p,
    hardKinematics_q, hardKinematics_k, leptonIn_initialState, leptonIn_of_collinear hcol,
    pX_sub_p_of_collinear hcol, map_sub, map_smul, smul_eq_mul]
  field_simp
  ring

/-- After exactly collinear initial-state emission, the electron method returns the Bjorken
variable `x_e = x y / (1 - z (1 - y))` in terms of the true `x` and `y`. -/
theorem electronMethod_x_of_collinear (hk : g e.k e.k = 0) (hk' : g e.kPrime e.kPrime = 0)
    (hcol : e.photon = (1 - z) • e.k) (hpk : g e.p e.k ≠ 0)
    (hy : (e.trueInvariants g .initialState).y ≠ 0) :
    (electronMethod g e.k e.p e.kPrime).x =
      (e.trueInvariants g .initialState).x * (e.trueInvariants g .initialState).y /
        (1 - z * (1 - (e.trueInvariants g .initialState).y)) := by
  have hz : z ≠ 0 := by
    rintro rfl
    exact hy (by simp [DisKinematics.yInel, leptonIn_of_collinear hcol])
  rw [← one_sub_electronMethod_y_of_collinear g hcol hz hpk, sub_sub_cancel]
  simp only [trueInvariants_y, trueInvariants_x, DisKinematics.yInel, DisKinematics.xBj,
    DisKinematics.Q2, hardKinematics_p, hardKinematics_q, hardKinematics_k,
    leptonIn_initialState, leptonIn_of_collinear hcol, pX_sub_p_of_collinear hcol,
    electronMethod_x, electronMethod_y, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, hk, hk'] at hy ⊢
  have hzk : z * g e.p e.k - g e.p e.kPrime ≠ 0 := (div_ne_zero_iff.mp hy).1
  rcases eq_or_ne (g e.p e.k - g e.p e.kPrime) 0 with h | h
  · simp [h]
  · have hzk' : g e.p e.k * z - g e.p e.kPrime ≠ 0 := by rwa [mul_comm]
    field_simp
    ring

/-- After exactly collinear initial-state emission of the fraction `1 - z > 0` of the lepton
momentum, the electron-method Bjorken variable differs from the true one, in the physical region
`0 < y < 1` of the true inelasticity. -/
theorem electronMethod_x_ne_trueInvariants_x_of_collinear (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) (hz1 : z < 1)
    (hpk : g e.p e.k ≠ 0) (hy0 : 0 < (e.trueInvariants g .initialState).y)
    (hy1 : (e.trueInvariants g .initialState).y < 1)
    (hx : (e.trueInvariants g .initialState).x ≠ 0) :
    (electronMethod g e.k e.p e.kPrime).x ≠ (e.trueInvariants g .initialState).x := by
  rw [electronMethod_x_of_collinear g hk hk' hcol hpk hy0.ne']
  set x := (e.trueInvariants g .initialState).x
  set y := (e.trueInvariants g .initialState).y
  have hd : y < 1 - z * (1 - y) := by nlinarith
  rw [Ne, div_eq_iff (by linarith), mul_right_inj' hx]
  exact hd.ne

/-- The Sigma method recovers the true Bjorken variable after exactly collinear initial-state
emission. With `sigmaMethod_y_eq_trueInvariants_y_initialState`, the Sigma method is exact in
`(x, y)`; its virtuality is the electron one, `Q²_e = Q² / z`. -/
theorem sigmaMethod_x_eq_trueInvariants_x_of_collinear (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • e.k) (hpk : g e.p e.k ≠ 0) :
    (sigmaMethod g e.k e.p e.kPrime e.pX).x = (e.trueInvariants g .initialState).x := by
  have hy := sigmaMethod_y_eq_trueInvariants_y_initialState g (e := e)
  rw [sigmaMethod_y] at hy
  rw [sigmaMethod_x, hy]
  simp only [trueInvariants_y, trueInvariants_x, DisKinematics.yInel, DisKinematics.xBj,
    DisKinematics.Q2, hardKinematics_p, hardKinematics_q, hardKinematics_k,
    leptonIn_initialState, leptonIn_of_collinear hcol, pX_sub_p_of_collinear hcol, map_sub,
    map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hk, hk']
  rcases eq_or_ne (z * g e.p e.k - g e.p e.kPrime) 0 with h | h
  · simp [h]
  · have h' : g e.p e.k * z - g e.p e.kPrime ≠ 0 := by rwa [mul_comm]
    field_simp
    ring

end InitialState

/-! ### Final-state radiation -/

/-- After exactly collinear final-state emission, in which the photon carries the fraction
`1 - z` of the outgoing hard lepton momentum `k' + ℓ`, the electron method rescales the
virtuality by `z`: `Q²_e = z Q²`. -/
theorem electronMethod_Q2_of_collinear_finalState (g : Bilin V) {z : ℝ} (hk : g e.k e.k = 0)
    (hk' : g e.kPrime e.kPrime = 0) (hcol : e.photon = (1 - z) • (e.kPrime + e.photon))
    (hz : z ≠ 0) :
    (electronMethod g e.k e.p e.kPrime).Q2 = z * (e.trueInvariants g .finalState).Q2 := by
  have hq : e.pX - e.p = e.k - (e.kPrime + e.photon) := by rw [pX_sub_p]; abel
  simp only [electronMethod_Q2, trueInvariants_Q2, DisKinematics.Q2, hardKinematics_q, hq]
  generalize hw : e.kPrime + e.photon = w at hcol
  have hkw : e.kPrime = z • w := by
    rw [eq_sub_of_add_eq hw, hcol, sub_smul, one_smul, sub_sub_cancel]
  simp only [hkw, map_smul, LinearMap.smul_apply, smul_eq_mul] at hk'
  have hww : g w w = 0 := by simpa [hz] using hk'
  rw [hkw]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hk,
    hww]
  ring

end RadiativeEvent

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
