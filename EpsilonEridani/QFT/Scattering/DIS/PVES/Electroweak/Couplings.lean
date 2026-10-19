/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.ElectricCharge
public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.Parameters
public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.Representation

/-!
# Neutral-current couplings as functions of the quantum numbers

A chiral fermion field with weak-isospin third component `T³` and electric charge `Q` couples to
the `Z` boson with strength `(g / cos θ_W) (T³ - Q sin²θ_W)`. In the Standard Model the
left-handed component of a fermion is a component of a weak-isospin doublet and the right-handed
component is a singlet (`T³ = 0`) of the same electric charge, so its left- and right-handed
couplings are

`g_L = T³ - Q sin²θ_W` and `g_R = -Q sin²θ_W`.

The vector and axial couplings of the Particle Data Group, in which the `Z` vertex is
`-i (g / (2 cos θ_W)) γ^μ (g_V - g_A γ⁵)`, are `g_V = g_L + g_R` and `g_A = g_L - g_R`, that is

`g_V = T³ - 2 Q sin²θ_W` and `g_A = T³`.

This file defines these couplings for an arbitrary fermion as functions of `(T³, Q, sin²θ_W)`,
and then evaluates them at the quantum numbers of one Standard Model generation: the weak-isospin
weights `isospinWeight` of a doublet, the hypercharges `GenerationAssignments.standardModel`, and
the electric charges `Q = T³ + Y / 2` of `doubletElectricCharge` and `singletElectricCharge`. The
result is that the tabulated couplings `smTreeLevelCouplings` used by the parity-violating
scattering interfaces are the values of the general coupling function at these quantum numbers,
rather than independent data.

## Main definitions

* `chiralCoupling t3 q s2`: the `Z` coupling `T³ - Q sin²θ_W` of a chiral field.
* `FermionNeutralCurrentCouplings.gL`, `FermionNeutralCurrentCouplings.gR`: the left- and
  right-handed couplings `(g_V ± g_A) / 2` of a vector/axial coupling pair.
* `FermionNeutralCurrentCouplings.ofQuantumNumbers t3 q s2`: the couplings
  `g_V = T³ - 2 Q sin²θ_W`, `g_A = T³` of a fermion whose left-handed component has
  weak-isospin third component `t3` and whose electric charge is `q`.

## Main results

* `FermionNeutralCurrentCouplings.gL_add_gR`, `FermionNeutralCurrentCouplings.gL_sub_gR`:
  `g_V = g_L + g_R` and `g_A = g_L - g_R`.
* `FermionNeutralCurrentCouplings.eq_ofQuantumNumbers_iff`: a coupling pair is that of the
  quantum numbers `(T³, Q)` exactly when its left-handed coupling is the `Z` coupling of a field
  with these quantum numbers and its right-handed coupling is that of a singlet of charge `Q`.
* `smTreeLevelCouplings_eq`: the tabulated electron, up-quark and down-quark couplings are the
  values of `ofQuantumNumbers` at the Standard Model quantum numbers.
* `ofQuantumNumbers_neutrino`: the neutrino is electrically neutral, but it couples to the `Z`
  with `g_V = g_A = 1/2` at every value of `sin²θ_W`.

## References

* Particle Data Group, *Electroweak model and constraints on new physics*, for the normalisation
  of `g_V`, `g_A` and of the chiral couplings.
* S. Weinberg, *A model of leptons*, Phys. Rev. Lett. 19 (1967) 1264.
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

/-- The neutral-current coupling `T³ - Q sin²θ_W` of a chiral fermion field with weak-isospin
third component `t3` and electric charge `q`, at `sin²θ_W = s2`. It is the charge with which the
field couples to the `Z` boson, in units of `g / cos θ_W`; a weak-isospin singlet has `t3 = 0`. -/
def chiralCoupling (t3 q s2 : ℝ) : ℝ := t3 - q * s2

/-- The chiral coupling unfolded. -/
theorem chiralCoupling_def (t3 q s2 : ℝ) : chiralCoupling t3 q s2 = t3 - q * s2 :=
  (rfl)

/-- An electrically neutral weak-isospin singlet does not couple to the `Z` boson. -/
@[simp]
theorem chiralCoupling_zero_zero (s2 : ℝ) : chiralCoupling 0 0 s2 = 0 := by
  simp [chiralCoupling_def]

namespace FermionNeutralCurrentCouplings

variable (c d : FermionNeutralCurrentCouplings)

/-- The left-handed neutral-current coupling `g_L = (g_V + g_A) / 2`. -/
def gL : ℝ := (c.gV + c.gA) / 2

/-- The right-handed neutral-current coupling `g_R = (g_V - g_A) / 2`. -/
def gR : ℝ := (c.gV - c.gA) / 2

/-- The left-handed coupling unfolded. -/
theorem gL_def : c.gL = (c.gV + c.gA) / 2 :=
  (rfl)

/-- The right-handed coupling unfolded. -/
theorem gR_def : c.gR = (c.gV - c.gA) / 2 :=
  (rfl)

/-- The vector coupling is the sum of the chiral couplings, `g_V = g_L + g_R`. -/
@[simp]
theorem gL_add_gR : c.gL + c.gR = c.gV := by
  rw [gL_def, gR_def]
  ring

/-- The axial coupling is the difference of the chiral couplings, `g_A = g_L - g_R`. -/
@[simp]
theorem gL_sub_gR : c.gL - c.gR = c.gA := by
  rw [gL_def, gR_def]
  ring

variable {c d} in
/-- A vector/axial coupling pair is determined by its two chiral couplings. -/
theorem ext_gL_gR (hL : c.gL = d.gL) (hR : c.gR = d.gR) : c = d := by
  obtain ⟨cV, cA⟩ := c
  obtain ⟨dV, dA⟩ := d
  have hV : cV = dV := by
    simpa using congrArg₂ (· + ·) hL hR
  have hA : cA = dA := by
    simpa using congrArg₂ (· - ·) hL hR
  rw [hV, hA]

variable {c d} in
/-- Two vector/axial coupling pairs are equal exactly when their chiral couplings agree. -/
theorem ext_gL_gR_iff : c = d ↔ c.gL = d.gL ∧ c.gR = d.gR :=
  ⟨fun h => h ▸ ⟨rfl, rfl⟩, fun h => ext_gL_gR h.1 h.2⟩

/-- The neutral-current couplings `g_V = T³ - 2 Q sin²θ_W` and `g_A = T³` of a fermion whose
left-handed component has weak-isospin third component `t3`, whose right-handed component is a
weak-isospin singlet, and whose electric charge is `q`, at `sin²θ_W = s2`. The normalisation is
that of the Particle Data Group: the `Z` vertex is `-i (g / (2 cos θ_W)) γ^μ (g_V - g_A γ⁵)`. -/
def ofQuantumNumbers (t3 q s2 : ℝ) : FermionNeutralCurrentCouplings where
  gV := t3 - 2 * q * s2
  gA := t3

/-- The vector coupling `g_V = T³ - 2 Q sin²θ_W`. -/
@[simp]
theorem ofQuantumNumbers_gV (t3 q s2 : ℝ) : (ofQuantumNumbers t3 q s2).gV = t3 - 2 * q * s2 :=
  (rfl)

/-- The axial coupling `g_A = T³`. -/
@[simp]
theorem ofQuantumNumbers_gA (t3 q s2 : ℝ) : (ofQuantumNumbers t3 q s2).gA = t3 :=
  (rfl)

/-- The left-handed coupling of `ofQuantumNumbers t3 q s2` is the `Z` coupling of a field with
weak-isospin third component `t3` and charge `q`. -/
@[simp]
theorem ofQuantumNumbers_gL (t3 q s2 : ℝ) :
    (ofQuantumNumbers t3 q s2).gL = chiralCoupling t3 q s2 := by
  rw [gL_def, ofQuantumNumbers_gV, ofQuantumNumbers_gA, chiralCoupling_def]
  ring

/-- The right-handed coupling of `ofQuantumNumbers t3 q s2` is the `Z` coupling of a
weak-isospin singlet of charge `q`. -/
@[simp]
theorem ofQuantumNumbers_gR (t3 q s2 : ℝ) :
    (ofQuantumNumbers t3 q s2).gR = chiralCoupling 0 q s2 := by
  rw [gR_def, ofQuantumNumbers_gV, ofQuantumNumbers_gA, chiralCoupling_def]
  ring

/-- A vector/axial coupling pair is that of the quantum numbers `(t3, q)` exactly when its
left-handed coupling is the `Z` coupling of a field with these quantum numbers and its
right-handed coupling is the `Z` coupling of a singlet of the same charge. -/
theorem eq_ofQuantumNumbers_iff {c : FermionNeutralCurrentCouplings} {t3 q s2 : ℝ} :
    c = ofQuantumNumbers t3 q s2 ↔
      c.gL = chiralCoupling t3 q s2 ∧ c.gR = chiralCoupling 0 q s2 := by
  rw [ext_gL_gR_iff, ofQuantumNumbers_gL, ofQuantumNumbers_gR]

/-- An electrically neutral fermion couples to the `Z` only through its left-handed component:
its vector and axial couplings both equal `T³`, whatever the value of `sin²θ_W`. -/
theorem ofQuantumNumbers_neutral (t3 s2 : ℝ) :
    ofQuantumNumbers t3 0 s2 = { gV := t3, gA := t3 } := by
  rw [ofQuantumNumbers]
  simp

end FermionNeutralCurrentCouplings

/-!
## The quantum numbers of one Standard Model generation

With the Standard Model hypercharges `(YQ, Yu, Yd, YL, Ye) = (1/3, 4/3, -2/3, -1, -2)`, the
charge formula `Q = T³ + Y / 2` gives the physical charges of the five multiplets. In particular
the left-handed (doublet) and right-handed (singlet) components of the up quark, the down quark
and the electron carry the same charge, which is what allows a single `Q` in `ofQuantumNumbers`.
-/

open GenerationAssignments FermionNeutralCurrentCouplings

/-- The up quark, the upper component of the quark doublet, has charge `2/3`. -/
@[simp]
theorem doubletElectricCharge_standardModel_YQ_zero :
    doubletElectricCharge (standardModel.YQ : ℝ) 0 = 2 / 3 := by
  norm_num [doubletElectricCharge_apply]

/-- The down quark, the lower component of the quark doublet, has charge `-1/3`. -/
@[simp]
theorem doubletElectricCharge_standardModel_YQ_one :
    doubletElectricCharge (standardModel.YQ : ℝ) 1 = -1 / 3 := by
  norm_num [doubletElectricCharge_apply]

/-- The neutrino, the upper component of the lepton doublet, is electrically neutral. -/
@[simp]
theorem doubletElectricCharge_standardModel_YL_zero :
    doubletElectricCharge (standardModel.YL : ℝ) 0 = 0 := by
  norm_num [doubletElectricCharge_apply]

/-- The electron, the lower component of the lepton doublet, has charge `-1`. -/
@[simp]
theorem doubletElectricCharge_standardModel_YL_one :
    doubletElectricCharge (standardModel.YL : ℝ) 1 = -1 := by
  norm_num [doubletElectricCharge_apply]

/-- The right-handed up-quark singlet has charge `2/3`. -/
@[simp]
theorem singletElectricCharge_standardModel_Yu :
    singletElectricCharge (standardModel.Yu : ℝ) = 2 / 3 := by
  norm_num [singletElectricCharge_def]

/-- The right-handed down-quark singlet has charge `-1/3`. -/
@[simp]
theorem singletElectricCharge_standardModel_Yd :
    singletElectricCharge (standardModel.Yd : ℝ) = -1 / 3 := by
  norm_num [singletElectricCharge_def]

/-- The right-handed electron singlet has charge `-1`. -/
@[simp]
theorem singletElectricCharge_standardModel_Ye :
    singletElectricCharge (standardModel.Ye : ℝ) = -1 := by
  norm_num [singletElectricCharge_def]

/-!
## The tabulated couplings are derived

The couplings `smTreeLevelCouplings` of the parity-violating scattering interfaces were entered
as data. They are the values of `ofQuantumNumbers` at the quantum numbers above.
-/

/-- **The tabulated neutral-current couplings are derived from the gauge quantum numbers.** At
every `sin²θ_W`, the electron, up-quark and down-quark couplings of `smTreeLevelCouplings` are
`ofQuantumNumbers` evaluated at the weak-isospin weight of the fermion's doublet component and at
the electric charge `T³ + Y / 2` that the Standard Model hypercharge of its doublet gives it. -/
theorem smTreeLevelCouplings_eq (s2 : ℝ) :
    smTreeLevelCouplings s2 =
      { electron :=
          ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YL : ℝ) 1) s2
        upType :=
          ofQuantumNumbers (isospinWeight 0) (doubletElectricCharge (standardModel.YQ : ℝ) 0) s2
        downType :=
          ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YQ : ℝ) 1)
            s2 } := by
  simp only [smTreeLevelCouplings, ofQuantumNumbers, isospinWeight_zero, isospinWeight_one,
    doubletElectricCharge_standardModel_YL_one, doubletElectricCharge_standardModel_YQ_zero,
    doubletElectricCharge_standardModel_YQ_one, NeutralCurrentCouplings.mk.injEq,
    FermionNeutralCurrentCouplings.mk.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> ring

/-- **The neutrino couples to the `Z` but not to the photon.** The upper component of the
Standard Model lepton doublet has electric charge `0`
(`doubletElectricCharge_standardModel_YL_zero`), but its neutral-current couplings are
`g_V = g_A = 1/2`, independently of `sin²θ_W`. Its right-handed coupling `g_R = (g_V - g_A) / 2`
vanishes, so the result does not depend on whether a right-handed neutral singlet is present. -/
theorem ofQuantumNumbers_neutrino (s2 : ℝ) :
    ofQuantumNumbers (isospinWeight 0) (doubletElectricCharge (standardModel.YL : ℝ) 0) s2 =
      { gV := 1 / 2, gA := 1 / 2 } := by
  rw [doubletElectricCharge_standardModel_YL_zero, ofQuantumNumbers_neutral, isospinWeight_zero]

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak
