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

The couplings of an arbitrary fermion, as functions of `(T³, Q, sin²θ_W)`, are `chiralCoupling`
and `FermionNeutralCurrentCouplings.ofQuantumNumbers` of `Electroweak.Parameters`. This file
evaluates them at the quantum numbers of one Standard Model generation: the weak-isospin
weights `isospinWeight` of a doublet, the hypercharges `GenerationAssignments.standardModel`, and
the electric charges `Q = T³ + Y / 2` of `doubletElectricCharge` and `singletElectricCharge`. The
result is that the tabulated couplings `smTreeLevelCouplings` used by the parity-violating
scattering interfaces are the values of the general coupling function at these quantum numbers,
rather than independent data.

## Main results

* `doubletElectricCharge_standardModel_YQ_zero_eq_singletElectricCharge_standardModel_Yu` and
  its down-quark and electron analogues: the doublet and singlet components of each charged
  Standard Model fermion carry the same electric charge.
* `smTreeLevelCouplings_electron_eq_ofQuantumNumbers`,
  `smTreeLevelCouplings_upType_eq_ofQuantumNumbers`,
  `smTreeLevelCouplings_downType_eq_ofQuantumNumbers`: the tabulated electron, up-quark and
  down-quark couplings are the values of `ofQuantumNumbers` at the Standard Model quantum numbers;
  `smTreeLevelCouplings_eq_ofQuantumNumbers` collects the three.
* `FermionNeutralCurrentCouplings.ofQuantumNumbers_neutrino`: the neutrino is electrically
  neutral, but it couples to the `Z` with `g_V = g_A = 1/2` at every value of `sin²θ_W`.

## References

* Particle Data Group, *Electroweak model and constraints on new physics*, for the normalisation
  of `g_V`, `g_A` and of the chiral couplings.
* S. Weinberg, *A model of leptons*, Phys. Rev. Lett. 19 (1967) 1264.
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

/-!
## The quantum numbers of one Standard Model generation

With the Standard Model hypercharges `(YQ, Yu, Yd, YL, Ye) = (1/3, 4/3, -2/3, -1, -2)`, the
charge formula `Q = T³ + Y / 2` gives the physical charges of the five multiplets. In particular
the left-handed (doublet) and right-handed (singlet) components of the up quark, the down quark
and the electron carry the same charge, which is what allows a single `Q` in `ofQuantumNumbers`;
the three `_eq_singletElectricCharge_` lemmas below state this, as instances of
`doubletElectricCharge_eq_singletElectricCharge_add_two_mul_isospinWeight`.
-/

open GenerationAssignments FermionNeutralCurrentCouplings

/-- The left-handed up quark, the upper component of the quark doublet, and the right-handed
up-quark singlet carry the same electric charge. -/
theorem doubletElectricCharge_standardModel_YQ_zero_eq_singletElectricCharge_standardModel_Yu :
    doubletElectricCharge (standardModel.YQ : ℝ) 0 =
      singletElectricCharge (standardModel.Yu : ℝ) := by
  rw [doubletElectricCharge_eq_singletElectricCharge_add_two_mul_isospinWeight,
    isospinWeight_zero]
  congr 1
  norm_num

/-- The left-handed down quark, the lower component of the quark doublet, and the right-handed
down-quark singlet carry the same electric charge. -/
theorem doubletElectricCharge_standardModel_YQ_one_eq_singletElectricCharge_standardModel_Yd :
    doubletElectricCharge (standardModel.YQ : ℝ) 1 =
      singletElectricCharge (standardModel.Yd : ℝ) := by
  rw [doubletElectricCharge_eq_singletElectricCharge_add_two_mul_isospinWeight,
    isospinWeight_one]
  congr 1
  norm_num

/-- The left-handed electron, the lower component of the lepton doublet, and the right-handed
electron singlet carry the same electric charge. -/
theorem doubletElectricCharge_standardModel_YL_one_eq_singletElectricCharge_standardModel_Ye :
    doubletElectricCharge (standardModel.YL : ℝ) 1 =
      singletElectricCharge (standardModel.Ye : ℝ) := by
  rw [doubletElectricCharge_eq_singletElectricCharge_add_two_mul_isospinWeight,
    isospinWeight_one]
  congr 1
  norm_num

/-- The up quark, the upper component of the quark doublet, has charge `2/3`. -/
theorem doubletElectricCharge_standardModel_YQ_zero :
    doubletElectricCharge (standardModel.YQ : ℝ) 0 = 2 / 3 := by
  norm_num [doubletElectricCharge_apply]

/-- The down quark, the lower component of the quark doublet, has charge `-1/3`. -/
theorem doubletElectricCharge_standardModel_YQ_one :
    doubletElectricCharge (standardModel.YQ : ℝ) 1 = -1 / 3 := by
  norm_num [doubletElectricCharge_apply]

/-- The neutrino, the upper component of the lepton doublet, is electrically neutral. -/
theorem doubletElectricCharge_standardModel_YL_zero :
    doubletElectricCharge (standardModel.YL : ℝ) 0 = 0 := by
  norm_num [doubletElectricCharge_apply]

/-- The electron, the lower component of the lepton doublet, has charge `-1`. -/
theorem doubletElectricCharge_standardModel_YL_one :
    doubletElectricCharge (standardModel.YL : ℝ) 1 = -1 := by
  norm_num [doubletElectricCharge_apply]

/-- The right-handed up-quark singlet has charge `2/3`. -/
theorem singletElectricCharge_standardModel_Yu :
    singletElectricCharge (standardModel.Yu : ℝ) = 2 / 3 := by
  rw [← doubletElectricCharge_standardModel_YQ_zero_eq_singletElectricCharge_standardModel_Yu,
    doubletElectricCharge_standardModel_YQ_zero]

/-- The right-handed down-quark singlet has charge `-1/3`. -/
theorem singletElectricCharge_standardModel_Yd :
    singletElectricCharge (standardModel.Yd : ℝ) = -1 / 3 := by
  rw [← doubletElectricCharge_standardModel_YQ_one_eq_singletElectricCharge_standardModel_Yd,
    doubletElectricCharge_standardModel_YQ_one]

/-- The right-handed electron singlet has charge `-1`. -/
theorem singletElectricCharge_standardModel_Ye :
    singletElectricCharge (standardModel.Ye : ℝ) = -1 := by
  rw [← doubletElectricCharge_standardModel_YL_one_eq_singletElectricCharge_standardModel_Ye,
    doubletElectricCharge_standardModel_YL_one]

/-!
## The tabulated couplings are derived

The couplings `smTreeLevelCouplings` of the parity-violating scattering interfaces were entered
as data. They are the values of `ofQuantumNumbers` at the quantum numbers above.
-/

/-- The tabulated electron couplings are `ofQuantumNumbers` at the quantum numbers of the lower
component of the lepton doublet. -/
theorem smTreeLevelCouplings_electron_eq_ofQuantumNumbers (s2 : ℝ) :
    (smTreeLevelCouplings s2).electron =
      ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YL : ℝ) 1) s2 := by
  rw [isospinWeight_one, doubletElectricCharge_standardModel_YL_one, eq_ofQuantumNumbers_iff,
    gL_def, gR_def, chiralCoupling_def, chiralCoupling_def]
  simp only [smTreeLevelCouplings]
  constructor <;> ring

/-- The tabulated up-quark couplings are `ofQuantumNumbers` at the quantum numbers of the upper
component of the quark doublet. -/
theorem smTreeLevelCouplings_upType_eq_ofQuantumNumbers (s2 : ℝ) :
    (smTreeLevelCouplings s2).upType =
      ofQuantumNumbers (isospinWeight 0) (doubletElectricCharge (standardModel.YQ : ℝ) 0) s2 := by
  rw [isospinWeight_zero, doubletElectricCharge_standardModel_YQ_zero, eq_ofQuantumNumbers_iff,
    gL_def, gR_def, chiralCoupling_def, chiralCoupling_def]
  simp only [smTreeLevelCouplings]
  constructor <;> ring

/-- The tabulated down-quark couplings are `ofQuantumNumbers` at the quantum numbers of the lower
component of the quark doublet. -/
theorem smTreeLevelCouplings_downType_eq_ofQuantumNumbers (s2 : ℝ) :
    (smTreeLevelCouplings s2).downType =
      ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YQ : ℝ) 1) s2 := by
  rw [isospinWeight_one, doubletElectricCharge_standardModel_YQ_one, eq_ofQuantumNumbers_iff,
    gL_def, gR_def, chiralCoupling_def, chiralCoupling_def]
  simp only [smTreeLevelCouplings]
  constructor <;> ring

/-- **The tabulated neutral-current couplings are derived from the gauge quantum numbers.** At
every `sin²θ_W`, the electron, up-quark and down-quark couplings of `smTreeLevelCouplings` are
`ofQuantumNumbers` evaluated at the weak-isospin weight of the fermion's doublet component and at
the electric charge `T³ + Y / 2` that the Standard Model hypercharge of its doublet gives it. -/
theorem smTreeLevelCouplings_eq_ofQuantumNumbers (s2 : ℝ) :
    smTreeLevelCouplings s2 =
      { electron :=
          ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YL : ℝ) 1) s2
        upType :=
          ofQuantumNumbers (isospinWeight 0) (doubletElectricCharge (standardModel.YQ : ℝ) 0) s2
        downType :=
          ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YQ : ℝ) 1)
            s2 } := by
  rw [← smTreeLevelCouplings_electron_eq_ofQuantumNumbers,
    ← smTreeLevelCouplings_upType_eq_ofQuantumNumbers,
    ← smTreeLevelCouplings_downType_eq_ofQuantumNumbers]

namespace FermionNeutralCurrentCouplings

/-- **The neutrino couples to the `Z` but not to the photon.** The upper component of the
Standard Model lepton doublet has electric charge `0`
(`doubletElectricCharge_standardModel_YL_zero`), but its neutral-current couplings are
`g_V = g_A = 1/2`, independently of `sin²θ_W`. Its right-handed coupling `g_R = (g_V - g_A) / 2`
vanishes, so the result does not depend on whether a right-handed neutral singlet is present. -/
theorem ofQuantumNumbers_neutrino (s2 : ℝ) :
    ofQuantumNumbers (isospinWeight 0) (doubletElectricCharge (standardModel.YL : ℝ) 0) s2 =
      { gV := 1 / 2, gA := 1 / 2 } := by
  rw [doubletElectricCharge_standardModel_YL_zero, ofQuantumNumbers_charge_zero, isospinWeight_zero]

end FermionNeutralCurrentCouplings

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak
