/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, The EpsilonEridani contributors
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.Couplings

/-!
# The parity-violating lepton-fermion couplings `C₁` and `C₂` and the weak charges

At momentum transfer small compared with the `Z` mass, `Z` exchange between a lepton `ℓ` and a
fermion `f` contracts to a four-fermion contact interaction. Its parity-violating part is, in the
normalisation of the Particle Data Group,

`(G_F / √2) [C₁ (ℓ̄ γ^μ γ⁵ ℓ)(f̄ γ_μ f) + C₂ (ℓ̄ γ^μ ℓ)(f̄ γ_μ γ⁵ f)]`,

with

`C₁ = 2 g_A^ℓ g_V^f` and `C₂ = 2 g_V^ℓ g_A^f`,

where `g_V`, `g_A` are the vector and axial neutral-current couplings of `ℓ` and `f`. This file
defines `C₁` and `C₂` as these bilinear combinations of two arbitrary coupling pairs
(`FermionNeutralCurrentCouplings.c1`, `FermionNeutralCurrentCouplings.c2`), rather than as
numbers. For electron-quark scattering they are the couplings `C_{1q}` and `C_{2q}`
(`NeutralCurrentCouplings.c1Up` and so on), which parity-violating electron scattering measures.
Their Standard Model values in terms of `sin²θ_W` are theorems, proved from the couplings
`ofQuantumNumbers` at the Standard Model quantum numbers (`Electroweak.Couplings`).

The weak charge of a single lepton (the electron's `Q_W^e`) is a function of its own coupling pair,
and the weak charges of the proton, the neutron and a nucleus are functions of a coupling bundle;
all are built from `C₁`.

## Main definitions

* `FermionNeutralCurrentCouplings.c1`, `FermionNeutralCurrentCouplings.c2`: the couplings
  `C₁ = 2 g_A^ℓ g_V^f` and `C₂ = 2 g_V^ℓ g_A^f` of a lepton `ℓ` and a fermion `f`.
* `NeutralCurrentCouplings.c1Up`, `.c1Down`, `.c2Up`, `.c2Down`: the electron-quark couplings
  `C_{1u}`, `C_{1d}`, `C_{2u}`, `C_{2d}` of a coupling bundle.
* `FermionNeutralCurrentCouplings.leptonWeakCharge`: the weak charge `2 C₁ = 4 g_A g_V` of a
  lepton coupled to itself, which for the electron is `Q_W^e`.
* `NeutralCurrentCouplings.protonWeakCharge`, `.neutronWeakCharge`, `.nuclearWeakCharge`: the
  hadronic weak charges.

## Main results

* `FermionNeutralCurrentCouplings.c1_add_c2`, `FermionNeutralCurrentCouplings.c1_sub_c2`: in the
  chiral basis, `C₁ + C₂ = 4 (g_L^ℓ g_L^f - g_R^ℓ g_R^f)` and
  `C₁ - C₂ = 4 (g_L^ℓ g_R^f - g_R^ℓ g_L^f)`.
* `FermionNeutralCurrentCouplings.c1_ofQuantumNumbers_left`: `C₁` depends on the lepton only
  through its weak isospin `T³`, not through its charge or `sin²θ_W`.
* `smTreeLevelCouplings_c1Up` and its three companions: the Standard Model
  values `C_{1u} = -1/2 + (4/3) sin²θ_W`, `C_{1d} = 1/2 - (2/3) sin²θ_W`,
  `C_{2u} = -1/2 + 2 sin²θ_W`, `C_{2d} = 1/2 - 2 sin²θ_W`.
* `smTreeLevelCouplings_two_mul_c1Up_sub_c1Down` and
  `smTreeLevelCouplings_two_mul_c2Up_sub_c2Down`: the isoscalar
  combinations `2 C_{1u} - C_{1d} = -3/2 + (10/3) sin²θ_W` and
  `2 C_{2u} - C_{2d} = -3/2 + 6 sin²θ_W`, which the deuteron asymmetry measures.
* `FermionNeutralCurrentCouplings.c1_ofQuantumNumbers_electron`: electron-electron (Møller)
  scattering has `C₁ = (1 - 4 sin²θ_W) / 2`, computed from the electron's quantum numbers alone.
  Here `C₂ = C₁` too, but only because both fermions are the electron: in general `C₂` is `C₁` with
  the fermions exchanged (`FermionNeutralCurrentCouplings.c2_eq_c1_swap`).
* `smTreeLevelCouplings_neutronWeakCharge`: the neutron weak charge is
  `-1` at every `sin²θ_W`.

## References

* Particle Data Group, *Electroweak model and constraints on new physics*, for the normalisation
  of `C_{1q}`, `C_{2q}` and of the nucleon weak charges.
* R. N. Cahn and F. J. Gilman, *Polarized-electron-nucleon scattering in gauge theories of weak
  and electromagnetic interactions*, Phys. Rev. D 17 (1978) 1313, for the combinations
  `2 C_{1u} - C_{1d}` and `2 C_{2u} - C_{2d}` in the deuteron asymmetry.
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

open GenerationAssignments

namespace FermionNeutralCurrentCouplings

variable (ℓ f : FermionNeutralCurrentCouplings)

/-- The parity-violating coupling `C₁ = 2 g_A^ℓ g_V^f` of a lepton `ℓ` and a fermion `f`. It
multiplies the product of the lepton axial current and the fermion vector current in the
low-energy contact interaction. -/
def c1 : ℝ := 2 * ℓ.gA * f.gV

/-- The parity-violating coupling `C₂ = 2 g_V^ℓ g_A^f` of a lepton `ℓ` and a fermion `f`. It
multiplies the product of the lepton vector current and the fermion axial current in the
low-energy contact interaction. -/
def c2 : ℝ := 2 * ℓ.gV * f.gA

/-- The coupling `C₁` unfolded. -/
theorem c1_def : ℓ.c1 f = 2 * ℓ.gA * f.gV :=
  (rfl)

/-- The coupling `C₂` unfolded. -/
theorem c2_def : ℓ.c2 f = 2 * ℓ.gV * f.gA :=
  (rfl)

/-- `C₂` is `C₁` with the roles of the two fermions exchanged. -/
theorem c2_eq_c1_swap : ℓ.c2 f = f.c1 ℓ := by
  rw [c1_def, c2_def]
  ring

/-- In the chiral basis, `C₁ + C₂ = 4 (g_L^ℓ g_L^f - g_R^ℓ g_R^f)`: the sum couples equal
chiralities, with opposite signs for the left- and right-handed products. -/
theorem c1_add_c2 : ℓ.c1 f + ℓ.c2 f = 4 * (ℓ.gL * f.gL - ℓ.gR * f.gR) := by
  rw [c1_def, c2_def, gL_def, gL_def, gR_def, gR_def]
  ring

/-- In the chiral basis, `C₁ - C₂ = 4 (g_L^ℓ g_R^f - g_R^ℓ g_L^f)`: the difference couples
opposite chiralities. -/
theorem c1_sub_c2 : ℓ.c1 f - ℓ.c2 f = 4 * (ℓ.gL * f.gR - ℓ.gR * f.gL) := by
  rw [c1_def, c2_def, gL_def, gL_def, gR_def, gR_def]
  ring

/-- The coupling `C₁` of a lepton with quantum numbers `(t3, q)` is `2 T³ g_V^f`. It does not
depend on the lepton's charge or on `sin²θ_W`, because the lepton enters through its axial
coupling. -/
@[simp]
theorem c1_ofQuantumNumbers_left (t3 q s2 : ℝ) :
    (ofQuantumNumbers t3 q s2).c1 f = 2 * t3 * f.gV := by
  rw [c1_def, ofQuantumNumbers_gA]

/-- The coupling `C₂` of a fermion with quantum numbers `(t3, q)` is `2 g_V^ℓ T³`. It does not
depend on the fermion's charge or on `sin²θ_W`, because the fermion enters through its axial
coupling. -/
@[simp]
theorem c2_ofQuantumNumbers_right (t3 q s2 : ℝ) :
    ℓ.c2 (ofQuantumNumbers t3 q s2) = 2 * ℓ.gV * t3 := by
  rw [c2_def, ofQuantumNumbers_gA]

/-- **The Møller couplings.** For electron-electron scattering, with the electron's couplings
`ofQuantumNumbers` at the quantum numbers of the lower component of the lepton doublet, the
parity-violating coupling is `C₁ = (1 - 4 sin²θ_W) / 2`. Because both fermions are the electron,
`C₂` takes the same value by `c2_eq_c1_swap`. No hadronic input enters. -/
theorem c1_ofQuantumNumbers_electron (s2 : ℝ) :
    (ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YL : ℝ) 1) s2).c1
      (ofQuantumNumbers (isospinWeight 1) (doubletElectricCharge (standardModel.YL : ℝ) 1) s2)
      = (1 - 4 * s2) / 2 := by
  rw [isospinWeight_one, doubletElectricCharge_standardModel_YL_one, c1_ofQuantumNumbers_left,
    ofQuantumNumbers_gV]
  ring

/-- The lepton weak charge `Q_W = 2 C₁ = 4 g_A g_V`, where `C₁` is the coupling of the lepton
with itself. For the electron this is `Q_W^e`, which is `1 - 4 sin²θ_W` at tree level
(`smTreeLevelCouplings_electron_leptonWeakCharge`).

This `+2 C₁` convention is the lepton one only. It is the opposite sign to the `-2 C_{1q}` that the
hadronic charges `NeutralCurrentCouplings.protonWeakCharge` and
`NeutralCurrentCouplings.neutronWeakCharge` follow, so for a quark coupling pair this is not the
quark weak charge of that convention. With these conventions the tree-level electron and proton
weak charges are equal. -/
def leptonWeakCharge : ℝ := 2 * ℓ.c1 ℓ

/-- The lepton weak charge unfolded. -/
theorem leptonWeakCharge_def : ℓ.leptonWeakCharge = 2 * ℓ.c1 ℓ :=
  (rfl)

/-- The lepton weak charge is four times the product of the lepton's axial and vector couplings. -/
theorem leptonWeakCharge_eq_four_mul_gA_mul_gV : ℓ.leptonWeakCharge = 4 * ℓ.gA * ℓ.gV := by
  rw [leptonWeakCharge_def, c1_def]
  ring

/-- The lepton weak charge vanishes exactly when the axial or the vector coupling does. -/
theorem leptonWeakCharge_eq_zero_iff : ℓ.leptonWeakCharge = 0 ↔ ℓ.gA = 0 ∨ ℓ.gV = 0 := by
  rw [leptonWeakCharge_eq_four_mul_gA_mul_gV, mul_assoc, mul_eq_zero, mul_eq_zero]
  norm_num

end FermionNeutralCurrentCouplings

namespace NeutralCurrentCouplings

open FermionNeutralCurrentCouplings

variable (C : NeutralCurrentCouplings)

/-- The electron-up-quark coupling `C_{1u} = 2 g_A^e g_V^u`. -/
def c1Up : ℝ := C.electron.c1 C.upType

/-- The electron-down-quark coupling `C_{1d} = 2 g_A^e g_V^d`. -/
def c1Down : ℝ := C.electron.c1 C.downType

/-- The electron-up-quark coupling `C_{2u} = 2 g_V^e g_A^u`. -/
def c2Up : ℝ := C.electron.c2 C.upType

/-- The electron-down-quark coupling `C_{2d} = 2 g_V^e g_A^d`. -/
def c2Down : ℝ := C.electron.c2 C.downType

/-- The coupling `C_{1u}` unfolded. -/
theorem c1Up_def : C.c1Up = C.electron.c1 C.upType :=
  (rfl)

/-- The coupling `C_{1d}` unfolded. -/
theorem c1Down_def : C.c1Down = C.electron.c1 C.downType :=
  (rfl)

/-- The coupling `C_{2u}` unfolded. -/
theorem c2Up_def : C.c2Up = C.electron.c2 C.upType :=
  (rfl)

/-- The coupling `C_{2d}` unfolded. -/
theorem c2Down_def : C.c2Down = C.electron.c2 C.downType :=
  (rfl)

/-!
## Weak charges

The weak charge of a target measures how strongly it couples, through its vector current, to the
electron axial current by `Z` exchange at zero momentum transfer. For a nucleon it is `-2` times
the sum of `C_{1q}` over its valence quarks.

The electron weak charge `Q_W^e` is the lepton weak charge
`FermionNeutralCurrentCouplings.leptonWeakCharge` of the electron's own coupling pair,
`C.electron.leptonWeakCharge`, and needs no quark couplings.
-/

/-- The weak charge of the proton, `Q_W^p = -2 (2 C_{1u} + C_{1d})`. -/
def protonWeakCharge : ℝ := -2 * (2 * C.c1Up + C.c1Down)

/-- The weak charge of the neutron, `Q_W^n = -2 (C_{1u} + 2 C_{1d})`. -/
def neutronWeakCharge : ℝ := -2 * (C.c1Up + 2 * C.c1Down)

/-- The weak charge `Z Q_W^p + N Q_W^n` of a nucleus with `Z` protons and `N` neutrons. -/
def nuclearWeakCharge (Z N : ℝ) : ℝ := Z * C.protonWeakCharge + N * C.neutronWeakCharge

/-- The proton weak charge unfolded. -/
theorem protonWeakCharge_def : C.protonWeakCharge = -2 * (2 * C.c1Up + C.c1Down) :=
  (rfl)

/-- The neutron weak charge unfolded. -/
theorem neutronWeakCharge_def : C.neutronWeakCharge = -2 * (C.c1Up + 2 * C.c1Down) :=
  (rfl)

/-- The nuclear weak charge unfolded. -/
theorem nuclearWeakCharge_def (Z N : ℝ) :
    C.nuclearWeakCharge Z N = Z * C.protonWeakCharge + N * C.neutronWeakCharge :=
  (rfl)

end NeutralCurrentCouplings

open FermionNeutralCurrentCouplings NeutralCurrentCouplings

/-!
## Standard Model values

The tabulated couplings `smTreeLevelCouplings` are `ofQuantumNumbers` at the Standard Model
quantum numbers (`smTreeLevelCouplings_eq_ofQuantumNumbers`), so the values of `C_{1q}` and
`C_{2q}` below follow from the weak isospins and electric charges of one generation.
-/

/-- The Standard Model value `C_{1u} = -1/2 + (4/3) sin²θ_W`. -/
@[simp]
theorem smTreeLevelCouplings_c1Up (s2 : ℝ) :
    (smTreeLevelCouplings s2).c1Up = -1 / 2 + 4 / 3 * s2 := by
  rw [c1Up_def, smTreeLevelCouplings_electron_eq_ofQuantumNumbers,
    smTreeLevelCouplings_upType_eq_ofQuantumNumbers, c1_ofQuantumNumbers_left, ofQuantumNumbers_gV,
    isospinWeight_one, isospinWeight_zero, doubletElectricCharge_standardModel_YQ_zero]
  ring

/-- The Standard Model value `C_{1d} = 1/2 - (2/3) sin²θ_W`. -/
@[simp]
theorem smTreeLevelCouplings_c1Down (s2 : ℝ) :
    (smTreeLevelCouplings s2).c1Down = 1 / 2 - 2 / 3 * s2 := by
  rw [c1Down_def, smTreeLevelCouplings_electron_eq_ofQuantumNumbers,
    smTreeLevelCouplings_downType_eq_ofQuantumNumbers, c1_ofQuantumNumbers_left,
    ofQuantumNumbers_gV, isospinWeight_one, doubletElectricCharge_standardModel_YQ_one]
  ring

/-- The Standard Model value `C_{2u} = -1/2 + 2 sin²θ_W`. -/
@[simp]
theorem smTreeLevelCouplings_c2Up (s2 : ℝ) :
    (smTreeLevelCouplings s2).c2Up = -1 / 2 + 2 * s2 := by
  rw [c2Up_def, smTreeLevelCouplings_electron_eq_ofQuantumNumbers,
    smTreeLevelCouplings_upType_eq_ofQuantumNumbers, c2_ofQuantumNumbers_right,
    ofQuantumNumbers_gV, isospinWeight_one, isospinWeight_zero,
    doubletElectricCharge_standardModel_YL_one]
  ring

/-- The Standard Model value `C_{2d} = 1/2 - 2 sin²θ_W`. -/
@[simp]
theorem smTreeLevelCouplings_c2Down (s2 : ℝ) :
    (smTreeLevelCouplings s2).c2Down = 1 / 2 - 2 * s2 := by
  rw [c2Down_def, smTreeLevelCouplings_electron_eq_ofQuantumNumbers,
    smTreeLevelCouplings_downType_eq_ofQuantumNumbers, c2_ofQuantumNumbers_right,
    ofQuantumNumbers_gV, isospinWeight_one, doubletElectricCharge_standardModel_YL_one]
  ring

/-- The isoscalar combination `2 C_{1u} - C_{1d} = -3/2 + (10/3) sin²θ_W` that the
parity-violating deuteron asymmetry measures. -/
theorem smTreeLevelCouplings_two_mul_c1Up_sub_c1Down (s2 : ℝ) :
    2 * (smTreeLevelCouplings s2).c1Up - (smTreeLevelCouplings s2).c1Down
      = -3 / 2 + 10 / 3 * s2 := by
  rw [smTreeLevelCouplings_c1Up, smTreeLevelCouplings_c1Down]
  ring

/-- The isoscalar combination `2 C_{2u} - C_{2d} = -3/2 + 6 sin²θ_W` that the
parity-violating deuteron asymmetry measures. -/
theorem smTreeLevelCouplings_two_mul_c2Up_sub_c2Down (s2 : ℝ) :
    2 * (smTreeLevelCouplings s2).c2Up - (smTreeLevelCouplings s2).c2Down
      = -3 / 2 + 6 * s2 := by
  rw [smTreeLevelCouplings_c2Up, smTreeLevelCouplings_c2Down]
  ring

/-- At tree level the electron weak charge is `1 - 4 sin²θ_W`. -/
@[simp]
theorem smTreeLevelCouplings_electron_leptonWeakCharge (s2 : ℝ) :
    (smTreeLevelCouplings s2).electron.leptonWeakCharge = 1 - 4 * s2 := by
  rw [leptonWeakCharge_def, smTreeLevelCouplings_electron_eq_ofQuantumNumbers,
    c1_ofQuantumNumbers_electron]
  ring

/-- At tree level the proton weak charge is `1 - 4 sin²θ_W`, the same as the electron's. -/
@[simp]
theorem smTreeLevelCouplings_protonWeakCharge (s2 : ℝ) :
    (smTreeLevelCouplings s2).protonWeakCharge = 1 - 4 * s2 := by
  rw [protonWeakCharge_def, smTreeLevelCouplings_c1Up, smTreeLevelCouplings_c1Down]
  ring

/-- **The neutron weak charge is `-1`, independently of the weak-mixing angle.** The
`sin²θ_W` dependence of `C_{1u}` and `C_{1d}` cancels in the combination `C_{1u} + 2 C_{1d}`,
because the neutron is electrically neutral. This is why a heavy nucleus, whose weak charge is
dominated by `-N`, is a weak-mixing-angle probe only through its proton term. -/
@[simp]
theorem smTreeLevelCouplings_neutronWeakCharge (s2 : ℝ) :
    (smTreeLevelCouplings s2).neutronWeakCharge = -1 := by
  rw [neutronWeakCharge_def, smTreeLevelCouplings_c1Up, smTreeLevelCouplings_c1Down]
  ring

/-- At tree level a nucleus with `Z` protons and `N` neutrons has weak charge
`Z (1 - 4 sin²θ_W) - N`. -/
@[simp]
theorem smTreeLevelCouplings_nuclearWeakCharge (Z N s2 : ℝ) :
    (smTreeLevelCouplings s2).nuclearWeakCharge Z N = Z * (1 - 4 * s2) - N := by
  rw [nuclearWeakCharge_def, smTreeLevelCouplings_protonWeakCharge,
    smTreeLevelCouplings_neutronWeakCharge]
  ring

/-- The tree-level electron weak charge vanishes exactly at `sin²θ_W = 1/4`. Its accidental
smallness at the physical value is the reason the Møller asymmetry is a sensitive probe of the
weak-mixing angle. -/
theorem smTreeLevelCouplings_electron_leptonWeakCharge_eq_zero_iff (s2 : ℝ) :
    (smTreeLevelCouplings s2).electron.leptonWeakCharge = 0 ↔ s2 = 1 / 4 := by
  rw [leptonWeakCharge_eq_zero_iff, ← electron_gV_eq_zero_iff, smTreeLevelCouplings_electron]
  norm_num

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak
