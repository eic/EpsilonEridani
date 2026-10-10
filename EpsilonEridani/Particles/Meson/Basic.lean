/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pseudoscalar mesons as data

A pseudoscalar meson is recorded as explicit data over a flavour type: its mass, its decay
constant, its electric charge in units of the positron charge, and the flavours of its valence
quark and valence antiquark. It is a structure rather than a typeclass on the flavour type, so that
two different mesons over the same flavour type, such as the positive pion and the positive kaon,
can be compared. The mass and the decay constant are positive; the chiral limit is reached as the
limit of a family of such data, never as an instance.

The decay constant is the one of the axial-current matrix element
`⟨0| q̄ γ^μ γ₅ q |M(P)⟩ = i f_M P^μ`, in which the charged-pion constant is close to `130 MeV`
rather than `92 MeV`.

The valence content enters the parton densities of a meson only through its *net valence
numbers*: the number of valence quarks minus the number of valence antiquarks of each flavour,
`PseudoscalarMeson.valenceNumber`. For a flavoured meson, one whose valence quark and antiquark
flavours differ, this is `+1` on the quark flavour, `-1` on the antiquark flavour and `0`
elsewhere, and it determines the valence pair (`valenceNumber_inj`). For a meson whose valence
quark and antiquark have the same flavour it vanishes identically (`valenceNumber_eq_zero_iff`).
Weighted by the quark charges, the net valence numbers sum to the meson's charge whenever the
charge is the one carried by the valence pair (`IsChargeConsistent.sum_mul_valenceNumber`).

The data describe a meson with a single valence quark-antiquark pair. The neutral pion, the
superposition `(u ū - d d̄) / √2`, has no single valence pair and is not an instance; its net
valence numbers, which are what its parton densities see, all vanish.

Flavour-symmetry breaking is carried as separate data, `FlavorBreaking`: the light-quark mass
difference and the difference between the strange and the average light-quark mass. The isospin
and SU(3) limits are the propositions that one or both vanish, so that a flavour relation can be
stated as a conditional on its limit rather than as an approximate equality. For breaking data
built from quark masses, the limits are exactly the degeneracy of the corresponding masses
(`FlavorBreaking.isIsospinLimit_ofMasses_iff`, `FlavorBreaking.isSU3Limit_ofMasses_iff`).

## Main definitions

* `PseudoscalarMeson`: mass, decay constant, charge and valence flavours of a pseudoscalar meson.
* `PseudoscalarMeson.chargeConj`: the charge-conjugate meson.
* `PseudoscalarMeson.valenceNumber`: the net valence number of each flavour.
* `PseudoscalarMeson.IsChargeConsistent`: the charge is the valence quark charge minus the
  valence antiquark charge.
* `LightFlavor`: the up, down and strange flavours, with their charges `LightFlavor.charge`.
* `piPlus`, `piMinus`, `kPlus`, `kMinus`: the charged pions and kaons over `LightFlavor`.
* `FlavorBreaking`: the isospin- and SU(3)-breaking parameters, with the limits
  `FlavorBreaking.IsIsospinLimit` and `FlavorBreaking.IsSU3Limit`.

## Main results

* `PseudoscalarMeson.valenceNumber_eq_one_iff`, `valenceNumber_eq_neg_one_iff`: the net valence
  number is `+1` exactly on the valence quark flavour and `-1` exactly on the valence antiquark
  flavour of a flavoured meson.
* `PseudoscalarMeson.valenceNumber_inj`: a flavoured meson's net valence numbers determine its
  valence pair.
* `PseudoscalarMeson.sum_valenceNumber`: the net valence numbers sum to zero.
* `PseudoscalarMeson.IsChargeConsistent.sum_mul_valenceNumber`: the charge-weighted net valence
  numbers sum to the meson's charge.
* `kPlus_valenceAntiquark_ne_piPlus`: the positive pion and kaon share their valence quark and
  differ in their valence antiquark.
* `FlavorBreaking.isSU3Limit_ofMasses_iff`: the SU(3) limit is the degeneracy of the three
  light-quark masses.

## References

* S. Navas et al. (Particle Data Group), *Review of Particle Physics*, Phys. Rev. D 110 (2024)
  030001: the masses, and the decay constants in the review *Leptonic decays of charged
  pseudoscalar mesons*.
* G. P. Lepage and S. J. Brodsky, *Exclusive processes in perturbative quantum chromodynamics*,
  Phys. Rev. D 22 (1980) 2157, for the decay-constant convention.
-/

@[expose] public section

namespace EpsilonEridani.Particles.Meson

/-- A pseudoscalar meson as explicit data over a flavour type: its mass, its decay constant
`f_M` in the convention `⟨0| q̄ γ^μ γ₅ q |M(P)⟩ = i f_M P^μ`, its electric charge in units of the
positron charge, and the flavours of its valence quark and valence antiquark. -/
@[ext]
structure PseudoscalarMeson (Flavor : Type*) where
  /-- The meson mass. -/
  mass : ℝ
  /-- The decay constant, in the convention in which the charged-pion value is near `130 MeV`. -/
  decayConstant : ℝ
  /-- The electric charge in units of the positron charge. -/
  charge : ℝ
  /-- The flavour of the valence quark. -/
  valenceQuark : Flavor
  /-- The flavour of the valence antiquark. -/
  valenceAntiquark : Flavor
  /-- The mass is positive: the chiral limit is a limit of a family, not an instance. -/
  mass_pos : 0 < mass
  /-- The decay constant is positive. -/
  decayConstant_pos : 0 < decayConstant

namespace PseudoscalarMeson

variable {Flavor : Type*} (M : PseudoscalarMeson Flavor)

theorem mass_ne_zero : M.mass ≠ 0 := M.mass_pos.ne'

theorem decayConstant_ne_zero : M.decayConstant ≠ 0 := M.decayConstant_pos.ne'

/-! ### Charge conjugation -/

/-- The charge-conjugate meson: the same mass and decay constant, the opposite charge, and the
valence quark and antiquark flavours exchanged. -/
def chargeConj : PseudoscalarMeson Flavor where
  mass := M.mass
  decayConstant := M.decayConstant
  charge := -M.charge
  valenceQuark := M.valenceAntiquark
  valenceAntiquark := M.valenceQuark
  mass_pos := M.mass_pos
  decayConstant_pos := M.decayConstant_pos

@[simp]
theorem chargeConj_mass : M.chargeConj.mass = M.mass := (rfl)

@[simp]
theorem chargeConj_decayConstant : M.chargeConj.decayConstant = M.decayConstant := (rfl)

@[simp]
theorem chargeConj_charge : M.chargeConj.charge = -M.charge := (rfl)

@[simp]
theorem chargeConj_valenceQuark : M.chargeConj.valenceQuark = M.valenceAntiquark := (rfl)

@[simp]
theorem chargeConj_valenceAntiquark : M.chargeConj.valenceAntiquark = M.valenceQuark := (rfl)

@[simp]
theorem chargeConj_chargeConj : M.chargeConj.chargeConj = M := by
  ext <;> simp

theorem chargeConj_involutive :
    Function.Involutive (chargeConj : PseudoscalarMeson Flavor → PseudoscalarMeson Flavor) :=
  chargeConj_chargeConj

theorem chargeConj_injective :
    Function.Injective (chargeConj : PseudoscalarMeson Flavor → PseudoscalarMeson Flavor) :=
  chargeConj_involutive.injective

/-! ### Net valence numbers -/

section ValenceNumber

variable [DecidableEq Flavor]

/-- The net valence number of each flavour: the number of valence quarks of that flavour minus
the number of valence antiquarks of that flavour. -/
def valenceNumber : Flavor → ℤ :=
  Pi.single M.valenceQuark 1 - Pi.single M.valenceAntiquark 1

theorem valenceNumber_apply (a : Flavor) :
    M.valenceNumber a =
      (if a = M.valenceQuark then 1 else 0) - (if a = M.valenceAntiquark then 1 else 0) := by
  simp [valenceNumber, Pi.single_apply]

/-- The net valence numbers of a meson whose valence quark and antiquark have the same flavour
vanish, and only such a meson has vanishing net valence numbers. -/
theorem valenceNumber_eq_zero_iff :
    M.valenceNumber = 0 ↔ M.valenceQuark = M.valenceAntiquark := by
  refine ⟨fun h => ?_, fun h => by simp [valenceNumber, h]⟩
  by_contra hne
  have := congrFun h M.valenceQuark
  simp [valenceNumber_apply, hne] at this

/-- The net valence number is `+1` exactly on the valence quark flavour, and only when that
flavour differs from the valence antiquark flavour. -/
theorem valenceNumber_eq_one_iff (a : Flavor) :
    M.valenceNumber a = 1 ↔ a = M.valenceQuark ∧ a ≠ M.valenceAntiquark := by
  rw [valenceNumber_apply]
  split_ifs <;> simp_all

/-- The net valence number is `-1` exactly on the valence antiquark flavour, and only when that
flavour differs from the valence quark flavour. -/
theorem valenceNumber_eq_neg_one_iff (a : Flavor) :
    M.valenceNumber a = -1 ↔ a = M.valenceAntiquark ∧ a ≠ M.valenceQuark := by
  rw [valenceNumber_apply]
  split_ifs <;> simp_all

theorem valenceNumber_valenceQuark (h : M.valenceQuark ≠ M.valenceAntiquark) :
    M.valenceNumber M.valenceQuark = 1 :=
  (M.valenceNumber_eq_one_iff _).2 ⟨rfl, h⟩

theorem valenceNumber_valenceAntiquark (h : M.valenceQuark ≠ M.valenceAntiquark) :
    M.valenceNumber M.valenceAntiquark = -1 :=
  (M.valenceNumber_eq_neg_one_iff _).2 ⟨rfl, Ne.symm h⟩

/-- A flavour carried by neither the valence quark nor the valence antiquark has net valence
number zero. -/
theorem valenceNumber_eq_zero_of_ne {a : Flavor} (hq : a ≠ M.valenceQuark)
    (ha : a ≠ M.valenceAntiquark) : M.valenceNumber a = 0 := by
  simp [valenceNumber_apply, hq, ha]

@[simp]
theorem valenceNumber_chargeConj : M.chargeConj.valenceNumber = -M.valenceNumber := by
  simp [valenceNumber]

/-- **The net valence numbers determine the valence pair of a flavoured meson.** Two mesons with
the same net valence numbers, the first of which has distinct valence quark and antiquark
flavours, have the same valence quark and the same valence antiquark. -/
theorem valenceNumber_inj (M' : PseudoscalarMeson Flavor)
    (h : M.valenceQuark ≠ M.valenceAntiquark) :
    M.valenceNumber = M'.valenceNumber ↔
      M.valenceQuark = M'.valenceQuark ∧ M.valenceAntiquark = M'.valenceAntiquark := by
  refine ⟨fun hN => ⟨?_, ?_⟩, fun ⟨hq, ha⟩ => by simp [valenceNumber, hq, ha]⟩
  · have := M.valenceNumber_valenceQuark h
    rw [hN, valenceNumber_eq_one_iff] at this
    exact this.1
  · have := M.valenceNumber_valenceAntiquark h
    rw [hN, valenceNumber_eq_neg_one_iff] at this
    exact this.1

variable [Fintype Flavor]

/-- **The net valence numbers sum to zero**: a meson has as many valence quarks as valence
antiquarks. -/
theorem sum_valenceNumber : ∑ a, M.valenceNumber a = 0 := by
  simp [valenceNumber, Finset.sum_sub_distrib]

/-- The net valence numbers weighted by a flavour function `e` sum to the value of `e` on the
valence quark minus its value on the valence antiquark. -/
theorem sum_mul_valenceNumber {R : Type*} [CommRing R] (e : Flavor → R) :
    ∑ a, e a * M.valenceNumber a = e M.valenceQuark - e M.valenceAntiquark := by
  simp [valenceNumber_apply, mul_sub, Finset.sum_sub_distrib]

end ValenceNumber

/-! ### Charge consistency -/

/-- The charge of the meson is the charge carried by its valence pair: for quark charges `e` in
units of the positron charge, a valence quark of flavour `q` and a valence antiquark of flavour
`q'` carry `e q - e q'`. -/
def IsChargeConsistent (e : Flavor → ℝ) : Prop :=
  M.charge = e M.valenceQuark - e M.valenceAntiquark

theorem isChargeConsistent_iff (e : Flavor → ℝ) :
    M.IsChargeConsistent e ↔ M.charge = e M.valenceQuark - e M.valenceAntiquark := Iff.rfl

@[simp]
theorem isChargeConsistent_chargeConj_iff (e : Flavor → ℝ) :
    M.chargeConj.IsChargeConsistent e ↔ M.IsChargeConsistent e := by
  simp only [isChargeConsistent_iff, chargeConj_charge, chargeConj_valenceQuark,
    chargeConj_valenceAntiquark]
  constructor <;> intro h <;> linarith

/-- **Charge from the valence numbers.** For a charge-consistent meson, the net valence numbers
weighted by the quark charges sum to the meson's charge. -/
theorem IsChargeConsistent.sum_mul_valenceNumber [DecidableEq Flavor] [Fintype Flavor]
    {M : PseudoscalarMeson Flavor} {e : Flavor → ℝ} (h : M.IsChargeConsistent e) :
    ∑ a, e a * M.valenceNumber a = M.charge := by
  rw [M.sum_mul_valenceNumber, h]

end PseudoscalarMeson

/-! ### The light flavours and the charged pions and kaons -/

/-- The three light quark flavours: up, down and strange. -/
inductive LightFlavor where
  /-- The up quark. -/
  | u
  /-- The down quark. -/
  | d
  /-- The strange quark. -/
  | s
  deriving DecidableEq, Repr

namespace LightFlavor

instance : Fintype LightFlavor where
  elems := {u, d, s}
  complete x := by cases x <;> simp

/-- The electric charge of the quark of each light flavour, in units of the positron charge. -/
noncomputable def charge : LightFlavor → ℝ
  | u => 2 / 3
  | d => -1 / 3
  | s => -1 / 3

@[simp] theorem charge_u : charge u = 2 / 3 := (rfl)

@[simp] theorem charge_d : charge d = -1 / 3 := (rfl)

@[simp] theorem charge_s : charge s = -1 / 3 := (rfl)

end LightFlavor

open LightFlavor

/-- The positive pion `π⁺ = u d̄`, with the Particle Data Group mass and decay constant in MeV. -/
noncomputable def piPlus : PseudoscalarMeson LightFlavor where
  mass := 139.57039
  decayConstant := 130.2
  charge := 1
  valenceQuark := u
  valenceAntiquark := d
  mass_pos := by norm_num
  decayConstant_pos := by norm_num

/-- The positive kaon `K⁺ = u s̄`, with the Particle Data Group mass and decay constant in MeV. -/
noncomputable def kPlus : PseudoscalarMeson LightFlavor where
  mass := 493.677
  decayConstant := 155.7
  charge := 1
  valenceQuark := u
  valenceAntiquark := s
  mass_pos := by norm_num
  decayConstant_pos := by norm_num

/-- The negative pion `π⁻ = d ū`, the charge conjugate of the positive pion. -/
noncomputable def piMinus : PseudoscalarMeson LightFlavor := piPlus.chargeConj

/-- The negative kaon `K⁻ = s ū`, the charge conjugate of the positive kaon. -/
noncomputable def kMinus : PseudoscalarMeson LightFlavor := kPlus.chargeConj

@[simp] theorem piPlus_valenceQuark : piPlus.valenceQuark = u := (rfl)

@[simp] theorem piPlus_valenceAntiquark : piPlus.valenceAntiquark = d := (rfl)

@[simp] theorem piPlus_charge : piPlus.charge = 1 := (rfl)

@[simp] theorem kPlus_valenceQuark : kPlus.valenceQuark = u := (rfl)

@[simp] theorem kPlus_valenceAntiquark : kPlus.valenceAntiquark = s := (rfl)

@[simp] theorem kPlus_charge : kPlus.charge = 1 := (rfl)

theorem piMinus_eq_chargeConj : piMinus = piPlus.chargeConj := (rfl)

theorem kMinus_eq_chargeConj : kMinus = kPlus.chargeConj := (rfl)

theorem isChargeConsistent_piPlus : piPlus.IsChargeConsistent LightFlavor.charge := by
  rw [PseudoscalarMeson.isChargeConsistent_iff]
  norm_num

theorem isChargeConsistent_kPlus : kPlus.IsChargeConsistent LightFlavor.charge := by
  rw [PseudoscalarMeson.isChargeConsistent_iff]
  norm_num

theorem isChargeConsistent_piMinus : piMinus.IsChargeConsistent LightFlavor.charge := by
  rw [piMinus_eq_chargeConj, PseudoscalarMeson.isChargeConsistent_chargeConj_iff]
  exact isChargeConsistent_piPlus

theorem isChargeConsistent_kMinus : kMinus.IsChargeConsistent LightFlavor.charge := by
  rw [kMinus_eq_chargeConj, PseudoscalarMeson.isChargeConsistent_chargeConj_iff]
  exact isChargeConsistent_kPlus

/-- The positive pion and the positive kaon have the same valence quark. -/
theorem kPlus_valenceQuark_eq_piPlus : kPlus.valenceQuark = piPlus.valenceQuark := (rfl)

/-- **Disjoint valence antiquarks.** The positive kaon's valence antiquark is not the positive
pion's: the two mesons differ exactly in the antiquark, `s̄` against `d̄`. -/
theorem kPlus_valenceAntiquark_ne_piPlus :
    kPlus.valenceAntiquark ≠ piPlus.valenceAntiquark := by
  simp

/-- The positive pion and the positive kaon have different net valence numbers. -/
theorem kPlus_valenceNumber_ne_piPlus : kPlus.valenceNumber ≠ piPlus.valenceNumber := by
  rw [Ne, kPlus.valenceNumber_inj piPlus (by simp)]
  simp

/-! ### Flavour-symmetry breaking -/

/-- Flavour-symmetry breaking as data: the light-quark mass difference `m_d - m_u`, whose
vanishing is the isospin limit, and the difference `m_s - (m_u + m_d) / 2` between the strange
and the average light-quark mass, whose vanishing together with the first is the SU(3) limit.
Both are differences rather than ratios, so that each limit is the vanishing of a parameter. -/
@[ext]
structure FlavorBreaking where
  /-- The light-quark mass difference `m_d - m_u`. -/
  isospin : ℝ
  /-- The strange-minus-light mass difference `m_s - (m_u + m_d) / 2`. -/
  strange : ℝ

namespace FlavorBreaking

/-- The isospin limit: the light-quark mass difference vanishes. -/
def IsIsospinLimit (b : FlavorBreaking) : Prop := b.isospin = 0

/-- The SU(3) flavour limit: both the light-quark and the strange-minus-light mass differences
vanish. -/
def IsSU3Limit (b : FlavorBreaking) : Prop := b.isospin = 0 ∧ b.strange = 0

theorem isIsospinLimit_iff (b : FlavorBreaking) : b.IsIsospinLimit ↔ b.isospin = 0 := Iff.rfl

theorem isSU3Limit_iff (b : FlavorBreaking) :
    b.IsSU3Limit ↔ b.isospin = 0 ∧ b.strange = 0 := Iff.rfl

/-- The SU(3) limit contains the isospin limit. -/
theorem IsSU3Limit.isIsospinLimit {b : FlavorBreaking} (h : b.IsSU3Limit) : b.IsIsospinLimit :=
  h.1

/-- The breaking parameters of the light-quark masses `m_u`, `m_d`, `m_s`. -/
noncomputable def ofMasses (mu md ms : ℝ) : FlavorBreaking where
  isospin := md - mu
  strange := ms - (mu + md) / 2

@[simp]
theorem ofMasses_isospin (mu md ms : ℝ) : (ofMasses mu md ms).isospin = md - mu := (rfl)

@[simp]
theorem ofMasses_strange (mu md ms : ℝ) :
    (ofMasses mu md ms).strange = ms - (mu + md) / 2 := (rfl)

/-- The isospin limit of quark-mass breaking data is the degeneracy of the up and down masses. -/
theorem isIsospinLimit_ofMasses_iff (mu md ms : ℝ) :
    (ofMasses mu md ms).IsIsospinLimit ↔ mu = md := by
  rw [isIsospinLimit_iff, ofMasses_isospin, sub_eq_zero, eq_comm]

/-- The SU(3) limit of quark-mass breaking data is the degeneracy of all three light-quark
masses. -/
theorem isSU3Limit_ofMasses_iff (mu md ms : ℝ) :
    (ofMasses mu md ms).IsSU3Limit ↔ mu = md ∧ md = ms := by
  rw [isSU3Limit_iff, ofMasses_isospin, ofMasses_strange]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> linarith

/-- The isospin limit is strictly weaker than the SU(3) limit: degenerate up and down masses with
a heavier strange quark are in the first and not the second. -/
theorem exists_isIsospinLimit_not_isSU3Limit :
    ∃ b : FlavorBreaking, b.IsIsospinLimit ∧ ¬ b.IsSU3Limit :=
  ⟨ofMasses 0 0 1, by simp [isIsospinLimit_ofMasses_iff, isSU3Limit_ofMasses_iff]⟩

end FlavorBreaking

end EpsilonEridani.Particles.Meson
