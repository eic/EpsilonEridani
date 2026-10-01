/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Physlib.Particles.StandardModel.AnomalyCancellation.Basic

/-!
# Representation Content of One Generation

This module defines the electroweak representation content of one fermion generation: a
left-handed quark doublet, two right-handed quark singlets, a left-handed lepton doublet, and a
right-handed charged-lepton singlet. Each is a `Multiplet` recording its weak-isospin and colour
representation dimensions, its hypercharge, and its chirality. A `GenerationAssignments` is a
choice of hypercharge for each of the five, and `GenerationAssignments.multiplets` turns it into
the five multiplets of one generation.

Hypercharges are normalised so that `Q = T³ + Y/2`, with the left-handed lepton doublet carrying
`Y = -1`; in this normalisation the Standard Model assignment is
`(YQ, Yu, Yd, YL, Ye) = (1/3, 4/3, -2/3, -1, -2)`.

The four anomaly coefficients of a generation (gravitational, `SU(2)² × U(1)`,
`SU(3)² × U(1)` and `U(1)³`) are defined as chirality-signed sums over the multiplets, weighted
by the appropriate representation dimensions; `toSMCharges` identifies each with the
corresponding one-family anomaly cancellation condition of Physlib's Standard Model ACC system.

## Main results

* `GenerationAssignments.isAnomalyFree_standardModel`: the Standard Model assignment cancels all
  four anomalies.
* `GenerationAssignments.exists_hypercharges_eq_of_isAnomalyFree`: every anomaly-free assignment
  with `YQ ≠ 0` is a rescaling of the Standard Model assignment, up to swapping the two
  right-handed quark singlets. The hypothesis `YQ ≠ 0` is needed: the assignments
  `(0, t, -t, 0, 0)` are anomaly-free for every `t` and are not of this form.

## References

* C. Q. Geng and R. E. Marshak, *Uniqueness of quark and lepton representations in the
  standard model from the anomalies viewpoint*, Phys. Rev. D 39 (1989) 693.
* J. A. Minahan, P. Ramond and R. C. Warner, *Comment on anomaly cancellation in the standard
  model*, Phys. Rev. D 41 (1990) 715.
* Particle Data Group, *Electroweak model and constraints on new physics*, for the hypercharge
  normalisation `Q = T³ + Y/2`.
-/

@[expose] public section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

/-- The chirality of a Weyl fermion multiplet. -/
inductive Chirality where
  /-- Left-handed. -/
  | left
  /-- Right-handed. -/
  | right
  deriving DecidableEq, Repr

/-- The sign with which a multiplet of the given chirality contributes to an anomaly
coefficient: `1` for left-handed and `-1` for right-handed fields. -/
def Chirality.sign : Chirality → ℚ
  | .left => 1
  | .right => -1

/-- An electroweak fermion multiplet, presented by its representation labels. It is the unit
from which the anomaly coefficients of a generation are summed. -/
structure Multiplet where
  /-- Dimension of the weak-isospin `SU(2)` representation (`2` for a doublet, `1` for a
  singlet). -/
  isospinDim : ℕ
  /-- Dimension of the colour `SU(3)` representation (`3` for quarks, `1` for leptons). -/
  colourDim : ℕ
  /-- Hypercharge, normalised so that `Q = T³ + Y/2`. -/
  Y : ℚ
  /-- Chirality. -/
  chirality : Chirality
  deriving DecidableEq, Repr

/-- A hypercharge assignment for the five multiplets of one generation, normalised so that
`Q = T³ + Y/2`. -/
structure GenerationAssignments where
  /-- Hypercharge of the left-handed quark doublet. -/
  YQ : ℚ
  /-- Hypercharge of the right-handed up-type quark singlet. -/
  Yu : ℚ
  /-- Hypercharge of the right-handed down-type quark singlet. -/
  Yd : ℚ
  /-- Hypercharge of the left-handed lepton doublet. -/
  YL : ℚ
  /-- Hypercharge of the right-handed charged-lepton singlet. -/
  Ye : ℚ

namespace GenerationAssignments

variable (a : GenerationAssignments)

/-- The left-handed quark doublet with hypercharge `a.YQ`. -/
def quarkDoublet : Multiplet := ⟨2, 3, a.YQ, .left⟩

/-- The right-handed up-type quark singlet with hypercharge `a.Yu`. -/
def upSinglet : Multiplet := ⟨1, 3, a.Yu, .right⟩

/-- The right-handed down-type quark singlet with hypercharge `a.Yd`. -/
def downSinglet : Multiplet := ⟨1, 3, a.Yd, .right⟩

/-- The left-handed lepton doublet with hypercharge `a.YL`. -/
def leptonDoublet : Multiplet := ⟨2, 1, a.YL, .left⟩

/-- The right-handed charged-lepton singlet with hypercharge `a.Ye`. -/
def electronSinglet : Multiplet := ⟨1, 1, a.Ye, .right⟩

/-- The five multiplets of one generation carrying the hypercharges `a`. -/
def multiplets : List Multiplet :=
  [a.quarkDoublet, a.upSinglet, a.downSinglet, a.leptonDoublet, a.electronSinglet]

/-- The mixed gravitational anomaly coefficient: the chirality-signed sum of the hypercharges
over all states of the generation. -/
def gravitationalAnomaly : ℚ :=
  (a.multiplets.map fun m : Multiplet =>
    m.chirality.sign * (m.isospinDim : ℚ) * (m.colourDim : ℚ) * m.Y).sum

/-- The `SU(2)² × U(1)` anomaly coefficient: the chirality-signed, colour-weighted sum of the
hypercharges over the weak-isospin doublets, with the common Dynkin index `1/2` of the doublet
factored out. -/
def su2Anomaly : ℚ :=
  ((a.multiplets.filter (·.isospinDim = 2)).map fun m : Multiplet =>
    m.chirality.sign * (m.colourDim : ℚ) * m.Y).sum

/-- The `SU(3)² × U(1)` anomaly coefficient: the chirality-signed, isospin-weighted sum of the
hypercharges over the colour triplets, with the common Dynkin index `1/2` of the triplet
factored out. -/
def su3Anomaly : ℚ :=
  ((a.multiplets.filter (·.colourDim = 3)).map fun m : Multiplet =>
    m.chirality.sign * (m.isospinDim : ℚ) * m.Y).sum

/-- The `U(1)³` anomaly coefficient: the chirality-signed sum of the cubed hypercharges over all
states of the generation. -/
def cubicAnomaly : ℚ :=
  (a.multiplets.map fun m : Multiplet =>
    m.chirality.sign * (m.isospinDim : ℚ) * (m.colourDim : ℚ) * m.Y ^ 3).sum

/-- An assignment is anomaly-free if all four anomaly coefficients of the generation vanish. -/
def IsAnomalyFree : Prop :=
  a.gravitationalAnomaly = 0 ∧ a.su2Anomaly = 0 ∧ a.su3Anomaly = 0 ∧ a.cubicAnomaly = 0

/-- The gravitational anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem gravitationalAnomaly_eq :
    a.gravitationalAnomaly = 6 * a.YQ - 3 * a.Yu - 3 * a.Yd + 2 * a.YL - a.Ye := by
  simp [gravitationalAnomaly, multiplets, quarkDoublet, upSinglet, downSinglet, leptonDoublet,
    electronSinglet, Chirality.sign]
  ring

/-- The `SU(2)² × U(1)` anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem su2Anomaly_eq : a.su2Anomaly = 3 * a.YQ + a.YL := by
  simp [su2Anomaly, multiplets, quarkDoublet, upSinglet, downSinglet, leptonDoublet,
    electronSinglet, Chirality.sign]

/-- The `SU(3)² × U(1)` anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem su3Anomaly_eq : a.su3Anomaly = 2 * a.YQ - a.Yu - a.Yd := by
  simp [su3Anomaly, multiplets, quarkDoublet, upSinglet, downSinglet, leptonDoublet,
    electronSinglet, Chirality.sign]
  ring

/-- The `U(1)³` anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem cubicAnomaly_eq :
    a.cubicAnomaly = 6 * a.YQ ^ 3 - 3 * a.Yu ^ 3 - 3 * a.Yd ^ 3 + 2 * a.YL ^ 3 - a.Ye ^ 3 := by
  simp [cubicAnomaly, multiplets, quarkDoublet, upSinglet, downSinglet, leptonDoublet,
    electronSinglet, Chirality.sign]
  ring

/-- Anomaly freedom as three linear equations and one cubic equation in the hypercharges. -/
theorem isAnomalyFree_iff :
    a.IsAnomalyFree ↔ 6 * a.YQ - 3 * a.Yu - 3 * a.Yd + 2 * a.YL - a.Ye = 0 ∧
      3 * a.YQ + a.YL = 0 ∧ 2 * a.YQ - a.Yu - a.Yd = 0 ∧
      6 * a.YQ ^ 3 - 3 * a.Yu ^ 3 - 3 * a.Yd ^ 3 + 2 * a.YL ^ 3 - a.Ye ^ 3 = 0 := by
  simp [IsAnomalyFree]

/-- The Standard Model hypercharge assignment `(1/3, 4/3, -2/3, -1, -2)` of one generation, in
the normalisation `Q = T³ + Y/2`. -/
def standardModel : GenerationAssignments := ⟨1 / 3, 4 / 3, -2 / 3, -1, -2⟩

/-- The Standard Model hypercharges cancel all four anomalies of a generation. -/
theorem isAnomalyFree_standardModel : standardModel.IsAnomalyFree := by
  rw [isAnomalyFree_iff]
  norm_num [standardModel]

/-- Every anomaly-free assignment with `YQ ≠ 0` is a rescaling of the Standard Model assignment
`(1/3, 4/3, -2/3, -1, -2)`, up to swapping the two right-handed quark singlets. The hypothesis
`YQ ≠ 0` excludes the anomaly-free family `(0, t, -t, 0, 0)`, which is not of this form. -/
theorem exists_hypercharges_eq_of_isAnomalyFree (hYQ : a.YQ ≠ 0) (h : a.IsAnomalyFree) :
    ∃ q : ℚ,
      a.YQ = (1/3) * q ∧
      a.YL = -1 * q ∧
      a.Ye = -2 * q ∧
      ((a.Yu = (4/3) * q ∧ a.Yd = -(2/3) * q) ∨
       (a.Yu = -(2/3) * q ∧ a.Yd = (4/3) * q)) := by
  obtain ⟨hgrav, hsu2, hsu3, hcub⟩ := (isAnomalyFree_iff a).mp h
  -- The three linear conditions fix `YL`, `Yd` and `Ye` in terms of `YQ` and `Yu`.
  have hYL : a.YL = -3 * a.YQ := by linear_combination hsu2
  have hYd : a.Yd = 2 * a.YQ - a.Yu := by linear_combination -hsu3
  have hYe : a.Ye = -6 * a.YQ := by linear_combination -hgrav + 2 * hsu2 + 3 * hsu3
  -- Substituting into the cubic condition leaves a quadratic in `Yu` with roots `4YQ`, `-2YQ`.
  have hquad : (a.Yu - 4 * a.YQ) * (a.Yu + 2 * a.YQ) = 0 := by
    have h18 : (18 * a.YQ) * ((a.Yu - 4 * a.YQ) * (a.Yu + 2 * a.YQ)) = 0 := by
      rw [hYL, hYd, hYe] at hcub
      linear_combination -hcub
    exact (mul_eq_zero.mp h18).resolve_left (mul_ne_zero (by norm_num) hYQ)
  refine ⟨3 * a.YQ, by ring, by linear_combination hYL, by linear_combination hYe, ?_⟩
  rcases mul_eq_zero.mp hquad with hu | hu
  · exact Or.inl ⟨by linear_combination hu, by linear_combination hYd - hu⟩
  · exact Or.inr ⟨by linear_combination hu, by linear_combination hYd - hu⟩

/-- The one-family Standard Model charge vector in Physlib's anomaly cancellation system
`SMCharges 1`, which records the charges of left-handed Weyl fermions: the right-handed singlets
enter through their conjugates, with hypercharges `-Yu`, `-Yd` and `-Ye`. -/
def toSMCharges : (SMCharges 1).Charges :=
  SMCharges.toSpeciesEquiv.symm fun i _ => ![a.YQ, -a.Yu, -a.Yd, a.YL, -a.Ye] i

/-- The species components of `toSMCharges`. -/
@[simp]
theorem toSpecies_toSMCharges (i : Fin 5) (j : Fin (SMSpecies 1).numberCharges) :
    SMCharges.toSpecies i a.toSMCharges j = ![a.YQ, -a.Yu, -a.Yd, a.YL, -a.Ye] i := by
  exact congrFun (SMCharges.toSMSpecies_toSpecies_inv i _) j

/-- Physlib's gravitational anomaly condition on `toSMCharges` is `gravitationalAnomaly`. -/
theorem accGrav_toSMCharges : SMACCs.accGrav a.toSMCharges = a.gravitationalAnomaly := by
  simp only [SMACCs.accGrav, LinearMap.coe_mk, AddHom.coe_mk, toSpecies_toSMCharges,
    SMCharges.sum_SMSpecies_numberCharges_one, gravitationalAnomaly_eq]
  simp
  ring

/-- Physlib's `SU(2)` anomaly condition on `toSMCharges` is `su2Anomaly`. -/
theorem accSU2_toSMCharges : SMACCs.accSU2 a.toSMCharges = a.su2Anomaly := by
  simp only [SMACCs.accSU2, LinearMap.coe_mk, AddHom.coe_mk, toSpecies_toSMCharges,
    SMCharges.sum_SMSpecies_numberCharges_one, su2Anomaly_eq]
  simp

/-- Physlib's `SU(3)` anomaly condition on `toSMCharges` is `su3Anomaly`. -/
theorem accSU3_toSMCharges : SMACCs.accSU3 a.toSMCharges = a.su3Anomaly := by
  simp only [SMACCs.accSU3, LinearMap.coe_mk, AddHom.coe_mk, toSpecies_toSMCharges,
    SMCharges.sum_SMSpecies_numberCharges_one, su3Anomaly_eq]
  simp
  ring

/-- Physlib's cubic anomaly condition on `toSMCharges` is `cubicAnomaly`. -/
theorem accCube_toSMCharges : SMACCs.accCube a.toSMCharges = a.cubicAnomaly := by
  change SMACCs.cubeTriLin a.toSMCharges a.toSMCharges a.toSMCharges = _
  rw [SMACCs.cubeTriLin, TriLinearSymm.mk₃_toFun_apply_apply,
    SMCharges.sum_SMSpecies_numberCharges_one]
  simp only [toSpecies_toSMCharges, cubicAnomaly_eq]
  simp
  ring

end GenerationAssignments

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

end
