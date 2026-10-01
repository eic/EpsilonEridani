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

All in the namespace `GenerationAssignments`:

* `isAnomalyFree_standardModel`: the Standard Model assignment cancels all four anomalies.
* `isAnomalyFree_iff_exists_eq_smul_standardModel_or_swapQuarkSinglets`:
  an assignment with `YQ ≠ 0` is anomaly-free if and only if it is a rescaling of the Standard
  Model assignment, up to swapping the two right-handed quark singlets. The hypothesis `YQ ≠ 0`
  is needed: `isAnomalyFree_mk_zero_neg` shows that the assignments `(0, t, -t, 0, 0)` are
  anomaly-free for every `t`, and they are not of this form.
* `isAnomalyFree_iff_exists_eq_smul_standardModel_or_swapQuarkSinglets_or_mk_zero_neg`:
  the anomaly-free assignments are exactly these rescalings together with the family
  `(0, t, -t, 0, 0)`.

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

/-- Left-handed multiplets contribute with sign `1`. -/
@[simp] theorem Chirality.sign_left : Chirality.left.sign = 1 := rfl

/-- Right-handed multiplets contribute with sign `-1`. -/
@[simp] theorem Chirality.sign_right : Chirality.right.sign = -1 := rfl

/-- An electroweak fermion multiplet, presented by its representation labels. It is the unit
from which the anomaly coefficients of a generation are summed. -/
structure Multiplet where
  /-- Dimension of the weak-isospin `SU(2)` representation (`2` for a doublet, `1` for a
  singlet). -/
  isospinDim : ℕ
  /-- Dimension of the colour `SU(3)` representation (`3` for quarks, `1` for leptons). -/
  colorDim : ℕ
  /-- Hypercharge, normalised so that `Q = T³ + Y/2`. -/
  Y : ℚ
  /-- Chirality. -/
  chirality : Chirality
  deriving DecidableEq, Repr

/-- A hypercharge assignment for the five multiplets of one generation, normalised so that
`Q = T³ + Y/2`. -/
@[ext]
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

/-- Rescaling all five hypercharges of an assignment by a common factor. -/
instance : SMul ℚ GenerationAssignments where
  smul q a := ⟨q * a.YQ, q * a.Yu, q * a.Yd, q * a.YL, q * a.Ye⟩

/-- The quark-doublet hypercharge of a rescaled assignment. -/
@[simp] theorem smul_YQ (q : ℚ) : (q • a).YQ = q * a.YQ := rfl

/-- The up-type singlet hypercharge of a rescaled assignment. -/
@[simp] theorem smul_Yu (q : ℚ) : (q • a).Yu = q * a.Yu := rfl

/-- The down-type singlet hypercharge of a rescaled assignment. -/
@[simp] theorem smul_Yd (q : ℚ) : (q • a).Yd = q * a.Yd := rfl

/-- The lepton-doublet hypercharge of a rescaled assignment. -/
@[simp] theorem smul_YL (q : ℚ) : (q • a).YL = q * a.YL := rfl

/-- The charged-lepton singlet hypercharge of a rescaled assignment. -/
@[simp] theorem smul_Ye (q : ℚ) : (q • a).Ye = q * a.Ye := rfl

/-- Rescaling of hypercharge assignments is an action of the multiplicative monoid `ℚ`. -/
instance : MulAction ℚ GenerationAssignments where
  one_smul a := by ext <;> simp
  mul_smul q r a := by ext <;> simp [mul_assoc]

/-- The assignment with the hypercharges of the two right-handed quark singlets exchanged. -/
@[simps]
def swapQuarkSinglets : GenerationAssignments := ⟨a.YQ, a.Yd, a.Yu, a.YL, a.Ye⟩

/-- The left-handed quark doublet with hypercharge `a.YQ`. -/
@[simps]
def quarkDoublet : Multiplet := ⟨2, 3, a.YQ, .left⟩

/-- The right-handed up-type quark singlet with hypercharge `a.Yu`. -/
@[simps]
def upSinglet : Multiplet := ⟨1, 3, a.Yu, .right⟩

/-- The right-handed down-type quark singlet with hypercharge `a.Yd`. -/
@[simps]
def downSinglet : Multiplet := ⟨1, 3, a.Yd, .right⟩

/-- The left-handed lepton doublet with hypercharge `a.YL`. -/
@[simps]
def leptonDoublet : Multiplet := ⟨2, 1, a.YL, .left⟩

/-- The right-handed charged-lepton singlet with hypercharge `a.Ye`. -/
@[simps]
def electronSinglet : Multiplet := ⟨1, 1, a.Ye, .right⟩

/-- The five multiplets of one generation carrying the hypercharges `a`. -/
def multiplets : List Multiplet :=
  [a.quarkDoublet, a.upSinglet, a.downSinglet, a.leptonDoublet, a.electronSinglet]

/-- The mixed gravitational anomaly coefficient: the chirality-signed sum of the hypercharges
over all states of the generation. -/
def gravitationalAnomaly : ℚ :=
  (a.multiplets.map fun m : Multiplet =>
    m.chirality.sign * (m.isospinDim : ℚ) * (m.colorDim : ℚ) * m.Y).sum

/-- The `SU(2)² × U(1)` anomaly coefficient: the chirality-signed, colour-weighted sum of the
hypercharges over the weak-isospin doublets, with the common Dynkin index `1/2` of the doublet
factored out. -/
def su2Anomaly : ℚ :=
  ((a.multiplets.filter (·.isospinDim = 2)).map fun m : Multiplet =>
    m.chirality.sign * (m.colorDim : ℚ) * m.Y).sum

/-- The `SU(3)² × U(1)` anomaly coefficient: the chirality-signed, isospin-weighted sum of the
hypercharges over the colour triplets, with the common Dynkin index `1/2` of the triplet
factored out. -/
def su3Anomaly : ℚ :=
  ((a.multiplets.filter (·.colorDim = 3)).map fun m : Multiplet =>
    m.chirality.sign * (m.isospinDim : ℚ) * m.Y).sum

/-- The `U(1)³` anomaly coefficient: the chirality-signed sum of the cubed hypercharges over all
states of the generation. -/
def cubicAnomaly : ℚ :=
  (a.multiplets.map fun m : Multiplet =>
    m.chirality.sign * (m.isospinDim : ℚ) * (m.colorDim : ℚ) * m.Y ^ 3).sum

/-- An assignment is anomaly-free if all four anomaly coefficients of the generation vanish. -/
def IsAnomalyFree : Prop :=
  a.gravitationalAnomaly = 0 ∧ a.su2Anomaly = 0 ∧ a.su3Anomaly = 0 ∧ a.cubicAnomaly = 0

/-- The gravitational anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem gravitationalAnomaly_eq :
    a.gravitationalAnomaly = 6 * a.YQ - 3 * a.Yu - 3 * a.Yd + 2 * a.YL - a.Ye := by
  simp only [gravitationalAnomaly, multiplets, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, quarkDoublet_isospinDim, quarkDoublet_colorDim, quarkDoublet_Y,
    quarkDoublet_chirality, upSinglet_isospinDim, upSinglet_colorDim, upSinglet_Y,
    upSinglet_chirality, downSinglet_isospinDim, downSinglet_colorDim, downSinglet_Y,
    downSinglet_chirality, leptonDoublet_isospinDim, leptonDoublet_colorDim, leptonDoublet_Y,
    leptonDoublet_chirality, electronSinglet_isospinDim, electronSinglet_colorDim,
    electronSinglet_Y, electronSinglet_chirality, Chirality.sign_left, Chirality.sign_right,
    Nat.cast_ofNat, Nat.cast_one]
  ring

/-- The `SU(2)² × U(1)` anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem su2Anomaly_eq : a.su2Anomaly = 3 * a.YQ + a.YL := by
  simp [su2Anomaly, multiplets]

/-- The `SU(3)² × U(1)` anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem su3Anomaly_eq : a.su3Anomaly = 2 * a.YQ - a.Yu - a.Yd := by
  simp only [su3Anomaly, multiplets, quarkDoublet_colorDim, upSinglet_colorDim,
    downSinglet_colorDim, leptonDoublet_colorDim, electronSinglet_colorDim, decide_true,
    decide_false, Bool.false_eq_true, List.filter_cons_of_pos, List.filter_cons_of_neg,
    OfNat.one_ne_ofNat, not_false_eq_true, List.filter_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, quarkDoublet_isospinDim, quarkDoublet_Y, quarkDoublet_chirality,
    upSinglet_isospinDim, upSinglet_Y, upSinglet_chirality, downSinglet_isospinDim, downSinglet_Y,
    downSinglet_chirality, Chirality.sign_left, Chirality.sign_right, Nat.cast_ofNat,
    Nat.cast_one]
  ring

/-- The `U(1)³` anomaly coefficient of a generation, written out in the hypercharges. -/
@[simp]
theorem cubicAnomaly_eq :
    a.cubicAnomaly = 6 * a.YQ ^ 3 - 3 * a.Yu ^ 3 - 3 * a.Yd ^ 3 + 2 * a.YL ^ 3 - a.Ye ^ 3 := by
  simp only [cubicAnomaly, multiplets, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    quarkDoublet_isospinDim, quarkDoublet_colorDim, quarkDoublet_Y, quarkDoublet_chirality,
    upSinglet_isospinDim, upSinglet_colorDim, upSinglet_Y, upSinglet_chirality,
    downSinglet_isospinDim, downSinglet_colorDim, downSinglet_Y, downSinglet_chirality,
    leptonDoublet_isospinDim, leptonDoublet_colorDim, leptonDoublet_Y, leptonDoublet_chirality,
    electronSinglet_isospinDim, electronSinglet_colorDim, electronSinglet_Y,
    electronSinglet_chirality, Chirality.sign_left, Chirality.sign_right, Nat.cast_ofNat,
    Nat.cast_one]
  ring

/-- Anomaly freedom as three linear equations and one cubic equation in the hypercharges. -/
theorem isAnomalyFree_iff :
    a.IsAnomalyFree ↔ 6 * a.YQ - 3 * a.Yu - 3 * a.Yd + 2 * a.YL - a.Ye = 0 ∧
      3 * a.YQ + a.YL = 0 ∧ 2 * a.YQ - a.Yu - a.Yd = 0 ∧
      6 * a.YQ ^ 3 - 3 * a.Yu ^ 3 - 3 * a.Yd ^ 3 + 2 * a.YL ^ 3 - a.Ye ^ 3 = 0 := by
  simp [IsAnomalyFree]

/-- The Standard Model hypercharge assignment `(1/3, 4/3, -2/3, -1, -2)` of one generation, in
the normalisation `Q = T³ + Y/2`. -/
@[simps]
def standardModel : GenerationAssignments := ⟨1 / 3, 4 / 3, -2 / 3, -1, -2⟩

/-- The Standard Model hypercharges cancel all four anomalies of a generation. -/
theorem isAnomalyFree_standardModel : standardModel.IsAnomalyFree := by
  rw [isAnomalyFree_iff]
  norm_num

variable {a} in
/-- Rescaling an anomaly-free assignment gives an anomaly-free assignment. -/
theorem IsAnomalyFree.smul (h : a.IsAnomalyFree) (q : ℚ) : (q • a).IsAnomalyFree := by
  obtain ⟨hgrav, hsu2, hsu3, hcub⟩ := (isAnomalyFree_iff a).mp h
  rw [isAnomalyFree_iff]
  simp only [smul_YQ, smul_Yu, smul_Yd, smul_YL, smul_Ye]
  exact ⟨by linear_combination q * hgrav, by linear_combination q * hsu2,
    by linear_combination q * hsu3, by linear_combination q ^ 3 * hcub⟩

variable {a} in
/-- Swapping the two right-handed quark singlets of an anomaly-free assignment gives an
anomaly-free assignment. -/
theorem IsAnomalyFree.swapQuarkSinglets (h : a.IsAnomalyFree) :
    a.swapQuarkSinglets.IsAnomalyFree := by
  obtain ⟨hgrav, hsu2, hsu3, hcub⟩ := (isAnomalyFree_iff a).mp h
  rw [isAnomalyFree_iff]
  simp only [swapQuarkSinglets_YQ, swapQuarkSinglets_Yu, swapQuarkSinglets_Yd,
    swapQuarkSinglets_YL, swapQuarkSinglets_Ye]
  exact ⟨by linear_combination hgrav, hsu2, by linear_combination hsu3,
    by linear_combination hcub⟩

/-- The assignments `(0, t, -t, 0, 0)` are anomaly-free for every `t`. -/
theorem isAnomalyFree_mk_zero_neg (t : ℚ) :
    (⟨0, t, -t, 0, 0⟩ : GenerationAssignments).IsAnomalyFree := by
  rw [isAnomalyFree_iff]
  exact ⟨by ring, by ring, by ring, by ring⟩

/-- An assignment with `YQ ≠ 0` is anomaly-free if and only if it is a rescaling of
`standardModel`, possibly with the two right-handed quark singlets swapped. The hypothesis
`YQ ≠ 0` excludes the anomaly-free family `isAnomalyFree_mk_zero_neg`, which is not of this
form; `isAnomalyFree_iff_exists_eq_smul_standardModel_or_swapQuarkSinglets_or_mk_zero_neg`
classifies all anomaly-free assignments. -/
theorem isAnomalyFree_iff_exists_eq_smul_standardModel_or_swapQuarkSinglets (hYQ : a.YQ ≠ 0) :
    a.IsAnomalyFree ↔
      ∃ q : ℚ, a = q • standardModel ∨ a = q • standardModel.swapQuarkSinglets := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨hgrav, hsu2, hsu3, hcub⟩ := (isAnomalyFree_iff a).mp h
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
    refine ⟨3 * a.YQ, ?_⟩
    rcases mul_eq_zero.mp hquad with hu | hu
    · left
      ext <;> simp only [smul_YQ, smul_Yu, smul_Yd, smul_YL, smul_Ye, standardModel_YQ,
        standardModel_Yu, standardModel_Yd, standardModel_YL, standardModel_Ye] <;> linarith
    · right
      ext <;> simp only [smul_YQ, smul_Yu, smul_Yd, smul_YL, smul_Ye, swapQuarkSinglets_YQ,
        swapQuarkSinglets_Yu, swapQuarkSinglets_Yd, swapQuarkSinglets_YL, swapQuarkSinglets_Ye,
        standardModel_YQ, standardModel_Yu, standardModel_Yd, standardModel_YL,
        standardModel_Ye] <;> linarith
  · rintro ⟨q, rfl | rfl⟩
    · exact isAnomalyFree_standardModel.smul q
    · exact isAnomalyFree_standardModel.swapQuarkSinglets.smul q

/-- The classification of anomaly-free assignments: an assignment is anomaly-free if and only if
it is a rescaling of `standardModel`, possibly with the two right-handed quark singlets swapped,
or it is of the form `(0, t, -t, 0, 0)`. -/
theorem isAnomalyFree_iff_exists_eq_smul_standardModel_or_swapQuarkSinglets_or_mk_zero_neg :
    a.IsAnomalyFree ↔
      (∃ q : ℚ, a = q • standardModel ∨ a = q • standardModel.swapQuarkSinglets) ∨
        ∃ t : ℚ, a = ⟨0, t, -t, 0, 0⟩ := by
  refine ⟨fun h => ?_, ?_⟩
  · rcases ne_or_eq a.YQ 0 with hYQ | hYQ
    · exact Or.inl
        ((isAnomalyFree_iff_exists_eq_smul_standardModel_or_swapQuarkSinglets a hYQ).mp h)
    -- At `YQ = 0` the three linear conditions force `YL = Ye = 0` and `Yd = -Yu`.
    obtain ⟨hgrav, hsu2, hsu3, -⟩ := (isAnomalyFree_iff a).mp h
    refine Or.inr ⟨a.Yu, ?_⟩
    ext
    · exact hYQ
    · rfl
    · linear_combination -hsu3 + 2 * hYQ
    · linear_combination hsu2 - 3 * hYQ
    · linear_combination -hgrav + 2 * hsu2 + 3 * hsu3 - 6 * hYQ
  · rintro (⟨q, rfl | rfl⟩ | ⟨t, rfl⟩)
    · exact isAnomalyFree_standardModel.smul q
    · exact isAnomalyFree_standardModel.swapQuarkSinglets.smul q
    · exact isAnomalyFree_mk_zero_neg t

/-- The one-family Standard Model charge vector in Physlib's anomaly cancellation system
`SMCharges 1`, which records the charges of left-handed Weyl fermions: the right-handed singlets
enter through their conjugates, with hypercharges `-Yu`, `-Yd` and `-Ye`. -/
def toSMCharges : (SMCharges 1).Charges :=
  SMCharges.toSpeciesEquiv.symm fun i _ => ![a.YQ, -a.Yu, -a.Yd, a.YL, -a.Ye] i

/-- The species components of `toSMCharges`. -/
@[simp]
theorem toSpecies_toSMCharges (i : Fin 5) :
    SMCharges.toSpecies i a.toSMCharges = fun _ => ![a.YQ, -a.Yu, -a.Yd, a.YL, -a.Ye] i :=
  SMCharges.toSMSpecies_toSpecies_inv i _

/-- Physlib's gravitational anomaly condition on `toSMCharges` is `gravitationalAnomaly`. -/
@[simp]
theorem accGrav_toSMCharges : SMACCs.accGrav a.toSMCharges = a.gravitationalAnomaly := by
  simp only [SMACCs.accGrav, LinearMap.coe_mk, AddHom.coe_mk, toSpecies_toSMCharges,
    SMCharges.sum_SMSpecies_numberCharges_one, gravitationalAnomaly_eq, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_neg]
  ring

/-- Physlib's `SU(2)` anomaly condition on `toSMCharges` is `su2Anomaly`. -/
@[simp]
theorem accSU2_toSMCharges : SMACCs.accSU2 a.toSMCharges = a.su2Anomaly := by
  simp only [SMACCs.accSU2, LinearMap.coe_mk, AddHom.coe_mk, toSpecies_toSMCharges,
    SMCharges.sum_SMSpecies_numberCharges_one, su2Anomaly_eq, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val]

/-- Physlib's `SU(3)` anomaly condition on `toSMCharges` is `su3Anomaly`. -/
@[simp]
theorem accSU3_toSMCharges : SMACCs.accSU3 a.toSMCharges = a.su3Anomaly := by
  simp only [SMACCs.accSU3, LinearMap.coe_mk, AddHom.coe_mk, toSpecies_toSMCharges,
    SMCharges.sum_SMSpecies_numberCharges_one, su3Anomaly_eq, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Physlib's cubic anomaly condition on `toSMCharges` is `cubicAnomaly`. -/
theorem accCube_toSMCharges : SMACCs.accCube a.toSMCharges = a.cubicAnomaly := by
  -- `TriLinearSymm.toCubic_apply` does not rewrite `accCube a.toSMCharges`: the function
  -- coercion of `HomogeneousCubic` in the goal does not match the lemma's syntactically. The
  -- two agree by unfolding `accCube` and `TriLinearSymm.toCubic`, so `change` exposes the
  -- trilinear form directly.
  change SMACCs.cubeTriLin a.toSMCharges a.toSMCharges a.toSMCharges = _
  rw [SMACCs.cubeTriLin, TriLinearSymm.mk₃_toFun_apply_apply,
    SMCharges.sum_SMSpecies_numberCharges_one]
  simp only [toSpecies_toSMCharges, cubicAnomaly_eq, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val]
  ring

/-- Anomaly freedom is the vanishing of Physlib's four one-family anomaly cancellation
conditions on `toSMCharges`. -/
theorem isAnomalyFree_iff_smaccs :
    a.IsAnomalyFree ↔ SMACCs.accGrav a.toSMCharges = 0 ∧ SMACCs.accSU2 a.toSMCharges = 0 ∧
      SMACCs.accSU3 a.toSMCharges = 0 ∧ SMACCs.accCube a.toSMCharges = 0 := by
  rw [accGrav_toSMCharges, accSU2_toSMCharges, accSU3_toSMCharges, accCube_toSMCharges,
    IsAnomalyFree]

end GenerationAssignments

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

end
