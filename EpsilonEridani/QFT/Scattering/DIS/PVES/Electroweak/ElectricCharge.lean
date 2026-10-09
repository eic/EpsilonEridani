/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LieAlgebra.SpecialUnitaryExtensions
public import EpsilonEridani.Particles.StandardModel.HiggsBoson.BasicExtensions
public import EpsilonEridani.QFT.QCD.SU2Generators
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Physlib.Relativity.PauliMatrices.Basic

/-!
# Electric charge as the unbroken generator

The electroweak gauge algebra is `𝔰𝔲(2) ⊕ 𝔲(1)`. We write its elements as pairs `(A, β)` with
`A ∈ 𝔰𝔲(2)` a skew-Hermitian traceless `2 × 2` matrix and `β : ℝ` the hypercharge parameter. On
a weak-isospin doublet of hypercharge `y` the pair acts by `A + i β (y / 2)`, and on a singlet of
hypercharge `y` by `i β (y / 2)`. The Hermitian generators are `T³ = σ³ / 2` and `Y / 2`, with
hypercharges normalised so that the Higgs doublet has `Y = 1` and the left-handed lepton doublet
has `Y = -1`.

The Higgs vacuum `(0, v)` with `v ≠ 0` lies in the lower, `T³ = -1/2`, component of the Higgs
doublet. The generators that annihilate it form the line through
`electricChargeGenerator = (i T³, 1)`. This is the unique unbroken direction, and it lies in the
Cartan subalgebra of diagonal generators. It acts on a doublet of hypercharge `y` as `i` times
the electric charge operator `electricChargeOperator y = T³ + y / 2`, and on a singlet as
`i (y / 2)`. So for the doublets and singlets treated here the electric charge of a state with
weak-isospin third component `T³` and hypercharge `Y` is `Q = T³ + Y / 2`.

## Main results

* `doubletStabilizer_higgsVacuum`: the generators annihilating the Higgs vacuum are the real
  multiples of `electricChargeGenerator`. `finrank_doubletStabilizer_higgsVacuum` says there is
  exactly one.
* `doubletAction_electricChargeGenerator`: on a doublet of hypercharge `y` the unbroken
  generator acts as `i` times `electricChargeOperator y = T³ + y / 2`.
  `isospinT3_mulVec_single` gives the weights `isospinWeight k = ±1/2` of `T³` on the two
  components, `electricChargeOperator_mulVec_single` the charges
  `doubletElectricCharge y k = ±1/2 + y / 2`, and
  `doubletAction_electricChargeGenerator_mulVec_single` combines the two.
  `singletAction_electricChargeGenerator` is the singlet version, with charge
  `singletElectricCharge y = y / 2`.

## References

* S. Weinberg, *A model of leptons*, Phys. Rev. Lett. 19 (1967) 1264.
* Particle Data Group, *Electroweak model and constraints on new physics*, for the normalisation
  `Q = T³ + Y/2`.
-/

public section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

open Complex Matrix PauliMatrix
open EpsilonEridani.LieAlgebra.SpecialUnitary EpsilonEridani.Particles.StandardModel.HiggsBoson
open EpsilonEridani.QFT.QCD.RepresentationColor

/-- The weak-isospin weights of a doublet: the `T³` eigenvalue `1/2` of the upper component and
`-1/2` of the lower one. -/
noncomputable def isospinWeight : Fin 2 → ℝ := ![1 / 2, -1 / 2]

/-- The upper component of a doublet has weak isospin `1/2`. -/
@[simp]
theorem isospinWeight_zero : isospinWeight 0 = 1 / 2 :=
  (rfl)

/-- The lower component of a doublet has weak isospin `-1/2`. -/
@[simp]
theorem isospinWeight_one : isospinWeight 1 = -1 / 2 :=
  (rfl)

/-- The weak-isospin generator `T³ = σ³ / 2` on a doublet. Its eigenvalues are the weights
`isospinWeight`. -/
noncomputable def isospinT3 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • σ3

/-- `T³` is `σ³ / 2`. -/
theorem isospinT3_def : isospinT3 = (1 / 2 : ℂ) • σ3 :=
  (rfl)

/-- `T³` is the third fundamental `su(2)` generator `σ³ / 2` of `su2GenEntry`. -/
theorem isospinT3_apply_eq_su2GenEntry (i j : Fin 2) : isospinT3 i j = su2GenEntry 2 i j := by
  rw [isospinT3_def, Matrix.smul_apply, smul_eq_mul, su2GenEntry]

/-- `T³` is diagonal, with the weights `isospinWeight` on the diagonal. -/
theorem isospinT3_eq_diagonal : isospinT3 = diagonal fun k => (isospinWeight k : ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [isospinT3, pauliMatrix, isospinWeight]

/-- The action of `(A, β) ∈ 𝔰𝔲(2) ⊕ 𝔲(1)` on a weak-isospin singlet of hypercharge `y`: the
`𝔰𝔲(2)` component acts trivially and the hypercharge acts by `i β (y / 2)`. -/
noncomputable def singletAction (y : ℝ) : su (Fin 2) × ℝ →ₗ[ℝ] ℂ where
  toFun x := I * (x.2 * (y / 2 : ℝ) : ℂ)
  map_add' x x' := by simp only [Prod.snd_add, ofReal_add, add_mul, mul_add]
  map_smul' c x := by
    simp only [Prod.smul_snd, smul_eq_mul, ofReal_mul, RingHom.id_apply, Complex.real_smul]
    ring

/-- The singlet action unfolded. -/
theorem singletAction_apply (y : ℝ) (x : su (Fin 2) × ℝ) :
    singletAction y x = I * (x.2 * (y / 2 : ℝ) : ℂ) :=
  (rfl)

/-- The action of `(A, β) ∈ 𝔰𝔲(2) ⊕ 𝔲(1)` on a weak-isospin doublet of hypercharge `y`:
the matrix `A + i β (y / 2)`, whose hypercharge part is the singlet action. -/
noncomputable def doubletAction (y : ℝ) : su (Fin 2) × ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun x := (x.1 : Matrix (Fin 2) (Fin 2) ℂ) + singletAction y x • 1
  map_add' x x' := by
    rw [Prod.fst_add, AddMemClass.coe_add, map_add, add_smul]
    abel
  map_smul' c x := by
    rw [Prod.smul_fst, SetLike.val_smul, map_smul, RingHom.id_apply, smul_add, smul_assoc]

/-- The doublet action unfolded. -/
theorem doubletAction_apply (y : ℝ) (x : su (Fin 2) × ℝ) :
    doubletAction y x = (x.1 : Matrix (Fin 2) (Fin 2) ℂ) + singletAction y x • 1 :=
  (rfl)

/-- The stabilizer of a vector `φ` in a doublet of hypercharge `y`: the generators of
`𝔰𝔲(2) ⊕ 𝔲(1)` whose doublet action annihilates `φ`. These are the directions of the gauge
algebra left unbroken when `φ` is the vacuum. -/
noncomputable def doubletStabilizer (y : ℝ) (φ : Fin 2 → ℂ) : Submodule ℝ (su (Fin 2) × ℝ) :=
  LinearMap.ker (((mulVecBilin ℝ ℂ).flip φ).comp (doubletAction y))

/-- Membership in the stabilizer is the vanishing of the doublet action on `φ`. -/
@[simp]
theorem mem_doubletStabilizer_iff (y : ℝ) (φ : Fin 2 → ℂ) (x : su (Fin 2) × ℝ) :
    x ∈ doubletStabilizer y φ ↔ doubletAction y x *ᵥ φ = 0 := by
  rw [doubletStabilizer, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.flip_apply,
    mulVecBilin_apply]

/-- `T³` is Hermitian. -/
theorem isHermitian_isospinT3 : isospinT3.IsHermitian := by
  rw [isospinT3_eq_diagonal, isHermitian_diagonal_iff]
  exact fun k => Complex.conj_ofReal _

/-- `T³` is traceless. -/
theorem trace_isospinT3 : trace isospinT3 = 0 := by
  rw [isospinT3_def, trace_smul, trace_σ3, smul_zero]

/-- `i T³` is skew-Hermitian and traceless, so it lies in `𝔰𝔲(2)`. -/
theorem I_smul_isospinT3_mem_su : I • isospinT3 ∈ su (Fin 2) :=
  I_smul_mem_su isHermitian_isospinT3 trace_isospinT3

/-- The electric-charge generator `(i T³, 1) ∈ 𝔰𝔲(2) ⊕ 𝔲(1)`, whose associated Hermitian
generator, `-i` times its doublet action, is `T³ + Y / 2`. -/
noncomputable def electricChargeGenerator : su (Fin 2) × ℝ :=
  (⟨I • isospinT3, I_smul_isospinT3_mem_su⟩, 1)

/-- The `𝔰𝔲(2)` component of the electric charge generator is `i T³`. -/
@[simp]
theorem coe_electricChargeGenerator_fst :
    (electricChargeGenerator.1 : Matrix (Fin 2) (Fin 2) ℂ) = I • isospinT3 :=
  (rfl)

/-- The hypercharge component of the electric charge generator is `1`. -/
@[simp]
theorem electricChargeGenerator_snd : electricChargeGenerator.2 = 1 :=
  (rfl)

/-- The electric charge generator lies in the Cartan subalgebra: its `𝔰𝔲(2)` component is
diagonal. -/
theorem isDiag_electricChargeGenerator_fst :
    Matrix.IsDiag (electricChargeGenerator.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [coe_electricChargeGenerator_fst, isospinT3_eq_diagonal]
  exact (isDiag_diagonal _).smul I

/-- The electric charge generator is nonzero. -/
theorem electricChargeGenerator_ne_zero : electricChargeGenerator ≠ 0 := by
  intro h
  simpa using congrArg Prod.snd h

/-- The electric charge `T³ₖ + y / 2` of the `k`-th component of a doublet of hypercharge `y`. -/
noncomputable def doubletElectricCharge (y : ℝ) (k : Fin 2) : ℝ := isospinWeight k + y / 2

/-- The doublet electric charge unfolded. -/
theorem doubletElectricCharge_apply (y : ℝ) (k : Fin 2) :
    doubletElectricCharge y k = isospinWeight k + y / 2 :=
  (rfl)

/-- The electric charge `y / 2` of a weak-isospin singlet of hypercharge `y`. -/
noncomputable def singletElectricCharge (y : ℝ) : ℝ := y / 2

/-- The singlet electric charge unfolded. -/
theorem singletElectricCharge_def (y : ℝ) : singletElectricCharge y = y / 2 :=
  (rfl)

/-- The electric-charge operator `Q = T³ + y / 2` on a weak-isospin doublet of hypercharge `y`. -/
noncomputable def electricChargeOperator (y : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  isospinT3 + ((y / 2 : ℝ) : ℂ) • 1

/-- The electric charge operator unfolded. -/
theorem electricChargeOperator_def (y : ℝ) :
    electricChargeOperator y = isospinT3 + ((y / 2 : ℝ) : ℂ) • 1 :=
  (rfl)

/-- The electric charge operator is diagonal, with the charges `doubletElectricCharge y` on the
diagonal. -/
theorem electricChargeOperator_eq_diagonal (y : ℝ) :
    electricChargeOperator y = diagonal fun k => (doubletElectricCharge y k : ℂ) := by
  rw [electricChargeOperator_def, isospinT3_eq_diagonal,
    ← diagonal_one, ← diagonal_smul, diagonal_add]
  congr 1
  funext k
  simp [doubletElectricCharge_apply]

/-- The charge operator is Hermitian. -/
theorem isHermitian_electricChargeOperator (y : ℝ) : (electricChargeOperator y).IsHermitian := by
  rw [electricChargeOperator_eq_diagonal, isHermitian_diagonal_iff]
  exact fun k => Complex.conj_ofReal _

/-- The charge operator is diagonal. -/
theorem isDiag_electricChargeOperator (y : ℝ) : (electricChargeOperator y).IsDiag := by
  rw [electricChargeOperator_eq_diagonal]
  exact isDiag_diagonal _

/-- **The charge is `T³ + Y/2`.** On a doublet of hypercharge `y` the unbroken generator acts as
`i` times the charge operator `T³ + y / 2`. -/
@[simp]
theorem doubletAction_electricChargeGenerator (y : ℝ) :
    doubletAction y electricChargeGenerator =
      I • electricChargeOperator y := by
  rw [doubletAction_apply, singletAction_apply, coe_electricChargeGenerator_fst,
    electricChargeGenerator_snd, electricChargeOperator_def, smul_add, smul_smul,
    ofReal_one, one_mul]

/-- On a singlet of hypercharge `y` the unbroken generator acts as `i` times the singlet
electric charge `singletElectricCharge y = y / 2`: the electric charge of a weak-isospin singlet
is `Y / 2`. -/
@[simp]
theorem singletAction_electricChargeGenerator (y : ℝ) :
    singletAction y electricChargeGenerator =
      I * (singletElectricCharge y : ℂ) := by
  rw [singletAction_apply, electricChargeGenerator_snd,
    singletElectricCharge_def, ofReal_one, one_mul]

/-- The weak-isospin weights of a doublet: `T³` scales the `k`-th basis vector by
`isospinWeight k`. -/
theorem isospinT3_mulVec_single (k : Fin 2) :
    isospinT3 *ᵥ (Pi.single k 1 : Fin 2 → ℂ) =
      (isospinWeight k : ℂ) • (Pi.single k 1 : Fin 2 → ℂ) := by
  rw [isospinT3_eq_diagonal, diagonal_mulVec_single, ← smul_eq_mul, Pi.single_smul]

/-- The charges of a doublet: the electric charge operator `T³ + y / 2` scales the `k`-th
basis vector by `doubletElectricCharge y k`. -/
theorem electricChargeOperator_mulVec_single (y : ℝ) (k : Fin 2) :
    electricChargeOperator y *ᵥ (Pi.single k 1 : Fin 2 → ℂ) =
      (doubletElectricCharge y k : ℂ) • (Pi.single k 1 : Fin 2 → ℂ) := by
  rw [electricChargeOperator_eq_diagonal, diagonal_mulVec_single, ← smul_eq_mul, Pi.single_smul]

/-- On a doublet of hypercharge `y` the unbroken generator scales the `k`-th basis vector by
`i` times its electric charge `doubletElectricCharge y k`. -/
theorem doubletAction_electricChargeGenerator_mulVec_single (y : ℝ) (k : Fin 2) :
    doubletAction y electricChargeGenerator *ᵥ (Pi.single k 1 : Fin 2 → ℂ) =
      (I * doubletElectricCharge y k) •
        (Pi.single k 1 : Fin 2 → ℂ) := by
  rw [doubletAction_electricChargeGenerator, smul_mulVec,
    electricChargeOperator_mulVec_single, smul_smul]

/-- **Electric charge is the unbroken generator.** For `v ≠ 0` the generators of
`𝔰𝔲(2) ⊕ 𝔲(1)` annihilating the Higgs vacuum `(0, v)` are exactly the real multiples of
`electricChargeGenerator`. -/
@[simp]
theorem doubletStabilizer_higgsVacuum {v : ℂ} (hv : v ≠ 0) :
    doubletStabilizer 1 (higgsVacuum v).ofLp = ℝ ∙ electricChargeGenerator := by
  ext x
  rw [mem_doubletStabilizer_iff, Submodule.mem_span_singleton, ofLp_higgsVacuum]
  constructor
  · obtain ⟨⟨A, hA⟩, β⟩ := x
    intro h
    obtain ⟨hAH, htr⟩ := (mem_su_iff A).mp hA
    rw [Matrix.trace_fin_two] at htr
    have h10 : A 1 0 = -star (A 0 1) := by
      have := congrArg (fun M => M 1 0) hAH
      simp only [conjTranspose_apply, Matrix.neg_apply] at this
      linear_combination this
    -- The upper row of `(A + i β / 2) (0, v) = 0` kills `A 0 1`; the lower row fixes
    -- `A 1 1 = -i β / 2`. Skew-Hermiticity and tracelessness then fix the other two entries.
    have hrows : doubletAction 1 (⟨A, hA⟩, β) *ᵥ ![0, v] =
        ![A 0 1 * v, (A 1 1 + I * (β / 2)) * v] := by
      ext i
      fin_cases i <;>
        simp [doubletAction_apply, singletAction_apply, Matrix.mulVec, dotProduct,
          Fin.sum_univ_two]
    rw [hrows] at h
    have h0 : A 0 1 * v = 0 := congrFun h 0
    have h1 : (A 1 1 + I * (β / 2)) * v = 0 := congrFun h 1
    have hA01 : A 0 1 = 0 := (mul_eq_zero.mp h0).resolve_right hv
    have hA11 : A 1 1 = -(I * (β / 2)) := by
      linear_combination (mul_eq_zero.mp h1).resolve_right hv
    have h00 : A 0 0 = I * (β / 2) := by linear_combination htr - hA11
    have h10' : A 1 0 = 0 := by rw [h10, hA01, star_zero, neg_zero]
    refine ⟨β, Prod.ext (Subtype.ext ?_) ?_⟩
    · -- Goal: ((β • electricChargeGenerator).1).val = ((⟨A, hA⟩, β).1).val
      dsimp
      rw [SetLike.val_smul, coe_electricChargeGenerator_fst,
        isospinT3_eq_diagonal]
      simp [h00, hA01, h10', hA11, isospinWeight_zero, isospinWeight_one]
      ext i j
      fin_cases i <;> fin_cases j <;> ring
    · simp [electricChargeGenerator]
  · rintro ⟨c, rfl⟩
    -- The vacuum is `v` times the lower basis vector, whose electric charge at `Y = 1` is
    -- `-1 / 2 + 1 / 2 = 0`, so the electric charge generator annihilates it.
    have hvac : ![0, v] = v • (Pi.single (1 : Fin 2) 1 : Fin 2 → ℂ) := by
      funext i
      fin_cases i <;> simp
    rw [map_smul, hvac, Matrix.smul_mulVec, Matrix.mulVec_smul,
      doubletAction_electricChargeGenerator_mulVec_single]
    norm_num [doubletElectricCharge_apply]

/-- There is exactly one unbroken direction: the stabilizer of the Higgs vacuum is a line. -/
theorem finrank_doubletStabilizer_higgsVacuum {v : ℂ} (hv : v ≠ 0) :
    Module.finrank ℝ (doubletStabilizer 1 (higgsVacuum v).ofLp) = 1 := by
  rw [doubletStabilizer_higgsVacuum hv, finrank_span_singleton electricChargeGenerator_ne_zero]

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

end
