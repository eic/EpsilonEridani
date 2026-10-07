/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LieAlgebra.SpecialUnitary
public import Physlib.Particles.StandardModel.HiggsBoson.Basic
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
doublet. The generators that annihilate it form the line through `chargeGenerator = (i T³, 1)`.
This is the unique unbroken direction, and it lies in the Cartan subalgebra of diagonal
generators. It acts on a doublet of hypercharge `y` as `i (T³ + y / 2)` and on a singlet as
`i (y / 2)`. So the electric charge of a state with weak-isospin third component `T³` and
hypercharge `Y` is `Q = T³ + Y / 2`.

## Main results

* `stabilizer_higgsVacuum`: the generators annihilating the Higgs vacuum are the real multiples
  of `chargeGenerator`. `finrank_stabilizer_higgsVacuum` says there is exactly one.
* `doubletAction_chargeGenerator`: on a doublet of hypercharge `y` the unbroken generator acts as
  `i (T³ + y / 2)`. `isospinT3_mulVec_single` gives the weights `±1/2` of `T³` on the two
  components, `isospinT3_add_mulVec_single` the eigenvalues `±1/2 + y / 2` of `T³ + y / 2`, and
  `singletAction_chargeGenerator` is the singlet version.

## References

* S. Weinberg, *A model of leptons*, Phys. Rev. Lett. 19 (1967) 1264.
* Particle Data Group, *Electroweak model and constraints on new physics*, for the normalisation
  `Q = T³ + Y/2`.
-/

public section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

open Complex Matrix PauliMatrix StandardModel
open EpsilonEridani.LieAlgebra.SpecialUnitary

/-- The weak-isospin generator `T³ = σ³ / 2` on a doublet. Its eigenvalue is `1/2` on the
upper component and `-1/2` on the lower one. -/
noncomputable def isospinT3 : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • σ3

/-- `T³` in components. -/
theorem isospinT3_eq : isospinT3 = !![1 / 2, 0; 0, -1 / 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [isospinT3, pauliMatrix]

/-- The action of `(A, β) ∈ 𝔰𝔲(2) ⊕ 𝔲(1)` on a weak-isospin doublet of hypercharge `y`:
the matrix `A + i β (y / 2)`. -/
noncomputable def doubletAction (y : ℝ) : su (Fin 2) × ℝ →ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℂ where
  toFun x := (x.1 : Matrix (Fin 2) (Fin 2) ℂ) + (I * (x.2 * (y / 2 : ℝ) : ℂ)) • 1
  map_add' x x' := by
    simp only [Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, ofReal_add, add_mul, mul_add,
      add_smul]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, RingHom.id_apply, smul_add,
      ← smul_assoc, Complex.real_smul, smul_eq_mul, ofReal_mul]
    ring_nf

/-- The doublet action unfolded. -/
theorem doubletAction_apply (y : ℝ) (x : su (Fin 2) × ℝ) :
    doubletAction y x = (x.1 : Matrix (Fin 2) (Fin 2) ℂ) + (I * (x.2 * (y / 2 : ℝ) : ℂ)) • 1 :=
  (rfl)

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

/-- The stabilizer of a vector `φ` in a doublet of hypercharge `y`: the generators of
`𝔰𝔲(2) ⊕ 𝔲(1)` that annihilate `φ`. These are the directions of the gauge algebra left unbroken
when `φ` is the vacuum. -/
def stabilizer (y : ℝ) (φ : Fin 2 → ℂ) : Submodule ℝ (su (Fin 2) × ℝ) where
  carrier := {x | doubletAction y x *ᵥ φ = 0}
  add_mem' {x x'} hx hx' := by
    simp only [Set.mem_ofPred_eq, map_add, add_mulVec] at hx hx' ⊢
    rw [hx, hx', add_zero]
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_ofPred_eq, map_smul] at hx ⊢
    rw [← Complex.coe_smul, smul_mulVec, hx, smul_zero]

/-- Membership in the stabilizer is the vanishing of the action on `φ`. -/
@[simp]
theorem mem_stabilizer_iff (y : ℝ) (φ : Fin 2 → ℂ) (x : su (Fin 2) × ℝ) :
    x ∈ stabilizer y φ ↔ doubletAction y x *ᵥ φ = 0 :=
  (Iff.rfl)

/-- `i T³` is skew-Hermitian and traceless, so it lies in `𝔰𝔲(2)`. -/
theorem I_smul_isospinT3_mem_su : I • isospinT3 ∈ su (Fin 2) := by
  rw [mem_su_iff, isospinT3_eq]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · simp [Matrix.trace_fin_two]
    ring

/-- The electric-charge generator `(i T³, 1) ∈ 𝔰𝔲(2) ⊕ 𝔲(1)`, whose Hermitian form is
`T³ + Y / 2`. -/
noncomputable def chargeGenerator : su (Fin 2) × ℝ := (⟨I • isospinT3, I_smul_isospinT3_mem_su⟩, 1)

/-- The `𝔰𝔲(2)` component of the charge generator is `i T³`. -/
@[simp]
theorem coe_chargeGenerator_fst :
    (chargeGenerator.1 : Matrix (Fin 2) (Fin 2) ℂ) = I • isospinT3 :=
  (rfl)

/-- The hypercharge component of the charge generator is `1`. -/
@[simp]
theorem chargeGenerator_snd : chargeGenerator.2 = 1 :=
  (rfl)

/-- The charge generator lies in the Cartan subalgebra: its `𝔰𝔲(2)` component is diagonal. -/
theorem isDiag_chargeGenerator_fst :
    Matrix.IsDiag (chargeGenerator.1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [coe_chargeGenerator_fst, isospinT3_eq]
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

/-- The charge generator is nonzero. -/
theorem chargeGenerator_ne_zero : chargeGenerator ≠ 0 := by
  intro h
  simpa using congrArg Prod.snd h

/-- **The charge is `T³ + Y/2`.** On a doublet of hypercharge `y` the unbroken generator acts as
`i (T³ + y / 2)`. -/
@[simp]
theorem doubletAction_chargeGenerator (y : ℝ) :
    doubletAction y chargeGenerator = I • (isospinT3 + ((y / 2 : ℝ) : ℂ) • 1) := by
  rw [doubletAction_apply, coe_chargeGenerator_fst, chargeGenerator_snd, smul_add, smul_smul]
  push_cast
  ring_nf

/-- On a singlet of hypercharge `y` the unbroken generator acts as `i (y / 2)`: the charge of a
weak-isospin singlet is `Y / 2`. -/
@[simp]
theorem singletAction_chargeGenerator (y : ℝ) :
    singletAction y chargeGenerator = I * ((y / 2 : ℝ) : ℂ) := by
  simp [singletAction_apply]

/-- The weak-isospin weights of a doublet: `T³` scales the `k`-th basis vector by `T³ₖ`, with
`T³₀ = 1/2` and `T³₁ = -1/2`. -/
theorem isospinT3_mulVec_single (k : Fin 2) :
    isospinT3 *ᵥ (Pi.single k 1 : Fin 2 → ℂ) =
      ((![1 / 2, -1 / 2] k : ℝ) : ℂ) • (Pi.single k 1 : Fin 2 → ℂ) := by
  rw [isospinT3_eq]
  ext i
  fin_cases k <;> fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The charges of a doublet: the Hermitian charge operator `T³ + y / 2` scales the `k`-th basis
vector by `T³ₖ + y / 2`. -/
theorem isospinT3_add_mulVec_single (y : ℝ) (k : Fin 2) :
    (isospinT3 + ((y / 2 : ℝ) : ℂ) • 1) *ᵥ (Pi.single k 1 : Fin 2 → ℂ) =
      (((![1 / 2, -1 / 2] k + y / 2 : ℝ)) : ℂ) • (Pi.single k 1 : Fin 2 → ℂ) := by
  rw [add_mulVec, smul_mulVec, one_mulVec, isospinT3_mulVec_single, ofReal_add, add_smul]

/-- The Higgs vacuum `(0, v)`, in the lower (`T³ = -1/2`) component of the hypercharge-`1` Higgs
doublet. With `Q = T³ + Y / 2` this is the neutral component; Physlib's `HiggsVec.ofReal` uses
the upper component instead. -/
def higgsVacuum (v : ℂ) : HiggsVec := !₂[0, v]

/-- The Higgs vacuum in components. -/
@[simp]
theorem higgsVacuum_ofLp (v : ℂ) : (higgsVacuum v).ofLp = ![0, v] :=
  (rfl)

/-- **Electric charge is the unbroken generator.** For `v ≠ 0` the generators of
`𝔰𝔲(2) ⊕ 𝔲(1)` annihilating the Higgs vacuum `(0, v)` are exactly the real multiples of
`chargeGenerator`. -/
theorem stabilizer_higgsVacuum {v : ℂ} (hv : v ≠ 0) :
    stabilizer 1 (higgsVacuum v).ofLp = ℝ ∙ chargeGenerator := by
  ext x
  rw [mem_stabilizer_iff, Submodule.mem_span_singleton, higgsVacuum_ofLp]
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
        simp [doubletAction_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, div_eq_mul_inv]
    rw [hrows] at h
    have h0 : A 0 1 * v = 0 := congrFun h 0
    have h1 : (A 1 1 + I * (β / 2)) * v = 0 := congrFun h 1
    have hA01 : A 0 1 = 0 := (mul_eq_zero.mp h0).resolve_right hv
    have hA11 : A 1 1 = -(I * (β / 2)) := by
      linear_combination (mul_eq_zero.mp h1).resolve_right hv
    refine ⟨β, Prod.ext (Subtype.ext ?_) ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [chargeGenerator, isospinT3_eq, hA01, h10, hA11]
      · linear_combination hA11 - htr
      · ring
    · simp [chargeGenerator]
  · rintro ⟨c, rfl⟩
    -- The vacuum is `v` times the lower basis vector, whose `T³ + y / 2` eigenvalue at `Y = 1`
    -- is `-1 / 2 + 1 / 2 = 0`, so the charge annihilates it.
    have hvac : ![0, v] = v • (Pi.single (1 : Fin 2) 1 : Fin 2 → ℂ) := by
      funext i
      fin_cases i <;> simp
    have h : (isospinT3 + ((1 / 2 : ℝ) : ℂ) • 1) *ᵥ ![0, v] = 0 := by
      rw [hvac, Matrix.mulVec_smul, isospinT3_add_mulVec_single]
      norm_num
    rw [map_smul, doubletAction_chargeGenerator, Matrix.smul_mulVec, Matrix.smul_mulVec, h,
      smul_zero, smul_zero]

/-- There is exactly one unbroken direction: the stabilizer of the Higgs vacuum is a line. -/
theorem finrank_stabilizer_higgsVacuum {v : ℂ} (hv : v ≠ 0) :
    Module.finrank ℝ (stabilizer 1 (higgsVacuum v).ofLp) = 1 := by
  rw [stabilizer_higgsVacuum hv, finrank_span_singleton chargeGenerator_ne_zero]

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

end
