/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.CliffordAlgebra
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Physlib.Relativity.MinkowskiMatrix
public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
public import Physlib.Mathematics.LeviCivita.Basic
public import Physlib.Mathematics.KroneckerDelta.Basic
public import EpsilonEridani.Mathematics.KroneckerDelta.BasicExtensions

/-!
# Gamma matrix anticommutator and Dirac slash extensions

This file extends `Physlib.Relativity.CliffordAlgebra` with the lowered gamma matrices,
the Clifford anticommutator identity, the Dirac slash operators `/a = a_μ γ^μ`, and a
collection of gamma-matrix trace identities used in tree-level QED/QCD amplitude
computations.

## Main definitions

- `spaceTime.γDown`: the lowered gamma matrices `γ_μ = η_{μν} γ^ν`.
- `spaceTime.γ.Slash.slash`: the Dirac slash `/a` of a Lorentz vector.
- `spaceTime.γ.Slash.slashProd`: the product of a list of slashed Lorentz vectors.

## Main results

- `spaceTime.γ.gamma_anticomm`: the Clifford anticommutator `{γ^μ, γ^ν} = 2 η^{μν}`.
- `spaceTime.γ.Slash.slash_mul_add_mul_slash`: the anticommutator `{/a, /b} = 2 (a·b)`.
- `spaceTime.γ.Trace.slash_mul_slash_mul_slash_mul_slash_trace`: the four-slash trace
  identity `Tr[/a /b /c /d] = 4 (a·b c·d - a·c b·d + a·d b·c)`.
- `spaceTime.γ.Trace.gamma5_slash_mul_slash_mul_slash_mul_slash_trace`: the `γ5`
  four-slash trace identity in terms of the Levi-Civita symbol.

## Implementation notes

Upstream defines `γ0, …, γ3` through `Fermion.Dirac.endEquivMatrix` rather than as matrix
literals. `gamma_anticomm` is transported from the abstract `Fermion.Dirac.gamma_anticomm`;
the literals are recovered once (`γ0_eq`, …) for the entrywise computations. The
remaining identities are reduced by linearity to identities between gamma matrices
alone, which have Gaussian-integer entries; those are checked exactly over
`GaussianInt` by kernel evaluation (`decide +kernel`, no additional axioms) and
transported to `ℂ` through `GaussianInt.toComplex`.
-/

@[expose] public section

namespace spaceTime
open Complex

noncomputable section diracRepresentation

/-- The gamma matrices in the Dirac representation, indexed as `γ0, γ1, γ2, γ3`. -/
@[simp]
def γ : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ := ![γ0, γ1, γ2, γ3]

/-- The lowered gamma matrices in the Dirac representation. -/
@[simp]
def γDown (μ : Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
    ((@finSumFinEquiv 1 3).symm μ) : ℝ) : ℂ) • γ μ

/-! ### The gamma matrices as explicit Dirac-representation matrices

Upstream defines `γ0, …, γ3` through `Fermion.Dirac.endEquivMatrix`, which does not
reduce to matrix literals. These lemmas recover the literals (from
`Fermion.Dirac.endEquivMatrix_apply` and `Fermion.Dirac.gamma_toMatrix`), so that the
entrywise computations below can evaluate them. -/

lemma γ0_eq : γ0 = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  rw [γ0, Fermion.Dirac.endEquivMatrix_apply, Fermion.Dirac.gamma_toMatrix]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_four]

lemma γ1_eq : γ1 = !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0] := by
  rw [γ1, Fermion.Dirac.endEquivMatrix_apply, Fermion.Dirac.gamma_toMatrix]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_four]

lemma γ2_eq : γ2 = !![0, 0, 0, -I; 0, 0, I, 0; 0, I, 0, 0; -I, 0, 0, 0] := by
  rw [γ2, Fermion.Dirac.endEquivMatrix_apply, Fermion.Dirac.gamma_toMatrix]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

lemma γ3_eq : γ3 = !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0] := by
  rw [γ3, Fermion.Dirac.endEquivMatrix_apply, Fermion.Dirac.gamma_toMatrix]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_four]

/-- `γ μ` is the Dirac-representation matrix of the upstream gamma endomorphism. -/
lemma γ_eq_endEquivMatrix (μ : Fin 4) :
    γ μ = Fermion.Dirac.endEquivMatrix
      (Fermion.Dirac.gamma ((@finSumFinEquiv 1 3).symm μ)) := by
  fin_cases μ <;> rfl

namespace γ

open spaceTime

/-- The Clifford anticommutator identity for gamma matrices. -/
theorem gamma_anticomm (μ ν : Fin 4) :
    γ μ * γ ν + γ ν * γ μ =
      (2 * ((minkowskiMatrix
        ((@finSumFinEquiv 1 3).symm μ)
        ((@finSumFinEquiv 1 3).symm ν)) : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [γ_eq_endEquivMatrix, γ_eq_endEquivMatrix, ← map_mul, ← map_mul, ← map_add,
    Fermion.Dirac.gamma_anticomm, map_smul, map_one]

/-! ### Dirac Slash Operators -/

namespace Slash

/-- Components of a Lorentz vector in the `γ0,γ1,γ2,γ3` ordering. -/
def coord (k : Lorentz.Vector 3) : Fin 4 → ℂ :=
  ![(k (Sum.inl 0) : ℂ), (k (Sum.inr 0) : ℂ), (k (Sum.inr 1) : ℂ), (k (Sum.inr 2) : ℂ)]

/-- The Dirac slash of a Lorentz vector. -/
def slash (k : Lorentz.Vector 3) : Matrix (Fin 4) (Fin 4) ℂ :=
  ∑ μ, coord k μ • γ μ

/-- Product of slash factors, in left-to-right order. -/
def slashProd (ks : List (Lorentz.Vector 3)) : Matrix (Fin 4) (Fin 4) ℂ :=
  (ks.map slash).prod

@[simp]
lemma slash_zero : slash (0 : Lorentz.Vector 3) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slash, coord, Fin.sum_univ_four]

@[simp]
lemma slash_add (k l : Lorentz.Vector 3) : slash (k + l) = slash k + slash l := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slash, coord, Fin.sum_univ_four] <;> ring_nf

@[simp]
lemma slash_smul (c : ℝ) (k : Lorentz.Vector 3) : slash (c • k) = c • slash k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slash, coord, Fin.sum_univ_four, mul_assoc]

@[simp]
lemma slashProd_nil : slashProd [] = 1 := rfl

@[simp]
lemma slashProd_cons (k : Lorentz.Vector 3) (ks : List (Lorentz.Vector 3)) :
    slashProd (k :: ks) = slash k * slashProd ks := rfl

/-- Off-diagonal Minkowski entries vanish after pulling indices back to `Fin 4`. -/
theorem minkowski_pull_diag (μ ν : Fin 4) :
    minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
      ((@finSumFinEquiv 1 3).symm ν) =
      if μ = ν then
        minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
          ((@finSumFinEquiv 1 3).symm μ)
      else 0 := by
  by_cases h : μ = ν
  · subst h
    simp
  · have h' : (@finSumFinEquiv 1 3).symm μ ≠ (@finSumFinEquiv 1 3).symm ν :=
      fun hEq => h ((@finSumFinEquiv 1 3).symm.injective hEq)
    rw [ite_eq_right h]
    exact minkowskiMatrix.off_diag_zero h'

/-- Double contraction against the Minkowski matrix keeps only diagonal terms. -/
theorem sum_mul_metric_offdiag_vanish (f : Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ∑ ν, ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
      ((@finSumFinEquiv 1 3).symm ν) : ℝ) : ℂ) * f μ ν =
      ∑ μ, ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
        ((@finSumFinEquiv 1 3).symm μ) : ℝ) : ℂ) * f μ μ := by
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.sum_eq_single μ]
  · intro ν _ hν
    rw [minkowski_pull_diag, ite_eq_right (Ne.symm hν), Complex.ofReal_zero, zero_mul]
  · intro hμ
    exact absurd (Finset.mem_univ μ) hμ

/-- Contracting `coord` components with the Minkowski metric gives the Minkowski product. -/
theorem coord_metric_contract (a b : Lorentz.Vector 3) :
    ∑ μ, ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
      ((@finSumFinEquiv 1 3).symm μ) : ℝ) : ℂ) *
      (coord a μ * coord b μ) =
      ((Lorentz.Vector.minkowskiProduct a b : ℝ) : ℂ) := by
  have h0 : (@finSumFinEquiv 1 3).symm 0 = Sum.inl 0 := rfl
  have h1 : (@finSumFinEquiv 1 3).symm 1 = Sum.inr 0 := rfl
  have h2 : (@finSumFinEquiv 1 3).symm 2 = Sum.inr 1 := rfl
  have h3 : (@finSumFinEquiv 1 3).symm 3 = Sum.inr 2 := rfl
  rw [Fin.sum_univ_four, Lorentz.Vector.minkowskiProduct_toCoord, Fin.sum_univ_three, h0, h1, h2,
    h3, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i, minkowskiMatrix.inr_i_inr_i,
    minkowskiMatrix.inr_i_inr_i]
  simp [coord]
  ring

/-- Clifford anticommutator for slashed Lorentz vectors. -/
theorem slash_mul_add_mul_slash (a b : Lorentz.Vector 3) :
    slash a * slash b + slash b * slash a =
      ((2 * (Lorentz.Vector.minkowskiProduct a b : ℝ)) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  calc
    slash a * slash b + slash b * slash a
        = ∑ μ, ∑ ν, (coord a μ * coord b ν) • (γ μ * γ ν + γ ν * γ μ) := by
          simp only [slash, Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, smul_add,
            Finset.sum_add_distrib]
          congr 1
          · rw [Finset.sum_comm]
          · simp only [mul_comm]
    _ = ∑ μ, ∑ ν,
          ((2 * ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
            ((@finSumFinEquiv 1 3).symm ν) : ℝ) : ℂ)) *
            (coord a μ * coord b ν)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
          refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
          rw [gamma_anticomm, smul_smul]
          congr 1
          ring
    _ = (∑ μ, ∑ ν,
          (2 * ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
            ((@finSumFinEquiv 1 3).symm ν) : ℝ) : ℂ)) *
            (coord a μ * coord b ν)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
          simp [Finset.sum_smul]
    _ = ((2 : ℂ) * (∑ μ, ∑ ν,
          ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
            ((@finSumFinEquiv 1 3).symm ν) : ℝ) : ℂ) *
            (coord a μ * coord b ν))) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
          congr 1
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
    _ = ((2 : ℂ) * ((Lorentz.Vector.minkowskiProduct a b : ℝ) : ℂ)) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
          congr 1
          rw [sum_mul_metric_offdiag_vanish]
          simpa [mul_assoc, mul_left_comm, mul_comm] using coord_metric_contract a b
    _ = ((2 * (Lorentz.Vector.minkowskiProduct a b : ℝ)) : ℂ) •
          (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
          norm_num

end Slash

/-! ### Trace Identities -/

namespace Trace

/-- The Dirac gamma matrices over the Gaussian integers; `γ_eq_map` identifies them with `γ`. -/
private def γZ : Fin 4 → Matrix (Fin 4) (Fin 4) GaussianInt := ![
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1],
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0],
  !![0, 0, 0, ⟨0, -1⟩; 0, 0, ⟨0, 1⟩, 0; 0, ⟨0, 1⟩, 0, 0; ⟨0, -1⟩, 0, 0, 0],
  !![0, 0, 1, 0; 0, 0, 0, -1; -1, 0, 0, 0; 0, 1, 0, 0]]

/-- `γ5` over the Gaussian integers; `γ5_eq_map` identifies it with `γ5`. -/
private def γ5Z : Matrix (Fin 4) (Fin 4) GaussianInt :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

private lemma γ_eq_map (μ : Fin 4) : γ μ = (γZ μ).map GaussianInt.toComplex := by
  fin_cases μ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [γ, γZ, γ0_eq, γ1_eq, γ2_eq, γ3_eq, GaussianInt.toComplex_def']

private lemma γ5_eq_map : γ5 = γ5Z.map GaussianInt.toComplex := by
  rw [γ5, γ0_eq, γ1_eq, γ2_eq, γ3_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ5Z]

/-- The trace identity over the Gaussian integers, with the Levi-Civita symbol in the product
form of `leviCivitaSymbol_eq_prod_prod_Ioi`, so that it can be checked by evaluation. -/
private lemma trace_γ5Z_mul (μ ν ρ σ : Fin 4) :
    Matrix.trace (γ5Z * γZ μ * γZ ν * γZ ρ * γZ σ) =
      ⟨0, -4⟩ * ((∏ i, ∏ j ∈ Finset.Ioi i,
        (if ![μ, ν, ρ, σ] i < ![μ, ν, ρ, σ] j then 1
          else if ![μ, ν, ρ, σ] i = ![μ, ν, ρ, σ] j then 0 else -1) : ℤ) : GaussianInt) := by
  revert μ ν ρ σ
  decide +kernel

/-- The `γ5 γ^μ γ^ν γ^ρ γ^σ` trace equals `-4 i` times the Levi-Civita symbol, normalized by
`ε(0, 1, 2, 3) = 1`, with `γ5 = i γ0 γ1 γ2 γ3`.

Checked in exact arithmetic: all matrices involved have Gaussian-integer entries, so the
identity is transported from `trace_γ5Z_mul` through `GaussianInt.toComplex`. -/
theorem trace_γ5_mul_γ_mul_γ_mul_γ_mul_γ (μ ν ρ σ : Fin 4) :
    Matrix.trace (γ5 * γ μ * γ ν * γ ρ * γ σ) =
      (-4 * I) * (leviCivitaSymbol ![μ, ν, ρ, σ] : ℂ) := by
  rw [γ5_eq_map, γ_eq_map μ, γ_eq_map ν, γ_eq_map ρ, γ_eq_map σ]
  simp only [← Matrix.map_mul]
  rw [← AddMonoidHom.map_trace, trace_γ5Z_mul, leviCivitaSymbol_eq_prod_prod_Ioi, map_mul,
    map_intCast, GaussianInt.toComplex_def']
  push_cast
  ring

@[simp]
lemma trace_γ (μ : Fin 4) : Matrix.trace (γ μ) = 0 := by
  fin_cases μ <;> simp [Matrix.trace, Fin.sum_univ_four, γ, γ0_eq, γ1_eq, γ2_eq, γ3_eq]

@[simp]
lemma slash_trace (k : Lorentz.Vector 3) : Matrix.trace (Slash.slash k) = 0 := by
  simp only [Slash.slash, Matrix.trace_sum, Matrix.trace_smul, trace_γ, smul_zero,
    Finset.sum_const_zero]

/-- Two-slash trace identity: `Tr[/a /b] = 4 a·b`. -/
theorem slash_mul_slash_trace (a b : Lorentz.Vector 3) :
    Matrix.trace (Slash.slash a * Slash.slash b) =
      (4 * (Lorentz.Vector.minkowskiProduct a b : ℝ) : ℂ) := by
  simp [Slash.slash, Slash.coord, Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_three,
    γ0_eq, γ1_eq, γ2_eq, γ3_eq, Lorentz.Vector.minkowskiProduct_toCoord]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- `γ5` with two slashes has vanishing trace. -/
theorem gamma5_slash_mul_slash_trace (a b : Lorentz.Vector 3) :
    Matrix.trace (γ5 * Slash.slash a * Slash.slash b) = 0 := by
  simp [γ5, Slash.slash, Matrix.trace, Fin.sum_univ_four, γ0_eq, γ1_eq, γ2_eq, γ3_eq]
  ring_nf

/-- Cubic odd slash trace identity. -/
theorem slash_mul_slash_mul_slash_trace
    (k l m : Lorentz.Vector 3) :
    Matrix.trace (Slash.slash k * Slash.slash l * Slash.slash m) = 0 := by
  simp [Slash.slash, Slash.coord, Matrix.trace, Fin.sum_univ_four, γ0_eq, γ1_eq, γ2_eq, γ3_eq]
  ring_nf

/-- `γDown` over the Gaussian integers. -/
private def γDownZ (μ : Fin 4) : Matrix (Fin 4) (Fin 4) GaussianInt :=
  (![1, -1, -1, -1] μ : GaussianInt) • γZ μ

private lemma γDown_eq_map (μ : Fin 4) : γDown μ = (γDownZ μ).map GaussianInt.toComplex := by
  have e0 : (@finSumFinEquiv 1 3).symm 0 = Sum.inl 0 := rfl
  have e1 : (@finSumFinEquiv 1 3).symm 1 = Sum.inr 0 := rfl
  have e2 : (@finSumFinEquiv 1 3).symm 2 = Sum.inr 1 := rfl
  have e3 : (@finSumFinEquiv 1 3).symm 3 = Sum.inr 2 := rfl
  rw [γDownZ, Matrix.map_smul' _ _ _ (map_mul _), ← γ_eq_map, γDown]
  fin_cases μ <;>
    simp [e0, e1, e2, e3, minkowskiMatrix.inl_0_inl_0, minkowskiMatrix.inr_i_inr_i]

private lemma sum_γDown_mul_γ_mul_γ (ν : Fin 4) :
    ∑ μ, γDown μ * γ ν * γ μ = (-2 : ℂ) • γ ν := by
  have key : ∑ μ, γDownZ μ * γZ ν * γZ μ = (-2 : GaussianInt) • γZ ν := by
    revert ν; decide +kernel
  simp only [γDown_eq_map, γ_eq_map, ← RingHom.mapMatrix_apply, ← map_mul, ← map_sum, key]
  rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _), ← RingHom.mapMatrix_apply]
  simp [map_ofNat]

/-- The Minkowski metric on `Fin 4` indices, as an integer table. -/
private def ηZ (ν ρ : Fin 4) : ℤ := if ν = ρ then ![1, -1, -1, -1] ν else 0

private lemma sum_γDown_mul_γ_mul_γ_mul_γ (ν ρ : Fin 4) :
    ∑ μ, γDown μ * γ ν * γ ρ * γ μ = ((4 * ηZ ν ρ : ℤ) : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have key : ∑ μ, γDownZ μ * γZ ν * γZ ρ * γZ μ = ((4 * ηZ ν ρ : ℤ) : GaussianInt) • 1 := by
    revert ν ρ; decide +kernel
  simp only [γDown_eq_map, γ_eq_map, ← RingHom.mapMatrix_apply, ← map_mul, ← map_sum, key]
  rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _), ← RingHom.mapMatrix_apply,
    map_one, map_intCast]

private lemma sum_γDown_mul_γ_mul_γ_mul_γ_mul_γ (ν ρ σ : Fin 4) :
    ∑ μ, γDown μ * γ ν * γ ρ * γ σ * γ μ = (-2 : ℂ) • (γ σ * γ ρ * γ ν) := by
  have key : ∑ μ, γDownZ μ * γZ ν * γZ ρ * γZ σ * γZ μ =
      (-2 : GaussianInt) • (γZ σ * γZ ρ * γZ ν) := by
    revert ν ρ σ; decide +kernel
  simp only [γDown_eq_map, γ_eq_map, ← RingHom.mapMatrix_apply, ← map_mul, ← map_sum, key]
  rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _), ← RingHom.mapMatrix_apply]
  simp [map_ofNat]

/-- Reverses the order of a triple sum over `Fin 4`. -/
private lemma sum_rev3 {M : Type*} [AddCommMonoid M] (f : Fin 4 → Fin 4 → Fin 4 → M) :
    ∑ z, ∑ y, ∑ x, f x y z = ∑ x, ∑ y, ∑ z, f x y z := by
  calc ∑ z, ∑ y, ∑ x, f x y z = ∑ z, ∑ x, ∑ y, f x y z :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ x, ∑ z, ∑ y, f x y z := Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ z, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private lemma trace_γ_mul_γ_mul_γ_mul_γ (ν ρ σ τ : Fin 4) :
    Matrix.trace (γ ν * γ ρ * γ σ * γ τ) =
      ((4 * (ηZ ν ρ * ηZ σ τ - ηZ ν σ * ηZ ρ τ + ηZ ν τ * ηZ ρ σ) : ℤ) : ℂ) := by
  have key : Matrix.trace (γZ ν * γZ ρ * γZ σ * γZ τ) =
      ((4 * (ηZ ν ρ * ηZ σ τ - ηZ ν σ * ηZ ρ τ + ηZ ν τ * ηZ ρ σ) : ℤ) : GaussianInt) := by
    revert ν ρ σ τ; decide +kernel
  rw [γ_eq_map ν, γ_eq_map ρ, γ_eq_map σ, γ_eq_map τ]
  simp only [← Matrix.map_mul]
  rw [← AddMonoidHom.map_trace, key, map_intCast]

/-- The contracted identity `γ_μ γ^μ = 4 I`. -/
theorem gammaDown_mul_gamma :
    ∑ μ, γDown μ * γ μ = (4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have key : ∑ μ, γDownZ μ * γZ μ = (4 : GaussianInt) • 1 := by decide +kernel
  simp only [γDown_eq_map, γ_eq_map, ← RingHom.mapMatrix_apply, ← map_mul, ← map_sum, key]
  rw [RingHom.mapMatrix_apply, Matrix.map_smul' _ _ _ (map_mul _), ← RingHom.mapMatrix_apply,
    map_one, map_ofNat]

/-- The contracted identity `γ_μ /a γ^μ = -2 /a`. -/
theorem gammaDown_mul_slash_mul_gamma (a : Lorentz.Vector 3) :
    ∑ μ, γDown μ * Slash.slash a * γ μ = (-2 : ℂ) • Slash.slash a := by
  simp only [Slash.slash, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
  rw [Finset.sum_comm]
  simp only [← Finset.smul_sum, sum_γDown_mul_γ_mul_γ]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun μ _ => smul_comm _ _ _

/-- The contracted identity `γ_μ /a /b γ^μ = 4(a·b) I`. -/
theorem gammaDown_mul_slash_mul_slash_mul_gamma (a b : Lorentz.Vector 3) :
    ∑ μ, γDown μ * Slash.slash a * Slash.slash b * γ μ =
      ((4 * (Lorentz.Vector.minkowskiProduct a b : ℝ)) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  simp only [Slash.slash, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun ν _ => Finset.sum_comm).trans ?_
  simp only [← Finset.smul_sum, sum_γDown_mul_γ_mul_γ_mul_γ, smul_smul, ← Finset.sum_smul]
  congr 1
  simp [Fin.sum_univ_four, ηZ, Slash.coord, Lorentz.Vector.minkowskiProduct_toCoord,
    Fin.sum_univ_three]
  ring

/-- The contracted identity `γ_μ /a /b /c γ^μ = -2 /c /b /a`. -/
theorem gammaDown_mul_slash_mul_slash_mul_slash_mul_gamma
    (a b c : Lorentz.Vector 3) :
    ∑ μ, γDown μ * Slash.slash a * Slash.slash b * Slash.slash c * γ μ =
      (-2 : ℂ) • (Slash.slash c * Slash.slash b * Slash.slash a) := by
  have hL : ∑ μ, γDown μ * Slash.slash a * Slash.slash b * Slash.slash c * γ μ =
      ∑ z, ∑ y, ∑ x, (Slash.coord c z * Slash.coord b y * Slash.coord a x) •
        ∑ μ, γDown μ * γ x * γ y * γ z * γ μ := by
    simp only [Slash.slash, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul, mul_assoc]
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_comm]
  have hR : Slash.slash c * Slash.slash b * Slash.slash a =
      ∑ x, ∑ y, ∑ z, (Slash.coord a x * Slash.coord b y * Slash.coord c z) •
        (γ z * γ y * γ x) := by
    simp only [Slash.slash, Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul, mul_assoc]
  rw [hL, hR, sum_rev3]
  simp only [sum_γDown_mul_γ_mul_γ_mul_γ_mul_γ, Finset.smul_sum, smul_smul]
  simp only [mul_comm, mul_assoc]

/-- Four-slash trace identity:
`Tr[ /a /b /c /d ] = 4 (a·b c·d - a·c b·d + a·d b·c)`. -/
theorem slash_mul_slash_mul_slash_mul_slash_trace
    (a b c d : Lorentz.Vector 3) :
    Matrix.trace (Slash.slash a * Slash.slash b * Slash.slash c * Slash.slash d) =
      (4 * (((Lorentz.Vector.minkowskiProduct a b : ℝ) *
        (Lorentz.Vector.minkowskiProduct c d : ℝ)) -
        ((Lorentz.Vector.minkowskiProduct a c : ℝ) *
          (Lorentz.Vector.minkowskiProduct b d : ℝ)) +
        ((Lorentz.Vector.minkowskiProduct a d : ℝ) *
          (Lorentz.Vector.minkowskiProduct b c : ℝ))) : ℂ) := by
  simp only [Slash.slash, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, trace_γ_mul_γ_mul_γ_mul_γ]
  simp [Fin.sum_univ_four, ηZ, Slash.coord, Lorentz.Vector.minkowskiProduct_toCoord,
    Fin.sum_univ_three]
  ring

private def reverseConj : Matrix (Fin 4) (Fin 4) ℂ := γ1 * γ3

private def reverseConjInv : Matrix (Fin 4) (Fin 4) ℂ := γ3 * γ1

@[simp] private lemma reverseConj_mul_reverseConjInv : reverseConj * reverseConjInv = 1 := by
  rw [reverseConj, reverseConjInv, mul_assoc, ← mul_assoc γ3, γ3_mul_γ3, neg_one_mul, mul_neg,
    γ1_mul_γ1, neg_neg]

@[simp] private lemma reverseConjInv_mul_reverseConj : reverseConjInv * reverseConj = 1 := by
  rw [reverseConj, reverseConjInv, mul_assoc, ← mul_assoc γ1, γ1_mul_γ1, neg_one_mul, mul_neg,
    γ3_mul_γ3, neg_neg]

@[simp] private lemma reverseConj_mul_γ_transpose_mul_reverseConjInv (μ : Fin 4) :
    reverseConj * Matrix.transpose (γ μ) * reverseConjInv = γ μ := by
  have key : ∀ μ, γZ 1 * γZ 3 * Matrix.transpose (γZ μ) * (γZ 3 * γZ 1) = γZ μ := by
    decide +kernel
  have h1 : γ1 = γ 1 := rfl
  have h3 : γ3 = γ 3 := rfl
  rw [reverseConj, reverseConjInv, h1, h3]
  simp only [γ_eq_map, ← Matrix.transpose_map, ← Matrix.map_mul, key]

@[simp] private lemma reverseConj_mul_slash_transpose_mul_reverseConjInv (k : Lorentz.Vector 3) :
    reverseConj * Matrix.transpose (Slash.slash k) * reverseConjInv = Slash.slash k := by
  simp only [Slash.slash, Matrix.transpose_sum, Matrix.transpose_smul, Finset.mul_sum,
    Finset.sum_mul, mul_smul_comm, smul_mul_assoc, reverseConj_mul_γ_transpose_mul_reverseConjInv]

private lemma reverseConj_mul_transpose_mul_reverseConjInv_eq_slashProd_reverse
    (ks : List (Lorentz.Vector 3)) :
    reverseConj * Matrix.transpose (Slash.slashProd ks) * reverseConjInv =
      Slash.slashProd ks.reverse := by
  induction ks using List.reverseRecOn with
  | nil =>
      simp [Slash.slashProd]
  | append_singleton ks k ih =>
      calc
        reverseConj * Matrix.transpose (Slash.slashProd (ks ++ [k])) * reverseConjInv
          = reverseConj * Matrix.transpose (Slash.slashProd ks * Slash.slash k) *
              reverseConjInv := by
              simp [Slash.slashProd, List.map_append, List.prod_append]
        _ = reverseConj *
              (Matrix.transpose (Slash.slash k) * Matrix.transpose (Slash.slashProd ks)) *
              reverseConjInv := by
              simp [Matrix.transpose_mul]
        _ = (reverseConj * Matrix.transpose (Slash.slash k) * reverseConjInv) *
            (reverseConj * Matrix.transpose (Slash.slashProd ks) * reverseConjInv) := by
              simp only [mul_assoc]
              rw [← mul_assoc reverseConjInv reverseConj, reverseConjInv_mul_reverseConj, one_mul]
        _ = Slash.slash k * Slash.slashProd ks.reverse := by
              rw [reverseConj_mul_slash_transpose_mul_reverseConjInv, ih]
        _ = Slash.slashProd ((ks ++ [k]).reverse) := by simp [Slash.slashProd]

/-- Reversing a slash-product list leaves the trace unchanged:
`Tr[ /a /b /c /d ] = Tr[ /d /c /b /a ]`. -/
theorem slashProd_trace_reverse (ks : List (Lorentz.Vector 3)) :
    Matrix.trace (Slash.slashProd ks) = Matrix.trace (Slash.slashProd ks.reverse) := by
  calc
    Matrix.trace (Slash.slashProd ks)
        = Matrix.trace (Matrix.transpose (Slash.slashProd ks)) := by
            exact (Matrix.trace_transpose (Slash.slashProd ks)).symm
    _ = Matrix.trace (reverseConj * Matrix.transpose (Slash.slashProd ks) * reverseConjInv) := by
          symm
          rw [Matrix.trace_mul_cycle (A := reverseConj)
            (B := Matrix.transpose (Slash.slashProd ks)) (C := reverseConjInv)]
          simp
    _ = Matrix.trace (Slash.slashProd ks.reverse) := by
          simp [reverseConj_mul_transpose_mul_reverseConjInv_eq_slashProd_reverse]

/-- Reversing the order of four slash factors leaves the trace unchanged:
`Tr[ /a /b /c /d ] = Tr[ /d /c /b /a ]`. -/
theorem slash_mul_slash_mul_slash_mul_slash_trace_reverse
    (a b c d : Lorentz.Vector 3) :
    Matrix.trace (Slash.slash a * Slash.slash b * Slash.slash c * Slash.slash d) =
      Matrix.trace (Slash.slash d * Slash.slash c * Slash.slash b * Slash.slash a) := by
  simpa [Slash.slashProd, Matrix.mul_assoc] using
    (slashProd_trace_reverse [a, b, c, d])

/-- `γ5` four-slash trace identity in terms of the Levi-Civita symbol:
`Tr[ γ5 /a /b /c /d ] = -4i ε_{μνρσ} a^μ b^ν c^ρ d^σ`, with `ε` normalized by
`ε(0, 1, 2, 3) = 1` as in `trace_γ5_mul_γ_mul_γ_mul_γ_mul_γ`. -/
theorem gamma5_slash_mul_slash_mul_slash_mul_slash_trace
    (a b c d : Lorentz.Vector 3) :
    Matrix.trace (γ5 * Slash.slash a * Slash.slash b * Slash.slash c * Slash.slash d) =
      (-4 * I) *
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
          (leviCivitaSymbol ![μ, ν, ρ, σ] : ℂ) *
            Slash.coord a μ * Slash.coord b ν * Slash.coord c ρ * Slash.coord d σ) := by
  simp only [Slash.slash, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul, trace_γ5_mul_γ_mul_γ_mul_γ_mul_γ]
  simp only [Fin.sum_univ_four]
  ring

end Trace

end γ

end diracRepresentation
end spaceTime
