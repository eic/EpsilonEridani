/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
import Physlib.Relativity.CliffordAlgebra
import Mathlib.LinearAlgebra.Matrix.Trace
import Physlib.Relativity.MinkowskiMatrix
import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct
import Physlib.Mathematics.LeviCivita.Basic
import Physlib.Mathematics.KroneckerDelta.Basic
import EpsilonEridani.Mathematics.KroneckerDelta.BasicExtensions

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
-/

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

namespace γ

open spaceTime

/-- The Clifford anticommutator identity for gamma matrices. -/
theorem gamma_anticomm (μ ν : Fin 4) :
    γ μ * γ ν + γ ν * γ μ =
      (2 * ((minkowskiMatrix
        ((@finSumFinEquiv 1 3).symm μ)
        ((@finSumFinEquiv 1 3).symm ν)) : ℝ) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  fin_cases μ <;> fin_cases ν <;>
    simp [γ, γ0, γ1, γ2, γ3, Matrix.one_fin_four]

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
    simp [slash, coord, Fin.sum_univ_four, mul_assoc] <;> ring_nf

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
  · have h' : (@finSumFinEquiv 1 3).symm μ ≠
              (@finSumFinEquiv 1 3).symm ν := by
      intro hEq
      apply h
      exact (@finSumFinEquiv 1 3).injective
        (by simpa using congrArg (@finSumFinEquiv 1 3) hEq)
    simp [h, minkowskiMatrix.off_diag_zero h']

/-- Double contraction against the Minkowski matrix keeps only diagonal terms. -/
theorem sum_mul_metric_offdiag_vanish (f : Fin 4 → Fin 4 → ℂ) :
    ∑ μ, ∑ ν, ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
      ((@finSumFinEquiv 1 3).symm ν) : ℝ) : ℂ) * f μ ν =
      ∑ μ, ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
        ((@finSumFinEquiv 1 3).symm μ) : ℝ) : ℂ) * f μ μ := by
  simp [Fin.sum_univ_four, minkowski_pull_diag, mul_assoc, mul_left_comm, mul_comm]

/-- Contracting `coord` components with the Minkowski metric gives the Minkowski product. -/
theorem coord_metric_contract (a b : Lorentz.Vector 3) :
    ∑ μ, ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
      ((@finSumFinEquiv 1 3).symm μ) : ℝ) : ℂ) *
      (coord a μ * coord b μ) =
      ((Lorentz.Vector.minkowskiProduct a b : ℝ) : ℂ) := by
  simp [coord, Fin.sum_univ_four, Lorentz.Vector.minkowskiProduct_toCoord,
    minkowskiMatrix.inl_0_inl_0,
    minkowskiMatrix.inr_i_inr_i, Complex.ofReal_neg, sub_eq_add_neg, mul_assoc, mul_left_comm,
    mul_comm]
  ring_nf

/-- Clifford anticommutator for slashed Lorentz vectors. -/
theorem slash_mul_add_mul_slash (a b : Lorentz.Vector 3) :
    slash a * slash b + slash b * slash a =
      ((2 * (Lorentz.Vector.minkowskiProduct a b : ℝ)) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  calc
    slash a * slash b + slash b * slash a
        = ∑ μ, ∑ ν, (coord a μ * coord b ν) • (γ μ * γ ν + γ ν * γ μ) := by
          simp [slash, mul_add, add_mul, Finset.sum_mul, Finset.mul_sum, smul_add, smul_mul_assoc,
            mul_smul_comm, mul_assoc, mul_left_comm, mul_comm, Finset.sum_add_distrib]
    _ = ∑ μ, ∑ ν,
          ((2 * ((minkowskiMatrix ((@finSumFinEquiv 1 3).symm μ)
            ((@finSumFinEquiv 1 3).symm ν) : ℝ) : ℂ)) *
            (coord a μ * coord b ν)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
          simp [gamma_anticomm, smul_smul, mul_assoc, mul_left_comm, mul_comm]
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
          simp [Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]
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

/-- The `γ5 γ^μ γ^ν γ^ρ γ^σ` trace equals `4 i` times the Levi-Civita symbol. -/
theorem trace_γ5_mul_γ_mul_γ_mul_γ_mul_γ (μ ν ρ σ : Fin 4) :
    Matrix.trace (γ5 * γ μ * γ ν * γ ρ * γ σ) =
      (4 * I) * (leviCivitaSymbol ![μ, ν, ρ, σ] : ℂ) := by
  fin_cases μ <;> fin_cases ν <;> fin_cases ρ <;> fin_cases σ <;>
    norm_num [leviCivitaSymbol, KroneckerDelta.generalizedKroneckerDelta,
      KroneckerDelta.kroneckerDelta, γ5, γ, γ0, γ1, γ2, γ3,
      Matrix.trace, Fin.sum_univ_four]

@[simp]
lemma trace_γ (μ : Fin 4) : Matrix.trace (γ μ) = 0 := by
  fin_cases μ <;> simp [Matrix.trace, Fin.sum_univ_four, γ, γ0, γ1, γ2, γ3]

@[simp]
lemma slash_trace (k : Lorentz.Vector 3) : Matrix.trace (Slash.slash k) = 0 := by
  simp [Slash.slash]

/-- Two-slash trace identity: `Tr[/a /b] = 4 a·b`. -/
theorem slash_mul_slash_trace (a b : Lorentz.Vector 3) :
    Matrix.trace (Slash.slash a * Slash.slash b) =
      (4 * (Lorentz.Vector.minkowskiProduct a b : ℝ) : ℂ) := by
  have hI2 : (I : ℂ) ^ 2 = -1 := by simpa [pow_two] using Complex.I_sq
  simp [Slash.slash, Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_three,
    γ0, γ1, γ2, γ3, Lorentz.Vector.minkowskiProduct_toCoord, hI2]
  ring_nf

/-- `γ5` with two slashes has vanishing trace. -/
theorem gamma5_slash_mul_slash_trace (a b : Lorentz.Vector 3) :
    Matrix.trace (γ5 * Slash.slash a * Slash.slash b) = 0 := by
  simp [γ5, Slash.slash, Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_three,
    γ0, γ1, γ2, γ3, Complex.I_sq, pow_two]
  ring_nf

/-- Cubic odd slash trace identity. -/
theorem slash_mul_slash_mul_slash_trace
    (k l m : Lorentz.Vector 3) :
    Matrix.trace (Slash.slash k * Slash.slash l * Slash.slash m) = 0 := by
  simp only [Slash.slash, add_mul, mul_add, Matrix.trace_add, Matrix.trace_neg, Matrix.trace_smul,
    map_add, map_mul, map_neg, map_sub]
  simp [Matrix.trace, Fin.sum_univ_four, γ0, γ1, γ2, γ3]

/-- The contracted identity `γ_μ γ^μ = 4 I`. -/
theorem gammaDown_mul_gamma :
    ∑ μ, γDown μ * γ μ = (4 : ℂ) • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [γDown, γ, γ0, γ1, γ2, γ3, Matrix.one_fin_four]
  ring_nf

/-- The contracted identity `γ_μ /a γ^μ = -2 /a`. -/
theorem gammaDown_mul_slash_mul_gamma (a : Lorentz.Vector 3) :
    ∑ μ, γDown μ * Slash.slash a * γ μ = (-2 : ℂ) • Slash.slash a := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [γDown, Slash.slash, Slash.coord, γ, γ0, γ1, γ2, γ3,
      Matrix.mul_assoc, Fin.sum_univ_four, Fin.sum_univ_three]
  ring_nf

/-- The contracted identity `γ_μ /a /b γ^μ = 4(a·b) I`. -/
theorem gammaDown_mul_slash_mul_slash_mul_gamma (a b : Lorentz.Vector 3) :
    ∑ μ, γDown μ * Slash.slash a * Slash.slash b * γ μ =
      ((4 * (Lorentz.Vector.minkowskiProduct a b : ℝ)) : ℂ) •
        (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hI2 : (I : ℂ) ^ 2 = -1 := by simpa [pow_two] using Complex.I_sq
  have hI4 : (I : ℂ) ^ 4 = 1 := by
    calc
      (I : ℂ) ^ 4 = ((I : ℂ) ^ 2) ^ 2 := by ring
      _ = (-1 : ℂ) ^ 2 := by simp [hI2]
      _ = 1 := by norm_num
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [γDown, Slash.slash, Slash.coord, γ, γ0, γ1, γ2, γ3,
      Matrix.mul_assoc, Fin.sum_univ_four, Fin.sum_univ_three,
      Lorentz.Vector.minkowskiProduct_toCoord, hI2, hI4]
  ring_nf

/-- The contracted identity `γ_μ /a /b /c γ^μ = -2 /c /b /a`. -/
theorem gammaDown_mul_slash_mul_slash_mul_slash_mul_gamma
    (a b c : Lorentz.Vector 3) :
    ∑ μ, γDown μ * Slash.slash a * Slash.slash b * Slash.slash c * γ μ =
      (-2 : ℂ) • (Slash.slash c * Slash.slash b * Slash.slash a) := by
  have hI2 : (I : ℂ) ^ 2 = -1 := by simpa [pow_two] using Complex.I_sq
  have hI4 : (I : ℂ) ^ 4 = 1 := by
    calc
      (I : ℂ) ^ 4 = ((I : ℂ) ^ 2) ^ 2 := by ring
      _ = (-1 : ℂ) ^ 2 := by simp [hI2]
      _ = 1 := by norm_num
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [γDown, Slash.slash, Slash.coord, γ, γ0, γ1, γ2, γ3,
      Matrix.mul_assoc, Fin.sum_univ_four, Fin.sum_univ_three, hI2, hI4]
  ring_nf

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
  have hI2 : (I : ℂ) ^ 2 = -1 := by simpa [pow_two] using Complex.I_sq
  have hI4 : (I : ℂ) ^ 4 = 1 := by
    calc
      (I : ℂ) ^ 4 = ((I : ℂ) ^ 2) ^ 2 := by ring
      _ = (-1 : ℂ) ^ 2 := by simp [hI2]
      _ = 1 := by norm_num
  simp [Slash.slash, Matrix.trace, Fin.sum_univ_four, Fin.sum_univ_three,
    γ0, γ1, γ2, γ3, Lorentz.Vector.minkowskiProduct_toCoord, hI2, hI4]
  ring_nf
  simp [Slash.coord, hI2, hI4, sub_eq_add_neg]
  ring_nf

private def reverseConj : Matrix (Fin 4) (Fin 4) ℂ := γ1 * γ3

private def reverseConjInv : Matrix (Fin 4) (Fin 4) ℂ := γ3 * γ1

@[simp] private lemma reverseConj_mul_reverseConjInv : reverseConj * reverseConjInv = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [reverseConj, reverseConjInv, γ1, γ3, Matrix.one_fin_four]

@[simp] private lemma reverseConjInv_mul_reverseConj : reverseConjInv * reverseConj = 1 := by
  ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [reverseConj, reverseConjInv, γ1, γ3, Matrix.one_fin_four]

@[simp] private lemma reverseConj_mul_γ_transpose_mul_reverseConjInv (μ : Fin 4) :
    reverseConj * Matrix.transpose (γ μ) * reverseConjInv = γ μ := by
  ext i j
  fin_cases μ <;> fin_cases i <;> fin_cases j <;>
    simp [reverseConj, reverseConjInv, γ, γ0, γ1, γ2, γ3]

@[simp] private lemma reverseConj_mul_slash_transpose_mul_reverseConjInv (k : Lorentz.Vector 3) :
    reverseConj * Matrix.transpose (Slash.slash k) * reverseConjInv = Slash.slash k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Slash.slash, Slash.coord, reverseConj, reverseConjInv, γ, γ0, γ1, γ2, γ3,
      Matrix.mul_apply, Fin.sum_univ_four, Fin.sum_univ_three]
  ring_nf

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
              simp [mul_assoc]
        _ = Slash.slash k * Slash.slashProd ks.reverse := by simpa [ih]
        _ = Slash.slashProd ((ks ++ [k]).reverse) := by simp [Slash.slashProd]

/-- Reversing a slash-product list leaves the trace unchanged:
`Tr[ /a /b /c /d ] = Tr[ /d /c /b /a ]`. -/
theorem slashProd_trace_reverse (ks : List (Lorentz.Vector 3)) :
    Matrix.trace (Slash.slashProd ks) = Matrix.trace (Slash.slashProd ks.reverse) := by
  calc
    Matrix.trace (Slash.slashProd ks)
        = Matrix.trace (Matrix.transpose (Slash.slashProd ks)) := by
            simpa using (Matrix.trace_transpose (Slash.slashProd ks)).symm
    _ = Matrix.trace (reverseConj * Matrix.transpose (Slash.slashProd ks) * reverseConjInv) := by
          symm
          rw [Matrix.trace_mul_cycle (A := reverseConj)
            (B := Matrix.transpose (Slash.slashProd ks)) (C := reverseConjInv)]
          simp [mul_assoc]
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
`Tr[ γ5 /a /b /c /d ] = 4i ε^{μνρσ} a_μ b_ν c_ρ d_σ`. -/
theorem gamma5_slash_mul_slash_mul_slash_mul_slash_trace
    (a b c d : Lorentz.Vector 3) :
    Matrix.trace (γ5 * Slash.slash a * Slash.slash b * Slash.slash c * Slash.slash d) =
      (4 * I) *
        (∑ μ, ∑ ν, ∑ ρ, ∑ σ,
          (leviCivitaSymbol ![μ, ν, ρ, σ] : ℂ) *
            Slash.coord a μ * Slash.coord b ν * Slash.coord c ρ * Slash.coord d σ) := by
  simp [Slash.slash, Slash.coord, γ, Fin.sum_univ_four,
    mul_add, add_mul, mul_assoc, Matrix.trace_add, Matrix.trace_smul,
    Finset.mul_sum, Finset.sum_mul, trace_γ5_mul_γ_mul_γ_mul_γ_mul_γ]
  ring_nf

end Trace

end γ

end diracRepresentation
end spaceTime
