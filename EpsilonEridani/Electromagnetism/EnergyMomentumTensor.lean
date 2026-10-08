/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry
public import Physlib.Relativity.MinkowskiMatrix

/-!
# The energy-momentum tensor of a field strength

The symmetric energy-momentum tensor of free Maxwell theory is, with all indices lowered,

  `T_{μν} = - F_{μα} g^{αβ} F_{νβ} + (1/4) g_{μν} F_{αβ} F^{αβ}`.

It is built from the field strength alone, so its symmetry, its trace and its transformation
under the metric-preserving group are statements about a quadratic function of the field
strength at one spacetime point; this file proves them pointwise. The same tensor, summed over
the colour index, is the gluon part of the energy-momentum tensor of QCD
(`EpsilonEridani.QFT.QCD.EnergyMomentumTensor.gluonPart`).

## Conventions

Tensors with two lower indices on a spacetime with index type `n` are matrices
`Matrix n n ℝ`. The metric `g` is any matrix, its inverse `g⁻¹` is the one of
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, and a matrix `F` is a field strength
`F_{μν}`. Raising both indices of `F` is `g⁻¹ * F * g⁻¹`, so `F_{αβ} F^{αβ}` is
`trace (g⁻¹ * F * g⁻¹ * Fᵀ)` and the trace `T^μ{}_μ` of a tensor `T` is `trace (g⁻¹ * T)`.
A Lorentz transformation `Λ` acts on lower indices by `F ↦ Λᵀ * F * Λ` and preserves `g` when
`Λᵀ * g * Λ = g`.

None of the algebraic statements needs `F` to be antisymmetric, so that hypothesis is assumed
only where it is used, in the formula for the energy density. Statements specific to the
signature `(+, -, …, -)` use Physlib's Minkowski matrix `η = diag(1, -1, …, -1)` on spacetime
`Fin 1 ⊕ Fin d` of dimension `d + 1`.

## Main definitions

* `fieldStrengthSq g F`: the invariant `F_{αβ} F^{αβ}` of a field strength.
* `maxwellTensor g F`: the energy-momentum tensor of a field strength.

## Main statements

* `isSymm_maxwellTensor`: the tensor is symmetric, for any `F`.
* `trace_maxwellTensor`: `T^μ{}_μ = (D / 4 - 1) F_{αβ} F^{αβ}` in spacetime dimension `D`.
* `maxwellTensor_equivariant`: the tensor transforms as a tensor under transformations
  preserving `g`.
* `maxwellTensor_minkowski_inl_inl`: the energy density
  `T_{00} = (1/2) Σ_i F_{0i}² + (1/4) Σ_{ij} F_{ij}²` of an antisymmetric field strength, which
  is non-negative (`maxwellTensor_minkowski_inl_inl_nonneg`).

## References

* F. J. Belinfante, *Physica* **7** (1940) 449.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Electromagnetism

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The invariant `F_{αβ} F^{αβ}` of a field strength `F` with lower indices, the indices
being raised with the inverse metric `g⁻¹`. -/
def fieldStrengthSq (g F : Matrix n n ℝ) : ℝ :=
  trace (g⁻¹ * F * g⁻¹ * Fᵀ)

lemma fieldStrengthSq_def (g F : Matrix n n ℝ) :
    fieldStrengthSq g F = trace (g⁻¹ * F * g⁻¹ * Fᵀ) := (rfl)

/-- The energy-momentum tensor `T_{μν} = - F_{μα} g^{αβ} F_{νβ} + (1/4) g_{μν} F_{αβ} F^{αβ}`
of a field strength `F`, with lower indices. It is the energy-momentum tensor of free Maxwell
theory and the gluon part of the QCD tensor for a single colour component. -/
def maxwellTensor (g F : Matrix n n ℝ) : Matrix n n ℝ :=
  -(F * g⁻¹ * Fᵀ) + (fieldStrengthSq g F / 4) • g

lemma maxwellTensor_def (g F : Matrix n n ℝ) :
    maxwellTensor g F = -(F * g⁻¹ * Fᵀ) + (fieldStrengthSq g F / 4) • g := (rfl)

/-- The energy-momentum tensor of a field strength is symmetric for a symmetric metric,
whatever the field strength. -/
theorem isSymm_maxwellTensor {g : Matrix n n ℝ} (hg : g.IsSymm) (F : Matrix n n ℝ) :
    (maxwellTensor g F).IsSymm := by
  have hginv : (g⁻¹)ᵀ = g⁻¹ := by rw [transpose_nonsing_inv, hg.eq]
  simp only [IsSymm, maxwellTensor, transpose_add, transpose_neg, transpose_smul, hg.eq,
    transpose_mul, transpose_transpose, hginv, Matrix.mul_assoc]

/-- The trace `T^μ{}_μ = (D / 4 - 1) F_{αβ} F^{αβ}` of the energy-momentum tensor of a field
strength, in spacetime dimension `D = card n`. -/
theorem trace_maxwellTensor (g F : Matrix n n ℝ) :
    trace (g⁻¹ * maxwellTensor g F) = (Fintype.card n / 4 - 1) * fieldStrengthSq g F := by
  by_cases hg : IsUnit g.det
  · have hcyc : trace (g⁻¹ * (F * g⁻¹ * Fᵀ)) = fieldStrengthSq g F := by
      simp only [fieldStrengthSq, Matrix.mul_assoc]
    simp only [maxwellTensor, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul,
      nonsing_inv_mul g hg, trace_add, trace_neg, trace_smul, trace_one, hcyc, smul_eq_mul]
    ring
  · simp [fieldStrengthSq, nonsing_inv_apply_not_isUnit g hg]

/-- The invariant `F_{αβ} F^{αβ}` is unchanged by a transformation preserving the metric. -/
theorem fieldStrengthSq_equivariant {g Λ : Matrix n n ℝ} (hΛ : Λᵀ * g * Λ = g)
    (F : Matrix n n ℝ) :
    fieldStrengthSq g (Λᵀ * F * Λ) = fieldStrengthSq g F := by
  have h (G : Matrix n n ℝ) : fieldStrengthSq g G = trace (g⁻¹ * (G * g⁻¹ * Gᵀ)) := by
    simp only [fieldStrengthSq, Matrix.mul_assoc]
  rw [h, h, transpose_mul_mul_mul_inv_mul_transpose hΛ, trace_inv_mul_transpose_mul_mul hΛ]

/-- The energy-momentum tensor of a field strength transforms as a tensor with two lower
indices under a transformation preserving the metric. -/
theorem maxwellTensor_equivariant {g Λ : Matrix n n ℝ} (hΛ : Λᵀ * g * Λ = g)
    (F : Matrix n n ℝ) :
    maxwellTensor g (Λᵀ * F * Λ) = Λᵀ * maxwellTensor g F * Λ := by
  simp only [maxwellTensor, fieldStrengthSq_equivariant hΛ,
    transpose_mul_mul_mul_inv_mul_transpose hΛ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_neg,
    Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, hΛ]

/-! ### Minkowski spacetime -/

section Minkowski

open minkowskiMatrix

variable {d : ℕ}

/-- The energy density `T_{00} = (1/2) Σ_i F_{0i}² + (1/4) Σ_{ij} F_{ij}²` of an antisymmetric
field strength on Minkowski spacetime, i.e. `(E² + B²) / 2` in four dimensions. -/
theorem maxwellTensor_minkowski_inl_inl {F : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hF : Fᵀ = -F) :
    maxwellTensor η F (Sum.inl 0) (Sum.inl 0) =
      (∑ i, F (Sum.inl 0) (Sum.inr i) ^ 2) / 2 +
        (∑ i, ∑ j, F (Sum.inr i) (Sum.inr j) ^ 2) / 4 := by
  have hanti (μ ν) : F ν μ = -F μ ν := by simpa using congrFun (congrFun hF μ) ν
  have h00 : F (Sum.inl 0) (Sum.inl 0) = 0 := by
    have := hanti (Sum.inl 0) (Sum.inl 0)
    linarith
  rw [maxwellTensor, fieldStrengthSq, Matrix.inv_eq_left_inv sq, as_diagonal]
  simp only [Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  simp only [mul_apply, transpose_apply, trace, diag_apply, diagonal_apply, ite_mul, mul_ite,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Finset.sum_singleton, Sum.elim_inl,
    Sum.elim_inr, Pi.one_apply, Pi.neg_apply, Fin.default_eq_zero, h00,
    hanti (Sum.inr _) (Sum.inl 0)]
  simp only [mul_zero, mul_one, one_mul, neg_mul, mul_neg, neg_neg, neg_sq,
    ← pow_two, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- The energy density of an antisymmetric field strength on Minkowski spacetime is
non-negative. -/
theorem maxwellTensor_minkowski_inl_inl_nonneg {F : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hF : Fᵀ = -F) : 0 ≤ maxwellTensor η F (Sum.inl 0) (Sum.inl 0) := by
  rw [maxwellTensor_minkowski_inl_inl hF]
  have h1 : 0 ≤ ∑ i, F (Sum.inl 0) (Sum.inr i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ j, F (Sum.inr i) (Sum.inr j) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

end Minkowski

end Electromagnetism
end EpsilonEridani
