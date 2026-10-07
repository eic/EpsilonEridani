/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry
public import Physlib.Relativity.LorentzGroup.Basic

/-!
# The gluon part of the symmetric energy-momentum tensor

The gauge-field part of the symmetric, gauge-invariant (Belinfante) energy-momentum tensor of
QCD is, with all indices lowered,

  `T_g{}_{μν} = - F^a_{μα} g^{αβ} F^a_{νβ} + (1/4) g_{μν} F^a_{αβ} F^{a αβ}`,

summed over the colour index `a`. It is built from the field strength alone, so its symmetry,
its trace and its gauge invariance are statements about a quadratic function of the field
strength at one spacetime point; this file proves them pointwise.

## Conventions

Tensors with two lower indices on a spacetime with index type `n` are matrices
`Matrix n n ℝ`. The metric `g` is any matrix, its inverse `g⁻¹` is the one of
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, and a matrix `F` is a field strength
`F_{μν}`. Raising both indices of `F` is `g⁻¹ * F * g⁻¹`, so `F_{αβ} F^{αβ}` is
`trace (g⁻¹ * F * g⁻¹ * Fᵀ)` and the trace `T^μ{}_μ` of a tensor `T` is `trace (g⁻¹ * T)`.
A Lorentz transformation `Λ` acts on lower indices by `F ↦ Λᵀ * F * Λ` and preserves `g` when
`Λᵀ * g * Λ = g`. A colour multiplet of field strengths is a family `F : ι → Matrix n n ℝ`
indexed by a basis `ι` of the adjoint representation; a gauge transformation acts on it by an
orthogonal matrix `R : Matrix ι ι ℝ` (the adjoint action of a compact gauge group is
orthogonal in a basis orthonormal for its invariant form).

None of the algebraic statements needs `F` to be antisymmetric, so that hypothesis is assumed
only where it is used, in the formula for the energy density. Statements specific to the
signature `(+, -, …, -)` use Physlib's Minkowski matrix `η = diag(1, -1, …, -1)` on spacetime
`Fin 1 ⊕ Fin d` of dimension `d + 1`.

## Main definitions

* `fieldStrengthSq g F`: the invariant `F_{αβ} F^{αβ}` of one field strength.
* `maxwellTensor g F`: the energy-momentum tensor of one abelian field strength, which is the
  gluon part for a single colour and the energy-momentum tensor of free Maxwell theory.
* `gluonFieldSq g F`: the colour-summed invariant `F^a_{αβ} F^{a αβ}`, the gluon operator of
  the trace anomaly.
* `gluonPart g F`: the gluon part `T_g` of the energy-momentum tensor.

## Main statements

* `isSymm_gluonPart`: `T_g` is symmetric, without equations of motion and for any `F`.
* `trace_gluonPart`: `T_g^μ{}_μ = (D / 4 - 1) F^a_{αβ} F^{a αβ}` in spacetime dimension `D`.
* `trace_gluonPart_eq_zero_iff`: the trace vanishes exactly when `D = 4` or `F^a F^a = 0`, so
  the tracelessness of the classical gluon part is special to four dimensions.
* `gluonPart_gaugeRotate`: `T_g` is invariant under gauge transformations of the multiplet.
* `gluonPart_equivariant`: `T_g` transforms as a tensor under transformations preserving `g`.
* `maxwellTensor_minkowski_inl_inl`: the energy density
  `T_{00} = (1/2) Σ_i F_{0i}² + (1/4) Σ_{ij} F_{ij}²` of an antisymmetric field strength, which
  is non-negative (`maxwellTensor_minkowski_inl_inl_nonneg`).

## References

* F. J. Belinfante, *Physica* **7** (1940) 449.
* D. Z. Freedman, I. J. Muzinich and E. J. Weinberg, *Ann. Phys.* **87** (1974) 95.
* X. Ji, *Phys. Rev. D* **52** (1995) 271, arXiv:hep-ph/9502213, for the quark-gluon split.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace QCD
namespace EnergyMomentumTensor

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-! ### One field strength -/

/-- The invariant `F_{αβ} F^{αβ}` of a field strength `F` with lower indices, the indices
being raised with the inverse metric `g⁻¹`. -/
def fieldStrengthSq (g F : Matrix n n ℝ) : ℝ :=
  trace (g⁻¹ * F * g⁻¹ * Fᵀ)

/-- The energy-momentum tensor `T_{μν} = - F_{μα} g^{αβ} F_{νβ} + (1/4) g_{μν} F_{αβ} F^{αβ}`
of one field strength `F`, with lower indices. It is the energy-momentum tensor of free Maxwell
theory and the gluon part of the QCD tensor for a single colour component. -/
def maxwellTensor (g F : Matrix n n ℝ) : Matrix n n ℝ :=
  -(F * g⁻¹ * Fᵀ) + (fieldStrengthSq g F / 4) • g

/-- The energy-momentum tensor of one field strength is symmetric for a symmetric metric,
whatever the field strength. -/
theorem isSymm_maxwellTensor {g : Matrix n n ℝ} (hg : g.IsSymm) (F : Matrix n n ℝ) :
    (maxwellTensor g F).IsSymm := by
  have hginv : (g⁻¹)ᵀ = g⁻¹ := by rw [transpose_nonsing_inv, hg.eq]
  simp only [IsSymm, maxwellTensor, transpose_add, transpose_neg, transpose_smul, hg.eq,
    transpose_mul, transpose_transpose, hginv, Matrix.mul_assoc]

/-- The trace `T^μ{}_μ = (D / 4 - 1) F_{αβ} F^{αβ}` of the energy-momentum tensor of one field
strength, in spacetime dimension `D = card n`. -/
theorem trace_maxwellTensor (g F : Matrix n n ℝ) :
    trace (g⁻¹ * maxwellTensor g F) = (Fintype.card n / 4 - 1) * fieldStrengthSq g F := by
  by_cases hg : IsUnit g.det
  · have hcyc : trace (g⁻¹ * (F * g⁻¹ * Fᵀ)) = fieldStrengthSq g F := by
      simp only [fieldStrengthSq, Matrix.mul_assoc]
    rw [maxwellTensor, Matrix.mul_add, Matrix.mul_neg, Matrix.mul_smul, nonsing_inv_mul g hg,
      trace_add, trace_neg, trace_smul, trace_one, hcyc, smul_eq_mul]
    ring
  · simp [fieldStrengthSq, nonsing_inv_apply_not_isUnit g hg]

/-! ### Transformations preserving the metric -/

/-- The invariant `F_{αβ} F^{αβ}` is unchanged by a transformation preserving the metric. -/
theorem fieldStrengthSq_equivariant {g Λ : Matrix n n ℝ} (hΛ : Λᵀ * g * Λ = g)
    (F : Matrix n n ℝ) :
    fieldStrengthSq g (Λᵀ * F * Λ) = fieldStrengthSq g F := by
  have hinv := mul_inv_mul_transpose_eq_inv hΛ
  calc fieldStrengthSq g (Λᵀ * F * Λ)
      = trace ((g⁻¹ * Λᵀ * F * Λ * g⁻¹ * Λᵀ * Fᵀ) * Λ) := by
        simp only [fieldStrengthSq, transpose_mul, transpose_transpose, Matrix.mul_assoc]
    _ = trace (Λ * (g⁻¹ * Λᵀ * F * Λ * g⁻¹ * Λᵀ * Fᵀ)) := trace_mul_comm _ _
    _ = trace ((Λ * g⁻¹ * Λᵀ) * F * (Λ * g⁻¹ * Λᵀ) * Fᵀ) := by simp only [Matrix.mul_assoc]
    _ = fieldStrengthSq g F := by rw [hinv, fieldStrengthSq]

/-- The energy-momentum tensor of one field strength transforms as a tensor with two lower
indices under a transformation preserving the metric. -/
theorem maxwellTensor_equivariant {g Λ : Matrix n n ℝ} (hΛ : Λᵀ * g * Λ = g)
    (F : Matrix n n ℝ) :
    maxwellTensor g (Λᵀ * F * Λ) = Λᵀ * maxwellTensor g F * Λ := by
  have hinv := mul_inv_mul_transpose_eq_inv hΛ
  have hquad : Λᵀ * F * Λ * g⁻¹ * (Λᵀ * F * Λ)ᵀ = Λᵀ * (F * g⁻¹ * Fᵀ) * Λ := by
    calc Λᵀ * F * Λ * g⁻¹ * (Λᵀ * F * Λ)ᵀ = Λᵀ * F * (Λ * g⁻¹ * Λᵀ) * Fᵀ * Λ := by
          simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      _ = Λᵀ * (F * g⁻¹ * Fᵀ) * Λ := by rw [hinv]; simp only [Matrix.mul_assoc]
  rw [maxwellTensor, maxwellTensor, fieldStrengthSq_equivariant hΛ, hquad, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, hΛ]

/-! ### The colour multiplet -/

/-- The colour-summed invariant `F^a_{αβ} F^{a αβ}` of a multiplet of field strengths: the
gluon operator that appears in the trace of the energy-momentum tensor, and whose coefficient in
the renormalized trace is the trace anomaly. -/
def gluonFieldSq (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) : ℝ :=
  ∑ a, fieldStrengthSq g (F a)

/-- The gluon part `T_g{}_{μν} = - F^a_{μα} g^{αβ} F^a_{νβ} + (1/4) g_{μν} F^a_{αβ} F^{a αβ}` of
the symmetric, gauge-invariant energy-momentum tensor, for a colour multiplet `F` of field
strengths with lower indices. -/
def gluonPart (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) : Matrix n n ℝ :=
  ∑ a, maxwellTensor g (F a)

/-- The gluon part is symmetric for a symmetric metric. This is an identity: it uses neither
the equations of motion nor the antisymmetry of the field strength. -/
theorem isSymm_gluonPart {g : Matrix n n ℝ} (hg : g.IsSymm) (F : ι → Matrix n n ℝ) :
    (gluonPart g F).IsSymm := by
  simp only [IsSymm, gluonPart, transpose_sum, (isSymm_maxwellTensor hg _).eq]

/-- The trace `T_g^μ{}_μ = (D / 4 - 1) F^a_{αβ} F^{a αβ}` of the gluon part in spacetime
dimension `D = card n`. The coefficient vanishes only at `D = 4`; continued to `D = 4 - 2ε` in
dimensional regularisation it is `-ε / 2`, the `O(ε)` term from which the trace anomaly arises. -/
theorem trace_gluonPart (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) :
    trace (g⁻¹ * gluonPart g F) = (Fintype.card n / 4 - 1) * gluonFieldSq g F := by
  simp only [gluonPart, trace_sum, trace_maxwellTensor, gluonFieldSq, Finset.mul_sum]

/-- The trace of the gluon part vanishes exactly in four spacetime dimensions or when
`F^a_{αβ} F^{a αβ} = 0`: tracelessness is special to four dimensions. -/
theorem trace_gluonPart_eq_zero_iff (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) :
    trace (g⁻¹ * gluonPart g F) = 0 ↔ Fintype.card n = 4 ∨ gluonFieldSq g F = 0 := by
  rw [trace_gluonPart, mul_eq_zero, sub_eq_zero, div_eq_one_iff_eq (by norm_num)]
  norm_cast

/-- A colour multiplet rotated by `R : Matrix ι ι ℝ`, `F^a ↦ Σ_b R_{ab} F^b`; for `R` in the
adjoint representation of the gauge group this is a gauge transformation. -/
def gaugeRotate (R : Matrix ι ι ℝ) (F : ι → Matrix n n ℝ) : ι → Matrix n n ℝ :=
  fun a => ∑ b, R a b • F b

/-- The colour-summed invariant `F^a F^a` is gauge invariant. -/
theorem gluonFieldSq_gaugeRotate [DecidableEq ι] (g : Matrix n n ℝ) {R : Matrix ι ι ℝ}
    (hR : R ∈ orthogonalGroup ι ℝ) (F : ι → Matrix n n ℝ) :
    gluonFieldSq g (gaugeRotate R F) = gluonFieldSq g F := by
  let B : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun X Y => trace (g⁻¹ * X * g⁻¹ * Yᵀ))
      (by intros; simp [Matrix.mul_add, Matrix.add_mul])
      (by intros; simp)
      (by intros; simp [Matrix.mul_add])
      (by intros; simp)
  exact sum_bilin_sum_smul_of_mem_orthogonalGroup B hR F F

/-- The gluon part of the energy-momentum tensor is gauge invariant. -/
theorem gluonPart_gaugeRotate [DecidableEq ι] (g : Matrix n n ℝ) {R : Matrix ι ι ℝ}
    (hR : R ∈ orthogonalGroup ι ℝ) (F : ι → Matrix n n ℝ) :
    gluonPart g (gaugeRotate R F) = gluonPart g F := by
  let B : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
    LinearMap.mk₂ ℝ (fun X Y => X * g⁻¹ * Yᵀ)
      (by intros; simp [Matrix.add_mul])
      (by intros; simp)
      (by intros; simp [Matrix.mul_add])
      (by intros; simp)
  have hsum (G : ι → Matrix n n ℝ) :
      gluonPart g G = -(∑ a, G a * g⁻¹ * (G a)ᵀ) + (gluonFieldSq g G / 4) • g := by
    simp only [gluonPart, maxwellTensor, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      gluonFieldSq, Finset.sum_div, Finset.sum_smul]
  rw [hsum, hsum, gluonFieldSq_gaugeRotate g hR F]
  congr 2
  exact sum_bilin_sum_smul_of_mem_orthogonalGroup B hR F F

/-- The colour-summed invariant `F^a F^a` is unchanged by a transformation preserving the
metric. -/
theorem gluonFieldSq_equivariant {g Λ : Matrix n n ℝ} (hΛ : Λᵀ * g * Λ = g)
    (F : ι → Matrix n n ℝ) :
    gluonFieldSq g (fun a => Λᵀ * F a * Λ) = gluonFieldSq g F := by
  simp only [gluonFieldSq, fieldStrengthSq_equivariant hΛ]

/-- The gluon part transforms as a tensor with two lower indices under a transformation
preserving the metric. -/
theorem gluonPart_equivariant {g Λ : Matrix n n ℝ} (hΛ : Λᵀ * g * Λ = g)
    (F : ι → Matrix n n ℝ) :
    gluonPart g (fun a => Λᵀ * F a * Λ) = Λᵀ * gluonPart g F * Λ := by
  simp only [gluonPart, maxwellTensor_equivariant hΛ, Matrix.mul_sum, Matrix.sum_mul]

/-! ### Minkowski spacetime -/

section Minkowski

open minkowskiMatrix

variable {d : ℕ}

/-- The trace of the gluon part on Minkowski spacetime with `d` space dimensions is
`T_g^μ{}_μ = ((d - 3) / 4) F^a_{αβ} F^{a αβ}`. -/
theorem trace_gluonPart_minkowski (F : ι → Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    trace (η * gluonPart η F) = (d - 3) / 4 * gluonFieldSq η F := by
  have h := trace_gluonPart (η : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) F
  rw [Matrix.inv_eq_left_inv sq] at h
  rw [h]
  simp only [Fintype.card_sum, Fintype.card_unique, Fintype.card_fin, Nat.cast_add,
    Nat.cast_one]
  ring

/-- The gluon part transforms as a tensor under the Lorentz group. -/
theorem gluonPart_equivariant_lorentzGroup {Λ : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ}
    (hΛ : Λ ∈ LorentzGroup d) (F : ι → Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) :
    gluonPart η (fun a => Λᵀ * F a * Λ) = Λᵀ * gluonPart η F * Λ :=
  gluonPart_equivariant ((LorentzGroup.mem_iff_transpose_mul_minkowskiMatrix_mul_self Λ).mp hΛ) F

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

end EnergyMomentumTensor
end QCD
end QFT
end EpsilonEridani
