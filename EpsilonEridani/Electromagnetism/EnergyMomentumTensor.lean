/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry
public import Physlib.Relativity.MinkowskiMatrix
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

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

The antisymmetry of `F` is assumed only where it is used: in the formula for the energy
density and in the divergence. Statements specific to the signature `(+, -, …, -)` use
Physlib's Minkowski matrix `η = diag(1, -1, …, -1)` on spacetime `Fin 1 ⊕ Fin d` of dimension
`d + 1`.

Derivatives are pointwise data too. The partial derivatives `∂_ρ X_{μν}` of a tensor field at a
point form a family `dX : n → Matrix n n ℝ` with `dX ρ = ∂_ρ X`, and its divergence
`∂^ρ X_{ρν} = g^{ρμ} ∂_ρ X_{μν}` is `divergence g dX`. Since the energy-momentum tensor is
quadratic in the field strength, its derivative along a field strength `F` with derivatives `G`
is the bilinear variation `maxwellTensorDeriv g F G`, and the divergence of the tensor is a
statement about `F` and `G` at one point.

## Main definitions

* `fieldStrengthSq g F`: the invariant `F_{αβ} F^{αβ}` of a field strength.
* `maxwellTensor g F`: the energy-momentum tensor of a field strength.
* `maxwellTensorDeriv g F G`: its variation at `F` in the direction `G`, bilinear in `F`, `G`.
* `divergence g dX`: the divergence `∂^ρ X_{ρν}` of a tensor with partial derivatives `dX`.

## Main statements

* `isSymm_maxwellTensor`: the tensor is symmetric, for any `F`.
* `trace_maxwellTensor`: `T^μ{}_μ = (D / 4 - 1) F_{αβ} F^{αβ}` in spacetime dimension `D`.
* `maxwellTensor_equivariant`: the tensor transforms as a tensor under transformations
  preserving `g`.
* `maxwellTensor_minkowski_inl_inl`: the energy density
  `T_{00} = (1/2) Σ_i F_{0i}² + (1/4) Σ_{ij} F_{ij}²` of an antisymmetric field strength, which
  is non-negative (`maxwellTensor_minkowski_inl_inl_nonneg`).
* `maxwellTensor_add`, `hasDerivAt_maxwellTensor_apply`: the tensor is quadratic, and its
  derivative along a differentiable family of field strengths is `maxwellTensorDeriv`.
* `divergence_maxwellTensorDeriv`: for an antisymmetric `F` whose derivatives obey the Bianchi
  identity, the divergence of the tensor is `- F_{να} J^α` with `J_ν = ∂^ρ F_{ρν}`, the negative of
  the Lorentz force density. The step that uses the Bianchi identity is
  `sum_sum_mul_eq_two_mul_of_bianchi`.

## References

* F. J. Belinfante, *Physica* **7** (1940) 449.
* J. D. Jackson, *Classical Electrodynamics*, 3rd ed. (Wiley, 1999), §12.10, for the divergence
  of the symmetric stress tensor.
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

@[simp]
lemma fieldStrengthSq_def (g F : Matrix n n ℝ) :
    fieldStrengthSq g F = trace (g⁻¹ * F * g⁻¹ * Fᵀ) := (rfl)

/-- The energy-momentum tensor `T_{μν} = - F_{μα} g^{αβ} F_{νβ} + (1/4) g_{μν} F_{αβ} F^{αβ}`
of a field strength `F`, with lower indices. It is the energy-momentum tensor of free Maxwell
theory and the gluon part of the QCD tensor for a single colour component. -/
def maxwellTensor (g F : Matrix n n ℝ) : Matrix n n ℝ :=
  -(F * g⁻¹ * Fᵀ) + (fieldStrengthSq g F / 4) • g

@[simp]
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

/-! ### Variations and the divergence -/

/-- The first-order variation of the energy-momentum tensor of a field strength `F` in the
direction of a field strength `G`,

  `δT_{μν} = - G_{μα} g^{αβ} F_{νβ} - F_{μα} g^{αβ} G_{νβ}
    + (1/4) g_{μν} (G_{αβ} F^{αβ} + F_{αβ} G^{αβ})`.

The tensor is quadratic in the field strength and this is its polarisation: the cross term of
`maxwellTensor_add`. It is the derivative of the tensor along any differentiable family of field
strengths (`hasDerivAt_maxwellTensor_apply`). -/
def maxwellTensorDeriv (g : Matrix n n ℝ) : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
  LinearMap.mk₂ ℝ
    (fun F G => -(G * g⁻¹ * Fᵀ + F * g⁻¹ * Gᵀ) +
      ((trace (g⁻¹ * G * g⁻¹ * Fᵀ) + trace (g⁻¹ * F * g⁻¹ * Gᵀ)) / 4) • g)
    (by intros; simp only [transpose_add, Matrix.add_mul, Matrix.mul_add, trace_add]; module)
    (by intros; simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
      smul_eq_mul]; module)
    (by intros; simp only [transpose_add, Matrix.add_mul, Matrix.mul_add, trace_add]; module)
    (by intros; simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, trace_smul,
      smul_eq_mul]; module)

@[simp]
lemma maxwellTensorDeriv_apply (g F G : Matrix n n ℝ) :
    maxwellTensorDeriv g F G = -(G * g⁻¹ * Fᵀ + F * g⁻¹ * Gᵀ) +
      ((trace (g⁻¹ * G * g⁻¹ * Fᵀ) + trace (g⁻¹ * F * g⁻¹ * Gᵀ)) / 4) • g := (rfl)

/-- The variation of the energy-momentum tensor is symmetric in the field strength and its
variation. -/
lemma maxwellTensorDeriv_comm (g F G : Matrix n n ℝ) :
    maxwellTensorDeriv g F G = maxwellTensorDeriv g G F := by
  simp only [maxwellTensorDeriv_apply, add_comm]

/-- The energy-momentum tensor is quadratic in the field strength, with cross term
`maxwellTensorDeriv`. -/
theorem maxwellTensor_add (g F G : Matrix n n ℝ) :
    maxwellTensor g (F + G) = maxwellTensor g F + maxwellTensorDeriv g F G + maxwellTensor g G := by
  simp only [maxwellTensor_def, maxwellTensorDeriv_apply, fieldStrengthSq_def, transpose_add,
    Matrix.add_mul, Matrix.mul_add, trace_add]
  module

/-- The energy-momentum tensor of a differentiable family of field strengths is differentiable,
with derivative the variation `maxwellTensorDeriv` in the direction of the derivative of the
family. Derivatives are taken entry by entry. -/
theorem hasDerivAt_maxwellTensor_apply (g : Matrix n n ℝ) {c : ℝ → Matrix n n ℝ}
    {c' : Matrix n n ℝ} {t : ℝ} (hc : ∀ i j, HasDerivAt (fun s => c s i j) (c' i j) t)
    (μ ν : n) :
    HasDerivAt (fun s => maxwellTensor g (c s) μ ν) (maxwellTensorDeriv g (c t) c' μ ν) t := by
  -- the entries of the contraction `c * M * cᵀ` obey the product rule
  have hmul (M : Matrix n n ℝ) (i j : n) :
      HasDerivAt (fun s => (c s * M * (c s)ᵀ) i j)
        ((c' * M * (c t)ᵀ + c t * M * c'ᵀ) i j) t := by
    simp only [mul_apply, transpose_apply, Matrix.add_apply]
    convert HasDerivAt.fun_sum fun k _ =>
      (HasDerivAt.fun_sum fun l _ => (hc i l).mul_const (M l k)).mul (hc j k) using 1
    rw [← Finset.sum_add_distrib]
  have htr : HasDerivAt (fun s => fieldStrengthSq g (c s))
      (trace (g⁻¹ * c' * g⁻¹ * (c t)ᵀ) + trace (g⁻¹ * c t * g⁻¹ * c'ᵀ)) t := by
    have h (Y : Matrix n n ℝ) : trace (g⁻¹ * Y) = ∑ i, ∑ j, g⁻¹ i j * Y j i := by
      simp only [trace, diag_apply, mul_apply]
    have e : (fun s => fieldStrengthSq g (c s)) =
        fun s => ∑ i, ∑ j, g⁻¹ i j * (c s * g⁻¹ * (c s)ᵀ) j i := by
      funext s
      rw [← h, fieldStrengthSq_def]
      simp only [Matrix.mul_assoc]
    rw [e]
    refine (HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      (hmul g⁻¹ j i).const_mul (g⁻¹ i j)).congr_deriv ?_
    rw [← h, Matrix.mul_add, trace_add]
    simp only [Matrix.mul_assoc]
  simp only [maxwellTensor_def, maxwellTensorDeriv_apply, Matrix.add_apply, Matrix.neg_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact ((hmul g⁻¹ μ ν).fun_neg.fun_add ((htr.div_const 4).mul_const (g μ ν))).congr_deriv
    (by simp only [Matrix.add_apply, add_comm])

/-- The divergence `∂^ρ X_{ρν} = g^{ρμ} ∂_ρ X_{μν}` of a tensor `X` with two lower indices,
given its partial derivatives `dX ρ = ∂_ρ X`. -/
def divergence (g : Matrix n n ℝ) : (n → Matrix n n ℝ) →ₗ[ℝ] n → ℝ where
  toFun dX ν := ∑ ρ, (g⁻¹ * dX ρ) ρ ν
  map_add' _ _ := by ext; simp [Matrix.mul_add, Finset.sum_add_distrib]
  map_smul' _ _ := by ext; simp [Finset.mul_sum]

@[simp]
lemma divergence_apply (g : Matrix n n ℝ) (dX : n → Matrix n n ℝ) (ν : n) :
    divergence g dX ν = ∑ ρ, (g⁻¹ * dX ρ) ρ ν := (rfl)

omit [DecidableEq n] in
/-- The Bianchi identity contracted with an antisymmetric tensor. If `P` is antisymmetric and the
antisymmetric matrices `G ρ` obey `G_{ρμν} + G_{μνρ} + G_{νρμ} = 0`, then
`P^{ρβ} G_{νρβ} = 2 P^{ρβ} G_{ρνβ}`. For `P = F^{ρβ}` and `G ρ = ∂_ρ F` this is
`F^{ρβ} ∂_ν F_{ρβ} = 2 F^{ρβ} ∂_ρ F_{νβ}`. -/
theorem sum_sum_mul_eq_two_mul_of_bianchi {P : Matrix n n ℝ} (hP : Pᵀ = -P)
    {G : n → Matrix n n ℝ} (hG : ∀ ρ, (G ρ)ᵀ = -G ρ)
    (hbianchi : ∀ ρ μ ν, G ρ μ ν + G μ ν ρ + G ν ρ μ = 0) (ν : n) :
    ∑ ρ, ∑ β, P ρ β * G ν ρ β = 2 * ∑ ρ, ∑ β, P ρ β * G ρ ν β := by
  -- by the Bianchi identity and antisymmetry, `G_{νρβ} = G_{ρνβ} - G_{βνρ}`
  have h1 (ρ β : n) : G ν ρ β = G ρ ν β - G β ν ρ := by
    have h2 : G ρ β ν = -G ρ ν β := by simpa using congrFun (congrFun (hG ρ) ν) β
    linarith [hbianchi ρ β ν]
  -- and the second term is the first with `ρ ↔ β`, which reverses the sign of `P`
  have h3 : ∑ ρ, ∑ β, P ρ β * G β ν ρ = -∑ ρ, ∑ β, P ρ β * G ρ ν β := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hPρβ : P ρ β = -P β ρ := by simpa using congrFun (congrFun hP β) ρ
    rw [hPρβ]
    ring
  have h4 : ∑ ρ, ∑ β, P ρ β * G ν ρ β = ∑ ρ, ∑ β, (P ρ β * G ρ ν β - P ρ β * G β ν ρ) :=
    Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun β _ => by rw [h1, mul_sub]
  simp only [h4, Finset.sum_sub_distrib, h3]
  ring

/-- **The divergence of the energy-momentum tensor of a field strength.** Let `F` be an
antisymmetric field strength and `G ρ` antisymmetric matrices obeying the Bianchi identity
`G_{ρμν} + G_{μνρ} + G_{νρμ} = 0`, as the derivatives `G ρ = ∂_ρ F` of a field strength do. Then
the divergence of the variation of the energy-momentum tensor along them is
`- F_{να} g^{αβ} J_β`, where `J = ∂^ρ G_{ρ·}` is the source of the inhomogeneous field equation.
For Maxwell theory this is `∂^μ T_{μν} = - F_{να} J^α`, the negative of the Lorentz force
density. -/
theorem divergence_maxwellTensorDeriv {g : Matrix n n ℝ} (hg : g.IsSymm) (hdet : IsUnit g.det)
    {F : Matrix n n ℝ} (hF : Fᵀ = -F) {G : n → Matrix n n ℝ} (hG : ∀ ρ, (G ρ)ᵀ = -G ρ)
    (hbianchi : ∀ ρ μ ν, G ρ μ ν + G μ ν ρ + G ν ρ μ = 0) :
    divergence g (fun ρ => maxwellTensorDeriv g F (G ρ)) = -(F *ᵥ g⁻¹ *ᵥ divergence g G) := by
  have hginv : (g⁻¹)ᵀ = g⁻¹ := by rw [transpose_nonsing_inv, hg.eq]
  -- the two traces in the variation agree
  have htr (X : Matrix n n ℝ) : trace (g⁻¹ * X * g⁻¹ * Fᵀ) = trace (g⁻¹ * F * g⁻¹ * Xᵀ) := by
    rw [← trace_transpose (g⁻¹ * F * g⁻¹ * Xᵀ)]
    simp only [transpose_mul, transpose_transpose, hginv, ← Matrix.mul_assoc]
    rw [trace_mul_comm _ g⁻¹]
    simp only [Matrix.mul_assoc]
  -- `P = F^{ρβ}`, the field strength with raised indices, is antisymmetric
  set P := g⁻¹ * F * g⁻¹ with hP_def
  have hP : Pᵀ = -P := by
    rw [hP_def, transpose_mul, transpose_mul, hginv, hF]
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
  funext ν
  -- the term `- G_{ρα} g^{αβ} F_{νβ}` contracts to `- F_{νβ} J^β`
  have hA : ∑ ρ, (g⁻¹ * (G ρ * g⁻¹ * Fᵀ)) ρ ν = (F *ᵥ g⁻¹ *ᵥ divergence g G) ν := by
    have e (ρ : n) : g⁻¹ * (G ρ * g⁻¹ * Fᵀ) = (g⁻¹ * G ρ) * (g⁻¹ * Fᵀ) := by
      simp only [Matrix.mul_assoc]
    have hT (β : n) : (g⁻¹ * Fᵀ) β ν = (F * g⁻¹) ν β := by
      rw [← transpose_apply (g⁻¹ * Fᵀ), transpose_mul, transpose_transpose, hginv]
    rw [mulVec_mulVec]
    simp only [e]
    simp only [mul_apply (M := g⁻¹ * G _) (N := g⁻¹ * Fᵀ), hT, mulVec, dotProduct,
      divergence_apply]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _
  -- the term `- F_{ρα} g^{αβ} G_{νβ}` contracts to `- F^{ρβ} ∂_ρ F_{νβ}`
  have hB : ∑ ρ, (g⁻¹ * (F * g⁻¹ * (G ρ)ᵀ)) ρ ν = ∑ ρ, ∑ β, P ρ β * G ρ ν β := by
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [show g⁻¹ * (F * g⁻¹ * (G ρ)ᵀ) = P * (G ρ)ᵀ by simp only [hP_def, Matrix.mul_assoc],
      mul_apply]
    simp only [transpose_apply]
  -- the trace term contracts with `g⁻¹ g = 1` to `(1/2) F^{ρβ} ∂_ν F_{ρβ}`
  have hC : trace (g⁻¹ * G ν * g⁻¹ * Fᵀ) + trace (P * (G ν)ᵀ) =
      2 * ∑ ρ, ∑ β, P ρ β * G ν ρ β := by
    rw [htr]
    simp only [trace, diag_apply, mul_apply, transpose_apply]
    ring
  simp only [divergence_apply, maxwellTensorDeriv_apply, Matrix.mul_add, Matrix.mul_neg,
    Matrix.mul_smul, nonsing_inv_mul g hdet, Matrix.add_apply, Matrix.neg_apply,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Pi.neg_apply]
  rw [hA, hB, hC, sum_sum_mul_eq_two_mul_of_bianchi hP hG hbianchi]
  ring

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
  simp only [Matrix.mul_apply, transpose_apply, trace, diag_apply, diagonal_apply, ite_mul, mul_ite,
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
