/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import EpsilonEridani.Electromagnetism.EnergyMomentumTensor

/-!
# The gluon part of the symmetric energy-momentum tensor

The gauge-field part of the symmetric, gauge-invariant (Belinfante) energy-momentum tensor of
QCD is, with all indices lowered,

  `T_g{}_{μν} = - F^a_{μα} g^{αβ} F^a_{νβ} + (1/4) g_{μν} F^a_{αβ} F^{a αβ}`,

summed over the colour index `a`. It is the colour sum of the energy-momentum tensor
`EpsilonEridani.Electromagnetism.maxwellTensor` of each component, so its symmetry, its trace
and its invariance properties are statements about a quadratic function of the field strengths
at one spacetime point; this file proves them pointwise.

## Conventions

The conventions for tensors, the metric `g` and its inverse are those of
`EpsilonEridani.Electromagnetism.EnergyMomentumTensor`. A colour multiplet of field strengths is
a family `F : ι → Matrix n n ℝ` indexed by a basis `ι` of the adjoint representation; a gauge
transformation acts on it by an orthogonal matrix `R : Matrix ι ι ℝ` (the adjoint action of a
compact gauge group is orthogonal in a basis orthonormal for its invariant form).

## Main definitions

* `gluonFieldSq g F`: the colour-summed invariant `F^a_{αβ} F^{a αβ}`.
* `gluonPart g F`: the gluon part `T_g` of the energy-momentum tensor.
* `gaugeRotate R F`: the multiplet `F` rotated by `R`.

## Main statements

* `isSymm_gluonPart`: `T_g` is symmetric, without equations of motion and for any `F`.
* `trace_gluonPart`: `T_g^μ{}_μ = (D / 4 - 1) F^a_{αβ} F^{a αβ}` in spacetime dimension `D`.
* `trace_gluonPart_eq_zero_iff`: the trace vanishes exactly when `D = 4` or `F^a F^a = 0`, so
  the tracelessness of the classical gluon part is special to four dimensions.
* `gluonPart_gaugeRotate`: `T_g` is invariant under orthogonal rotations of the multiplet.
* `gluonPart_equivariant`: `T_g` transforms as a tensor under transformations preserving `g`.

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

open Matrix Electromagnetism

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-! ### The colour multiplet -/

/-- The colour-summed invariant `F^a_{αβ} F^{a αβ}` of a multiplet of field strengths: the
gluon operator that appears in the trace of the gluon part (`trace_gluonPart`). -/
def gluonFieldSq (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) : ℝ :=
  ∑ a, fieldStrengthSq g (F a)

lemma gluonFieldSq_def (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) :
    gluonFieldSq g F = ∑ a, fieldStrengthSq g (F a) := (rfl)

/-- The gluon part `T_g{}_{μν} = - F^a_{μα} g^{αβ} F^a_{νβ} + (1/4) g_{μν} F^a_{αβ} F^{a αβ}` of
the symmetric, gauge-invariant energy-momentum tensor, for a colour multiplet `F` of field
strengths with lower indices. -/
def gluonPart (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) : Matrix n n ℝ :=
  ∑ a, maxwellTensor g (F a)

lemma gluonPart_def (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) :
    gluonPart g F = ∑ a, maxwellTensor g (F a) := (rfl)

/-- The gluon part is symmetric for a symmetric metric. This is an identity: it uses neither
the equations of motion nor the antisymmetry of the field strength. -/
theorem isSymm_gluonPart {g : Matrix n n ℝ} (hg : g.IsSymm) (F : ι → Matrix n n ℝ) :
    (gluonPart g F).IsSymm := by
  simp only [IsSymm, gluonPart, transpose_sum, (isSymm_maxwellTensor hg _).eq]

/-- The trace `T_g^μ{}_μ = (D / 4 - 1) F^a_{αβ} F^{a αβ}` of the gluon part in spacetime
dimension `D = card n`, as an algebraic identity in the natural number `D`. -/
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

omit [Fintype n] [DecidableEq n] in
lemma gaugeRotate_apply (R : Matrix ι ι ℝ) (F : ι → Matrix n n ℝ) (a : ι) :
    gaugeRotate R F a = ∑ b, R a b • F b := (rfl)

/-- The colour-summed contraction `F^a_{μα} g^{αβ} F^a_{νβ}` is invariant under orthogonal
rotations of the multiplet. -/
theorem sum_mul_inv_mul_transpose_gaugeRotate [DecidableEq ι] (g : Matrix n n ℝ)
    {R : Matrix ι ι ℝ} (hR : R ∈ orthogonalGroup ι ℝ) (F : ι → Matrix n n ℝ) :
    ∑ a, gaugeRotate R F a * g⁻¹ * (gaugeRotate R F a)ᵀ = ∑ a, F a * g⁻¹ * (F a)ᵀ := by
  let B : Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ →ₗ[ℝ] Matrix n n ℝ :=
    LinearMap.mk₂ ℝ (fun X Y => X * g⁻¹ * Yᵀ)
      (by intros; simp [Matrix.add_mul])
      (by intros; simp)
      (by intros; simp [Matrix.mul_add])
      (by intros; simp)
  exact B.sum_bilin_sum_smul_of_mem_orthogonalGroup hR F F

/-- The colour-summed invariant `F^a F^a` is invariant under orthogonal rotations of the
multiplet. -/
theorem gluonFieldSq_gaugeRotate [DecidableEq ι] (g : Matrix n n ℝ) {R : Matrix ι ι ℝ}
    (hR : R ∈ orthogonalGroup ι ℝ) (F : ι → Matrix n n ℝ) :
    gluonFieldSq g (gaugeRotate R F) = gluonFieldSq g F := by
  have h (G : ι → Matrix n n ℝ) :
      gluonFieldSq g G = trace (g⁻¹ * ∑ a, G a * g⁻¹ * (G a)ᵀ) := by
    simp only [gluonFieldSq, fieldStrengthSq_def, Matrix.mul_sum, trace_sum, Matrix.mul_assoc]
  rw [h, h, sum_mul_inv_mul_transpose_gaugeRotate g hR]

/-- The gluon part of the energy-momentum tensor is invariant under orthogonal rotations of the
multiplet. -/
theorem gluonPart_gaugeRotate [DecidableEq ι] (g : Matrix n n ℝ) {R : Matrix ι ι ℝ}
    (hR : R ∈ orthogonalGroup ι ℝ) (F : ι → Matrix n n ℝ) :
    gluonPart g (gaugeRotate R F) = gluonPart g F := by
  have h (G : ι → Matrix n n ℝ) :
      gluonPart g G = -(∑ a, G a * g⁻¹ * (G a)ᵀ) + (gluonFieldSq g G / 4) • g := by
    simp only [gluonPart, maxwellTensor_def, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      gluonFieldSq, Finset.sum_div, Finset.sum_smul]
  rw [h, h, gluonFieldSq_gaugeRotate g hR, sum_mul_inv_mul_transpose_gaugeRotate g hR]

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

end EnergyMomentumTensor
end QCD
end QFT
end EpsilonEridani
