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

A multiplet field is a function `F : (n → ℝ) → ι → Matrix n n ℝ` of the spacetime coordinates.
Its partial derivatives at a point are a family `dF : n → ι → Matrix n n ℝ`, and its
gauge-covariant derivatives are `DF ρ = dF ρ + gaugeRotate (ω ρ) F` for antisymmetric matrices
`ω ρ`, the adjoint action of the gauge potential `A_ρ`.

## Main definitions

* `gluonFieldSq g F`: the colour-summed invariant `F^a_{αβ} F^{a αβ}`.
* `gluonPart g F`: the gluon part `T_g` of the energy-momentum tensor.
* `gaugeRotate R F`: the multiplet `F` rotated by `R`.
* `gluonPartDeriv g F G`: the variation of `T_g` at `F` in the direction `G`, bilinear in `F`
  and `G`.

## Main statements

* `isSymm_gluonPart`: `T_g` is symmetric, without equations of motion and for any `F`.
* `trace_gluonPart`: `T_g^μ{}_μ = (D / 4 - 1) F^a_{αβ} F^{a αβ}` in spacetime dimension `D`.
* `trace_gluonPart_eq_zero_iff`: the trace vanishes exactly when `D = 4` or `F^a F^a = 0`, so
  the tracelessness of the classical gluon part is special to four dimensions.
* `gluonPart_gaugeRotate`: `T_g` is invariant under orthogonal rotations of the multiplet.
* `gluonPart_equivariant`: `T_g` transforms as a tensor under transformations preserving `g`.
* `gluonPart_add`, `hasDerivAt_gluonPart_apply`: `T_g` is quadratic in the multiplet, and its
  derivative along a differentiable family of multiplets is `gluonPartDeriv`.
* `gluonPartDeriv_gaugeRotate`: infinitesimal gauge invariance, so partial derivatives of the
  multiplet may be replaced by gauge-covariant ones (`gluonPartDeriv_add_gaugeRotate`).
* `divergence_deriv_gluonPart`: given the Bianchi identity and the Yang–Mills equation
  `D^ρ F^a_{ρν} = J^a_ν`, the divergence of the gluon part is
  `∂^μ T_g{}_{μν} = - Σ_a F^a_{να} J^{a α}`. The gluon part is not conserved by itself; this is
  the momentum it exchanges with the colour current, an operator built from `F` and the current.

## References

* F. J. Belinfante, *Physica* **7** (1940) 449.
* D. Z. Freedman, I. J. Muzinich and E. J. Weinberg, *Ann. Phys.* **87** (1974) 95.
* X. Ji, *Phys. Rev. D* **52** (1995) 271, arXiv:hep-ph/9502213, for the quark-gluon split.
-/

public section

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

@[simp]
lemma gluonFieldSq_def (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) :
    gluonFieldSq g F = ∑ a, fieldStrengthSq g (F a) := (rfl)

/-- The gluon part `T_g{}_{μν} = - F^a_{μα} g^{αβ} F^a_{νβ} + (1/4) g_{μν} F^a_{αβ} F^{a αβ}` of
the symmetric, gauge-invariant energy-momentum tensor, for a colour multiplet `F` of field
strengths with lower indices. -/
def gluonPart (g : Matrix n n ℝ) (F : ι → Matrix n n ℝ) : Matrix n n ℝ :=
  ∑ a, maxwellTensor g (F a)

@[simp]
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
@[simp]
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

/-! ### Variations and the divergence -/

/-- The first-order variation of the gluon part at a multiplet `F` of field strengths in the
direction of a multiplet `G`, the colour sum `Σ_a δT(F^a; G^a)` of the variations
`maxwellTensorDeriv` of its components. It is the derivative of the gluon part along a
differentiable family of multiplets (`hasDerivAt_gluonPart_apply`). -/
def gluonPartDeriv (g : Matrix n n ℝ) :
    (ι → Matrix n n ℝ) →ₗ[ℝ] (ι → Matrix n n ℝ) →ₗ[ℝ] Matrix n n ℝ :=
  ∑ a, (maxwellTensorDeriv g).compl₁₂ (LinearMap.proj a) (LinearMap.proj a)

@[simp]
lemma gluonPartDeriv_apply (g : Matrix n n ℝ) (F G : ι → Matrix n n ℝ) :
    gluonPartDeriv g F G = ∑ a, maxwellTensorDeriv g (F a) (G a) := by
  simp [gluonPartDeriv]

/-- The gluon part is quadratic in the multiplet, with cross term `gluonPartDeriv`. -/
theorem gluonPart_add (g : Matrix n n ℝ) (F G : ι → Matrix n n ℝ) :
    gluonPart g (F + G) = gluonPart g F + gluonPartDeriv g F G + gluonPart g G := by
  simp only [gluonPart_def, gluonPartDeriv_apply, Pi.add_apply, maxwellTensor_add,
    Finset.sum_add_distrib]

/-- The gluon part of a differentiable family of multiplets is differentiable, with derivative
the variation `gluonPartDeriv` in the direction of the derivative of the family. Derivatives are
taken entry by entry. -/
theorem hasDerivAt_gluonPart_apply (g : Matrix n n ℝ) {c : ℝ → ι → Matrix n n ℝ}
    {c' : ι → Matrix n n ℝ} {t : ℝ} (hc : ∀ a i j, HasDerivAt (fun s => c s a i j) (c' a i j) t)
    (μ ν : n) :
    HasDerivAt (fun s => gluonPart g (c s) μ ν) (gluonPartDeriv g (c t) c' μ ν) t := by
  simp only [gluonPart_def, gluonPartDeriv_apply, Matrix.sum_apply]
  exact HasDerivAt.fun_sum fun a _ => hasDerivAt_maxwellTensor_apply g (hc a) μ ν

/-- Infinitesimal gauge invariance of the gluon part: its variation along an infinitesimal
rotation `F^a ↦ Σ_b ω_{ab} F^b` of the multiplet by an antisymmetric `ω` vanishes. The adjoint
action of an element of the Lie algebra of a compact gauge group is such an `ω`. -/
theorem gluonPartDeriv_gaugeRotate (g : Matrix n n ℝ) {ω : Matrix ι ι ℝ} (hω : ωᵀ = -ω)
    (F : ι → Matrix n n ℝ) : gluonPartDeriv g F (gaugeRotate ω F) = 0 := by
  have hsum : gluonPartDeriv g F (gaugeRotate ω F) =
      ∑ a, ∑ b, ω a b • maxwellTensorDeriv g (F a) (F b) := by
    simp only [gluonPartDeriv_apply, gaugeRotate_apply, map_sum, map_smul]
  -- the sum pairs the antisymmetric `ω` with the symmetric `δT(F^a; F^b)`
  have hneg : ∑ a, ∑ b, ω a b • maxwellTensorDeriv g (F a) (F b) =
      -∑ a, ∑ b, ω a b • maxwellTensorDeriv g (F a) (F b) := by
    have h (a b : ι) : ω a b = -ω b a := by simpa using congrFun (congrFun hω b) a
    calc ∑ a, ∑ b, ω a b • maxwellTensorDeriv g (F a) (F b)
        = ∑ b, ∑ a, ω a b • maxwellTensorDeriv g (F a) (F b) := Finset.sum_comm
      _ = ∑ b, ∑ a, -(ω b a • maxwellTensorDeriv g (F b) (F a)) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by
          rw [h a b, neg_smul, maxwellTensorDeriv_comm g (F a) (F b)]
      _ = -∑ a, ∑ b, ω a b • maxwellTensorDeriv g (F a) (F b) := by
        simp only [Finset.sum_neg_distrib]
  rw [hsum]
  ext i j
  have h := congrFun (congrFun hneg i) j
  simp only [Matrix.neg_apply] at h
  simp only [Matrix.zero_apply]
  linarith

/-- The variation of the gluon part is unchanged when the direction is shifted by an
infinitesimal gauge rotation of the multiplet. Applied to the derivatives of a multiplet, it
says that partial derivatives `∂_ρ F` may be replaced by gauge-covariant derivatives
`D_ρ F = ∂_ρ F + ω_ρ F`. -/
theorem gluonPartDeriv_add_gaugeRotate (g : Matrix n n ℝ) {ω : Matrix ι ι ℝ} (hω : ωᵀ = -ω)
    (F G : ι → Matrix n n ℝ) :
    gluonPartDeriv g F (G + gaugeRotate ω F) = gluonPartDeriv g F G := by
  rw [map_add, gluonPartDeriv_gaugeRotate g hω, add_zero]

/-- **The divergence of the gluon part**, pointwise. Let `F` be a multiplet of antisymmetric
field strengths and `DF ρ` multiplets of antisymmetric matrices obeying the Bianchi identity
`D_ρ F^a_{μν} + D_μ F^a_{νρ} + D_ν F^a_{ρμ} = 0`, as the gauge-covariant derivatives of a
multiplet of field strengths do. Then the divergence of the variation of the gluon part along
them is `- Σ_a F^a_{να} g^{αβ} J^a_β`, where `J^a = D^ρ F^a_{ρ·}` is the colour current that
sources the Yang–Mills equation. -/
theorem divergence_gluonPartDeriv {g : Matrix n n ℝ} (hg : g.IsSymm) (hdet : IsUnit g.det)
    {F : ι → Matrix n n ℝ} (hF : ∀ a, (F a)ᵀ = -F a) {DF : n → ι → Matrix n n ℝ}
    (hDF : ∀ ρ a, (DF ρ a)ᵀ = -DF ρ a)
    (hbianchi : ∀ a ρ μ ν, DF ρ a μ ν + DF μ a ν ρ + DF ν a ρ μ = 0) :
    divergence g (fun ρ => gluonPartDeriv g F (DF ρ)) =
      -∑ a, F a *ᵥ g⁻¹ *ᵥ divergence g (fun ρ => DF ρ a) := by
  have h : (fun ρ => gluonPartDeriv g F (DF ρ)) =
      ∑ a, fun ρ => maxwellTensorDeriv g (F a) (DF ρ a) := by
    funext ρ
    simp only [gluonPartDeriv_apply, Finset.sum_apply]
  rw [h, map_sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun a _ =>
    divergence_maxwellTensorDeriv hg hdet (hF a) (fun ρ => hDF ρ a) (hbianchi a)

/-- **The divergence of the gluon part of the energy-momentum tensor.** Let `F` be a multiplet of
antisymmetric field strengths on spacetime `n → ℝ`, with partial derivatives `dF ρ` at `x`, and
let `DF ρ = dF ρ + ω_ρ F` be its gauge-covariant derivatives for a connection acting by
antisymmetric matrices `ω ρ`. If `DF` obeys the Bianchi identity and the Yang–Mills equation
`D^ρ F^a_{ρν} = J^a_ν` with colour current `J`, then

  `∂^μ T_g{}_{μν} = - Σ_a F^a_{να} J^{a α}`.

The gluon part alone is not conserved: it exchanges momentum with whatever carries the colour
current. In the abelian case `ι = Unit`, `ω = 0` this is `∂^μ T_{μν} = - F_{να} J^α` for the
Maxwell tensor, the negative of the Lorentz force density. -/
theorem divergence_deriv_gluonPart {g : Matrix n n ℝ} (hg : g.IsSymm) (hdet : IsUnit g.det)
    {F : (n → ℝ) → ι → Matrix n n ℝ} (hF : ∀ y a, (F y a)ᵀ = -F y a) {x : n → ℝ}
    {dF : n → ι → Matrix n n ℝ}
    (hdF : ∀ ρ a i j, HasDerivAt (fun s : ℝ => F (x + s • Pi.single ρ 1) a i j) (dF ρ a i j) 0)
    {ω : n → Matrix ι ι ℝ} (hω : ∀ ρ, (ω ρ)ᵀ = -ω ρ) {DF : n → ι → Matrix n n ℝ}
    (hD : ∀ ρ, DF ρ = dF ρ + gaugeRotate (ω ρ) (F x))
    (hbianchi : ∀ a ρ μ ν, DF ρ a μ ν + DF μ a ν ρ + DF ν a ρ μ = 0) {J : ι → n → ℝ}
    (hYM : ∀ a, divergence g (fun ρ => DF ρ a) = J a) :
    divergence g (fun ρ => Matrix.of fun μ ν =>
        deriv (fun s : ℝ => gluonPart g (F (x + s • Pi.single ρ 1)) μ ν) 0) =
      -∑ a, F x a *ᵥ g⁻¹ *ᵥ J a := by
  -- the partial derivatives of the gluon part are its variations along the covariant derivatives
  have hderiv (ρ : n) : (Matrix.of fun μ ν =>
      deriv (fun s : ℝ => gluonPart g (F (x + s • Pi.single ρ 1)) μ ν) 0) =
        gluonPartDeriv g (F x) (DF ρ) := by
    ext μ ν
    rw [Matrix.of_apply, (hasDerivAt_gluonPart_apply g (hdF ρ) μ ν).deriv, hD,
      gluonPartDeriv_add_gaugeRotate g (hω ρ), zero_smul, add_zero]
  -- the partial derivatives of an antisymmetric field strength are antisymmetric
  have hdF_anti (ρ : n) (a : ι) : (dF ρ a)ᵀ = -dF ρ a := by
    ext i j
    simp only [transpose_apply, Matrix.neg_apply]
    have e : (fun s : ℝ => F (x + s • Pi.single ρ 1) a j i) =
        fun s => -F (x + s • Pi.single ρ 1) a i j :=
      funext fun s => by simpa using congrFun (congrFun (hF (x + s • Pi.single ρ 1) a) i) j
    have h := hdF ρ a j i
    rw [e] at h
    exact h.unique (hdF ρ a i j).fun_neg
  have hDF_anti (ρ : n) (a : ι) : (DF ρ a)ᵀ = -DF ρ a := by
    simp only [hD, Pi.add_apply, gaugeRotate_apply, transpose_add, transpose_sum,
      transpose_smul, hdF_anti, hF, smul_neg, Finset.sum_neg_distrib, neg_add]
  simp only [hderiv, divergence_gluonPartDeriv hg hdet (hF x) hDF_anti hbianchi, hYM]

end EnergyMomentumTensor
end QCD
end QFT
end EpsilonEridani
