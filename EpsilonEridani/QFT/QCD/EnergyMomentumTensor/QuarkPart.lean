/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Trace
public import EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry

/-!
# The quark part of the symmetric energy-momentum tensor

The quark part of the symmetric, gauge-invariant (Belinfante) energy-momentum tensor of QCD is,
with all indices lowered,

  `T_q{}_{μν} = (1/4) ψ‾ (γ_μ i D↔_ν + γ_ν i D↔_μ) ψ`,

where `D↔_ν = D→_ν - D←_ν` is the covariant derivative acting to the right minus the one acting
to the left, `ψ‾ D←_ν = (D_ν ψ)‾`. Its entries are bilinear in the field `ψ` and its covariant
derivatives `D_ν ψ` at one spacetime point, so its symmetry, its trace and its invariance
properties are pointwise statements, which this file proves. The tensor is built from `ψ` and
`D_ν ψ` only, and that is what makes it gauge invariant.

## Conventions

Tensors with two lower indices on a spacetime with index type `n` are matrices `Matrix n n ℝ`,
as in `EpsilonEridani.Electromagnetism.EnergyMomentumTensor`. The metric is `g`, its inverse is
`g⁻¹`, and the trace `T^μ{}_μ` of a tensor `T` is `trace (g⁻¹ * T)`.

The quark field at a point is a vector `ψ : m → ℂ`. The index type `m` carries the spin index
together with the colour and flavour indices, so the sum over flavours in `T_q` is part of the
contraction. The covariant derivatives at the point form a family `Dψ : n → m → ℂ`, where
`Dψ ν` is `D_ν ψ`. The gamma matrices with a lower index form a family
`γ : n → Matrix m m ℂ`, and the Dirac conjugate is `ψ‾ = ψ† β` for a matrix `β`, which is `γ⁰`
in the Dirac representation. So `ψ‾ Γ χ` is `star ψ ⬝ᵥ (β * Γ) *ᵥ χ`. The physical case has
each `β * γ μ` Hermitian, as `γ⁰ γ_μ` is. That hypothesis is assumed exactly where it is used:
it makes the bilinears `ψ‾ γ_μ i D↔_ν ψ` real.

A transformation acts on the field by `ψ ↦ S *ᵥ ψ`. A gauge transformation `U` acts on `D_ν ψ`
in the same way, which is the defining property of the covariant derivative. A Lorentz
transformation, with matrix `Λ` acting on lower indices by `T ↦ Λᵀ * T * Λ`, also acts on the
index of `D_ν ψ`.

## Main definitions

* `quarkKinetic β γ ψ Dψ`: the gauge-invariant, unsymmetrised (kinetic) tensor
  `(1/2) ψ‾ γ_μ i D↔_ν ψ`.
* `quarkPart β γ ψ Dψ`: the quark part `T_q`, the symmetric part of `quarkKinetic`.
* `diracOp g γ Dψ`: the value `i γ^μ D_μ ψ` of the Dirac operator.

## Main statements

* `isSymm_quarkPart`: `T_q` is symmetric, for any field and without equations of motion.
* `quarkKinetic_apply_of_isHermitian`: `(1/2) ψ‾ γ_μ i D↔_ν ψ = Re (ψ‾ γ_μ i D_ν ψ)`.
* `quarkPart_equivariant`: `T_q` transforms as a tensor when `ψ‾ γ_μ ψ` transforms as a vector.
* `quarkPart_mulVec`: `T_q` is invariant under a transformation `U` acting on `ψ` and on
  `D_ν ψ` that preserves the bilinears `ψ‾ γ_μ χ`. A colour rotation does this.
* `trace_quarkPart`: `T_q^μ{}_μ = Re (ψ‾ i γ^μ D_μ ψ)`.
* `trace_quarkPart_of_diracEq`: on solutions of the Dirac equation `i γ^μ D_μ ψ = M ψ`, the
  trace is the classical value `Re (ψ‾ M ψ) = Σ_q m_q ψ‾_q ψ_q`, in any spacetime dimension.

## References

* F. J. Belinfante, *Physica* **7** (1940) 449.
* D. Z. Freedman, I. J. Muzinich and E. J. Weinberg, *Ann. Phys.* **87** (1974) 95.
* X. Ji, *Phys. Rev. Lett.* **78** (1997) 610, arXiv:hep-ph/9603249, for the quark part `T_q`.
* E. Leader and C. Lorcé, *Phys. Rep.* **541** (2014) 163, arXiv:1309.4235, for the kinetic
  tensor.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace QCD
namespace EnergyMomentumTensor

open Matrix Complex

variable {n m : Type*} [Fintype m]

/-- The gauge-invariant kinetic tensor
`(1/2) ψ‾ γ_μ i D↔_ν ψ = (i/2) (ψ‾ γ_μ D_ν ψ - (D_ν ψ)‾ γ_μ ψ)` of a quark field `ψ` with covariant
derivatives `Dψ ν = D_ν ψ`, with lower indices; it is not symmetric. It is real when each
`β * γ μ` is Hermitian (`ofReal_quarkKinetic_apply`), and this definition takes its real part. -/
def quarkKinetic (β : Matrix m m ℂ) (γ : n → Matrix m m ℂ) (ψ : m → ℂ) (Dψ : n → m → ℂ) :
    Matrix n n ℝ :=
  of fun μ ν => (I * (star ψ ⬝ᵥ (β * γ μ) *ᵥ Dψ ν - star (Dψ ν) ⬝ᵥ (β * γ μ) *ᵥ ψ)).re / 2

@[simp]
lemma quarkKinetic_apply (β : Matrix m m ℂ) (γ : n → Matrix m m ℂ) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) (μ ν : n) :
    quarkKinetic β γ ψ Dψ μ ν =
      (I * (star ψ ⬝ᵥ (β * γ μ) *ᵥ Dψ ν - star (Dψ ν) ⬝ᵥ (β * γ μ) *ᵥ ψ)).re / 2 := (rfl)

/-- The quark part `T_q{}_{μν} = (1/4) ψ‾ (γ_μ i D↔_ν + γ_ν i D↔_μ) ψ` of the symmetric,
gauge-invariant energy-momentum tensor, with lower indices: the symmetric part of the kinetic
tensor `quarkKinetic`. -/
def quarkPart (β : Matrix m m ℂ) (γ : n → Matrix m m ℂ) (ψ : m → ℂ) (Dψ : n → m → ℂ) :
    Matrix n n ℝ :=
  (1 / 2 : ℝ) • (quarkKinetic β γ ψ Dψ + (quarkKinetic β γ ψ Dψ)ᵀ)

@[simp]
lemma quarkPart_def (β : Matrix m m ℂ) (γ : n → Matrix m m ℂ) (ψ : m → ℂ) (Dψ : n → m → ℂ) :
    quarkPart β γ ψ Dψ = (1 / 2 : ℝ) • (quarkKinetic β γ ψ Dψ + (quarkKinetic β γ ψ Dψ)ᵀ) :=
  (rfl)

/-- The quark part is symmetric. This is an identity: it uses neither the equations of motion
nor any property of the gamma matrices. -/
theorem isSymm_quarkPart (β : Matrix m m ℂ) (γ : n → Matrix m m ℂ) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) : (quarkPart β γ ψ Dψ).IsSymm := by
  simp only [IsSymm, quarkPart_def, transpose_smul, transpose_add, transpose_transpose, add_comm]

variable {β : Matrix m m ℂ} {γ : n → Matrix m m ℂ}

/-- When each `β * γ μ` is Hermitian, `(i/2) (ψ‾ γ_μ D_ν ψ - (D_ν ψ)‾ γ_μ ψ)` is real, so taking
the real part in `quarkKinetic` loses nothing. -/
theorem ofReal_quarkKinetic_apply (hγ : ∀ μ, (β * γ μ).IsHermitian) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) (μ ν : n) :
    (quarkKinetic β γ ψ Dψ μ ν : ℂ) =
      I * (star ψ ⬝ᵥ (β * γ μ) *ᵥ Dψ ν - star (Dψ ν) ⬝ᵥ (β * γ μ) *ᵥ ψ) / 2 := by
  rw [quarkKinetic_apply, ofReal_div, ← (hγ μ).star_dotProduct_mulVec_comm (Dψ ν) ψ]
  congr 1
  rw [← conj_eq_iff_re]
  simp only [RCLike.star_def, map_mul, map_sub, conj_I, conj_conj]
  ring

/-- When each `β * γ μ` is Hermitian, `(1/2) ψ‾ γ_μ i D↔_ν ψ = Re (ψ‾ γ_μ i D_ν ψ)`: the
derivative acting to the left contributes the complex conjugate of the one acting to the
right. -/
theorem quarkKinetic_apply_of_isHermitian (hγ : ∀ μ, (β * γ μ).IsHermitian) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) (μ ν : n) :
    quarkKinetic β γ ψ Dψ μ ν = (star ψ ⬝ᵥ (β * γ μ) *ᵥ (I • Dψ ν)).re := by
  rw [quarkKinetic_apply, ← (hγ μ).star_dotProduct_mulVec_comm ψ (Dψ ν), mulVec_smul,
    dotProduct_smul]
  simp only [RCLike.star_def, mul_re, I_re, sub_re, conj_re, I_im, sub_im, conj_im, smul_eq_mul]
  ring

/-- The kinetic tensor is invariant under a transformation `U` of the field and its
covariant derivatives that preserves the bilinears `ψ‾ γ_μ χ`. A colour gauge transformation,
unitary and commuting with `β` and with the gamma matrices, is such a transformation. -/
theorem quarkKinetic_mulVec {U : Matrix m m ℂ} (hU : ∀ μ, Uᴴ * (β * γ μ) * U = β * γ μ)
    (ψ : m → ℂ) (Dψ : n → m → ℂ) :
    quarkKinetic β γ (U *ᵥ ψ) (fun ν => U *ᵥ Dψ ν) = quarkKinetic β γ ψ Dψ := by
  ext μ ν
  simp only [quarkKinetic_apply, star_mulVec_dotProduct_mulVec_mulVec, hU]

/-- The quark part is gauge invariant: it is unchanged by a transformation `U` of the field and
its covariant derivatives that preserves the bilinears `ψ‾ γ_μ χ`, such as a colour rotation. -/
theorem quarkPart_mulVec {U : Matrix m m ℂ} (hU : ∀ μ, Uᴴ * (β * γ μ) * U = β * γ μ)
    (ψ : m → ℂ) (Dψ : n → m → ℂ) :
    quarkPart β γ (U *ᵥ ψ) (fun ν => U *ᵥ Dψ ν) = quarkPart β γ ψ Dψ := by
  rw [quarkPart_def, quarkPart_def, quarkKinetic_mulVec hU]

variable [Fintype n]

/-- The kinetic tensor transforms with two lower indices, `K ↦ Λᵀ * K * Λ`, when the
field transforms by `S` and the bilinears `ψ‾ γ_μ χ` transform as a vector under `S`,
`Sᴴ β γ_μ S = Λ_{αμ} β γ_α`. -/
theorem quarkKinetic_equivariant {S : Matrix m m ℂ} {Λ : Matrix n n ℝ}
    (hS : ∀ μ, Sᴴ * (β * γ μ) * S = ∑ α, (Λ α μ : ℂ) • (β * γ α)) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) :
    quarkKinetic β γ (S *ᵥ ψ) (fun ν => ∑ α, (Λ α ν : ℂ) • S *ᵥ Dψ α) =
      Λᵀ * quarkKinetic β γ ψ Dψ * Λ := by
  ext μ ν
  simp only [quarkKinetic_apply, mul_apply, transpose_apply, mulVec_sum, mulVec_smul,
    dotProduct_sum, dotProduct_smul, star_sum, star_smul, sum_dotProduct, smul_dotProduct,
    star_mulVec_dotProduct_mulVec_mulVec, hS,
    Matrix.sum_mulVec, smul_mulVec, Complex.star_def, conj_ofReal, smul_eq_mul,
    ← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum, re_sum, div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm I, mul_left_comm I, re_ofReal_mul, re_ofReal_mul]
  ring

/-- The quark part transforms as a tensor with two lower indices when the bilinears
`ψ‾ γ_μ χ` transform as a vector under the transformation `S` of the field. -/
theorem quarkPart_equivariant {S : Matrix m m ℂ} {Λ : Matrix n n ℝ}
    (hS : ∀ μ, Sᴴ * (β * γ μ) * S = ∑ α, (Λ α μ : ℂ) • (β * γ α)) (ψ : m → ℂ)
    (Dψ : n → m → ℂ) :
    quarkPart β γ (S *ᵥ ψ) (fun ν => ∑ α, (Λ α ν : ℂ) • S *ᵥ Dψ α) =
      Λᵀ * quarkPart β γ ψ Dψ * Λ := by
  simp only [quarkPart_def, quarkKinetic_equivariant hS, transpose_mul, transpose_transpose,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

variable [DecidableEq n]

/-- The value `i γ^μ D_μ ψ = i g^{μν} γ_ν D_μ ψ` of the Dirac operator on a field with covariant
derivatives `Dψ`. -/
def diracOp (g : Matrix n n ℝ) (γ : n → Matrix m m ℂ) (Dψ : n → m → ℂ) : m → ℂ :=
  I • ∑ μ, ∑ ν, (g⁻¹ μ ν : ℂ) • γ ν *ᵥ Dψ μ

@[simp]
lemma diracOp_def (g : Matrix n n ℝ) (γ : n → Matrix m m ℂ) (Dψ : n → m → ℂ) :
    diracOp g γ Dψ = I • ∑ μ, ∑ ν, (g⁻¹ μ ν : ℂ) • γ ν *ᵥ Dψ μ := (rfl)

/-- The trace `(1/2) g^{μν} ψ‾ γ_ν i D↔_μ ψ` of the kinetic tensor is `Re (ψ‾ i γ^μ D_μ ψ)`. -/
theorem trace_inv_mul_quarkKinetic (hγ : ∀ μ, (β * γ μ).IsHermitian) (g : Matrix n n ℝ)
    (ψ : m → ℂ) (Dψ : n → m → ℂ) :
    trace (g⁻¹ * quarkKinetic β γ ψ Dψ) = (star ψ ⬝ᵥ β *ᵥ diracOp g γ Dψ).re := by
  simp only [trace, diag, mul_apply, quarkKinetic_apply_of_isHermitian hγ, diracOp_def,
    mulVec_smul, mulVec_sum, mulVec_mulVec, dotProduct_smul, dotProduct_sum, Finset.smul_sum,
    smul_eq_mul, re_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [mul_left_comm I, re_ofReal_mul]

/-- The trace `T_q^μ{}_μ = Re (ψ‾ i γ^μ D_μ ψ)` of the quark part, for a symmetric metric. -/
theorem trace_quarkPart {g : Matrix n n ℝ} (hg : g.IsSymm) (hγ : ∀ μ, (β * γ μ).IsHermitian)
    (ψ : m → ℂ) (Dψ : n → m → ℂ) :
    trace (g⁻¹ * quarkPart β γ ψ Dψ) = (star ψ ⬝ᵥ β *ᵥ diracOp g γ Dψ).re := by
  have hT : trace (g⁻¹ * (quarkKinetic β γ ψ Dψ)ᵀ) = trace (g⁻¹ * quarkKinetic β γ ψ Dψ) := by
    rw [← trace_transpose, transpose_mul, transpose_transpose, transpose_nonsing_inv, hg.eq,
      trace_mul_comm]
  rw [quarkPart_def, Matrix.mul_smul, Matrix.mul_add, trace_smul, trace_add, hT,
    trace_inv_mul_quarkKinetic hγ, smul_eq_mul]
  ring

/-- On solutions of the Dirac equation `i γ^μ D_μ ψ = M ψ` with mass matrix `M`, the trace of
the quark part is the classical value `Re (ψ‾ M ψ)`, that is `Σ_q m_q ψ‾_q ψ_q` for a mass matrix
diagonal in flavour. This holds in every spacetime dimension. -/
theorem trace_quarkPart_of_diracEq {g : Matrix n n ℝ} (hg : g.IsSymm)
    (hγ : ∀ μ, (β * γ μ).IsHermitian) {M : Matrix m m ℂ} {ψ : m → ℂ} {Dψ : n → m → ℂ}
    (h : diracOp g γ Dψ = M *ᵥ ψ) :
    trace (g⁻¹ * quarkPart β γ ψ Dψ) = (star ψ ⬝ᵥ (β * M) *ᵥ ψ).re := by
  rw [trace_quarkPart hg hγ, h, mulVec_mulVec]

end EnergyMomentumTensor
end QCD
end QFT
end EpsilonEridani
