/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.QCD.SUNStructureConstants
public import Physlib.Mathematics.DataStructures.Matrix.LieTrace

/-!
# The adjoint matrix of a unitary colour rotation

A unitary `U ∈ U(N)` acts on the Lie algebra `su(N)` by conjugation, `X ↦ U X U†`. In the
generalized Gell-Mann basis `Tᵃ` of `EpsilonEridani.QFT.QCD.SUNGenerators`, normalised by
`Tr(TᵃTᵇ) = δᵃᵇ/2`, this action has the real matrix

```
(Ad U)ᵃᵇ = 2 Re Tr(Tᵃ U Tᵇ U†),      U Tᵇ U† = Σₐ (Ad U)ᵃᵇ Tᵃ.
```

This is the adjoint-representation counterpart of a fundamental colour matrix: an
adjoint (gluon) Wilson line is the adjoint matrix of the fundamental one. The trace is
already real, because the generators are Hermitian, so taking the real part loses nothing.

## Main results

- `SUNGen.adjointMatrix`: the matrix `(Ad U)ᵃᵇ = 2 Re Tr(Tᵃ U Tᵇ U†)`.
- `SUNGen.ofReal_adjointMatrix_apply`: the trace `2 Tr(Tᵃ U Tᵇ U†)` is real and equals the
  entry.
- `SUNGen.sum_adjointMatrix_smul_genM`: `Σₐ (Ad U)ᵃᵇ Tᵃ = U Tᵇ U†`, the defining property.
- `SUNGen.adjointMatrix_mul_transpose` and `SUNGen.adjointMatrix_mem_orthogonalGroup`: the
  adjoint matrix is real orthogonal.
- `SUNGen.adjointMatrix_one` and `SUNGen.adjointMatrix_mul`: `U ↦ Ad U` is multiplicative.
- `SUNGen.adjointHom`: the adjoint representation `U(N) →* O(N² - 1)`.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace QCD
namespace RepresentationColor

namespace SUNGen

open Matrix

variable {N : ℕ}

/-- The adjoint matrix of a unitary `U`: `(Ad U)ᵃᵇ = 2 Re Tr(Tᵃ U Tᵇ U†)` in the generalized
Gell-Mann basis. It is the matrix of `X ↦ U X U†` on `su(N)`; see
`sum_adjointMatrix_smul_genM`. -/
def adjointMatrix (U : unitaryGroup (Fin N) ℂ) : Matrix (SUNIndex N) (SUNIndex N) ℝ :=
  Matrix.of fun a b => 2 * (trace (genM N a * U.1 * genM N b * star U.1)).re

lemma adjointMatrix_apply (U : unitaryGroup (Fin N) ℂ) (a b : SUNIndex N) :
    adjointMatrix U a b = 2 * (trace (genM N a * U.1 * genM N b * star U.1)).re :=
  (rfl)

/-- The entries of the adjoint matrix are `2 Tr(Tᵃ U Tᵇ U†)`; in particular this trace is
real. -/
lemma ofReal_adjointMatrix_apply (U : unitaryGroup (Fin N) ℂ) (a b : SUNIndex N) :
    (adjointMatrix U a b : ℂ) = 2 * trace (genM N a * U.1 * genM N b * star U.1) := by
  have hconj : (starRingEnd ℂ) (trace (genM N a * U.1 * genM N b * star U.1)) =
      trace (genM N a * U.1 * genM N b * star U.1) := by
    rw [← Complex.star_def, ← trace_conjTranspose]
    simp only [conjTranspose_mul, star_eq_conjTranspose, genM_conjTranspose,
      conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [trace_mul_comm (genM N a)]
    simp only [Matrix.mul_assoc]
  simp [adjointMatrix_apply, Complex.conj_eq_iff_re.mp hconj]

/-- **The defining property of the adjoint matrix**: `Σₐ (Ad U)ᵃᵇ Tᵃ = U Tᵇ U†`, so `Ad U` is
the matrix of conjugation by `U` on `su(N)` in the basis `Tᵃ`. -/
lemma sum_adjointMatrix_smul_genM (U : unitaryGroup (Fin N) ℂ) (b : SUNIndex N) :
    ∑ a : SUNIndex N, (adjointMatrix U a b : ℂ) • genM N a = U.1 * genM N b * star U.1 := by
  set X : Matrix (Fin N) (Fin N) ℂ := U.1 * genM N b * star U.1 with hX
  have hentry : ∀ a, (adjointMatrix U a b : ℂ) = 2 * trace (X * genM N a) := by
    intro a
    rw [ofReal_adjointMatrix_apply, trace_mul_comm X]
    simp only [hX, Matrix.mul_assoc]
  ext i l
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, hentry, mul_assoc, ← Finset.mul_sum]
  simp only [sum_genM_proj_apply, hX, trace_unitary_conj, trace_genM]
  ring

/-- **The adjoint matrix is orthogonal**: `Ad U (Ad U)ᵀ = 1`. -/
lemma adjointMatrix_mul_transpose (U : unitaryGroup (Fin N) ℂ) :
    adjointMatrix U * (adjointMatrix U)ᵀ = 1 := by
  have hu : U.1 * star U.1 = 1 := Unitary.mul_star_self_of_mem U.2
  have hconj : ∀ A : Matrix (Fin N) (Fin N) ℂ, trace (star U.1 * A * U.1) = trace A := fun A => by
    simpa using trace_unitary_conj A (star U)
  have htr : ∀ a : SUNIndex N, trace (star U.1 * genM N a * U.1) = 0 := fun a => by
    rw [hconj, trace_genM]
  have hpair : ∀ a b : SUNIndex N,
      trace (star U.1 * genM N b * U.1 * (star U.1 * genM N a * U.1)) =
        (1 / 2 : ℂ) * kdA b a := fun a b => by
    have : star U.1 * genM N b * U.1 * (star U.1 * genM N a * U.1) =
        star U.1 * (genM N b * genM N a) * U := by
      simp only [Matrix.mul_assoc]
      simp only [← Matrix.mul_assoc U.1 (star U.1), hu, Matrix.one_mul]
    simp only [this, hconj, trace_genM_mul]
  have hc : ∀ a c : SUNIndex N, trace (genM N a * U.1 * genM N c * star U.1) =
      trace (star U.1 * genM N a * U.1 * genM N c) := fun a c => by
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  ext a b
  apply Complex.ofReal_injective
  rw [mul_apply, Complex.ofReal_sum]
  simp only [transpose_apply, Complex.ofReal_mul, ofReal_adjointMatrix_apply, hc]
  have h4 : ∀ c : SUNIndex N, 2 * trace (star U.1 * genM N a * U.1 * genM N c) *
      (2 * trace (star U.1 * genM N b * U.1 * genM N c)) =
      4 * (trace (star U.1 * genM N a * U.1 * genM N c) *
        trace (star U.1 * genM N b * U.1 * genM N c)) := fun c => by ring
  simp only [h4, ← Finset.mul_sum, sum_trace_pair, hpair, htr, one_apply]
  by_cases h : a = b
  · subst h
    norm_num [kdA]
  · simp [kdA, h, Ne.symm h]

/-- The adjoint matrix of a unitary lies in the orthogonal group. -/
lemma adjointMatrix_mem_orthogonalGroup (U : unitaryGroup (Fin N) ℂ) :
    adjointMatrix U ∈ orthogonalGroup (SUNIndex N) ℝ :=
  (mem_orthogonalGroup_iff _ _).mpr (adjointMatrix_mul_transpose U)

/-- The identity colour rotation has the identity adjoint matrix. -/
@[simp]
lemma adjointMatrix_one : adjointMatrix (1 : unitaryGroup (Fin N) ℂ) = 1 := by
  ext a b
  apply Complex.ofReal_injective
  rw [ofReal_adjointMatrix_apply]
  simp only [UnitaryGroup.one_val, Matrix.mul_one, star_one, trace_genM_mul, kdA, one_apply]
  split_ifs <;> simp

/-- The adjoint matrix is multiplicative, `Ad (U V) = Ad U Ad V`. -/
@[simp]
lemma adjointMatrix_mul (U V : unitaryGroup (Fin N) ℂ) :
    adjointMatrix (U * V) = adjointMatrix U * adjointMatrix V := by
  ext a b
  apply Complex.ofReal_injective
  simp only [ofReal_adjointMatrix_apply (U * V), mul_apply, Complex.ofReal_sum]
  have h : genM N a * (U * V).1 * genM N b * star (U * V).1 =
      genM N a * U.1 * (V.1 * genM N b * star V.1) * star U.1 := by
    simp only [Submonoid.coe_mul, star_mul, Matrix.mul_assoc]
  rw [h, ← sum_adjointMatrix_smul_genM]
  simp only [Finset.sum_mul, trace_sum, Finset.mul_sum, Complex.ofReal_mul,
    ofReal_adjointMatrix_apply U a, Matrix.mul_smul, Matrix.smul_mul, trace_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- The adjoint representation `U(N) → O(N² - 1)`, `U ↦ Ad U`, as a monoid homomorphism into
the orthogonal group on the adjoint index set. -/
def adjointHom : unitaryGroup (Fin N) ℂ →* orthogonalGroup (SUNIndex N) ℝ where
  toFun U := ⟨adjointMatrix U, adjointMatrix_mem_orthogonalGroup U⟩
  map_one' := Subtype.ext adjointMatrix_one
  map_mul' U V := Subtype.ext (adjointMatrix_mul U V)

@[simp]
lemma coe_adjointHom_apply (U : unitaryGroup (Fin N) ℂ) :
    (adjointHom U : Matrix (SUNIndex N) (SUNIndex N) ℝ) = adjointMatrix U :=
  (rfl)

end SUNGen

end RepresentationColor
end QCD
end QFT
end EpsilonEridani
