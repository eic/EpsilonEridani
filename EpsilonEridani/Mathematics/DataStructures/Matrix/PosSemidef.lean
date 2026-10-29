/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import TauCeti.Analysis.Matrix.PosSemidef


/-!
# Entrywise bounds for positive-semidefinite matrices

A positive-semidefinite matrix `M` over `RCLike 𝕜` carries two entrywise bounds:

* `Matrix.PosSemidef.re_apply_self_nonneg`: `0 ≤ re (M i i)`;
* `Matrix.PosSemidef.two_mul_norm_apply_le`: `2 * ‖M i j‖ ≤ re (M i i) + re (M j j)`.

The second is the arithmetic-mean form of the Cauchy-Schwarz bound `Matrix.PosSemidef.normSq_le`
of `TauCeti.Analysis.Matrix.PosSemidef`. It is stated multiplied out, with no division, so that it
applies without field side conditions. Its specialisation to `𝕜 = ℝ` is
`Matrix.PosSemidef.two_mul_abs_apply_le`, `2 * |M i j| ≤ M i i + M j j`; over `ℝ` the first bound
is Mathlib's `Matrix.PosSemidef.diag_nonneg`, and the real case of `normSq_le` is
`Matrix.PosSemidef.sq_apply_le`, `(M i j) ^ 2 ≤ M i i * M j j`. This is the form in which
positivity constraints are used in hadronic physics; see
`EpsilonEridani/Particles/Parton/PDF/Positivity.lean` for the Soffer bound on the quark transversity
distribution, which is exactly the arithmetic-mean inequality applied to the parton spin-density
matrix.

The entrywise real part of a positive-semidefinite matrix is positive semidefinite, and a real
matrix is positive semidefinite exactly when its image under the coercion `ℝ → 𝕜` is. This is what
lets a complex positive-semidefinite matrix descend to a real one.

## Main results

- `Matrix.PosSemidef.re_apply_self_nonneg`: nonnegativity of the real part of the diagonal.
- `Matrix.PosSemidef.two_mul_norm_apply_le`: the entrywise arithmetic-mean bound over `RCLike`.
- `Matrix.PosSemidef.sq_apply_le`: the entrywise geometric-mean bound over `ℝ`.
- `Matrix.PosSemidef.two_mul_abs_apply_le`: the real specialisation of the arithmetic-mean bound.
- `Matrix.re_star_dotProduct_mulVec_ofReal`: the real part of the quadratic form of a matrix over
  `𝕜` on a real vector is the quadratic form of its entrywise real part.
- `Matrix.PosSemidef.map_re`: the entrywise real part of a positive-semidefinite matrix.
- `Matrix.re_star_dotProduct_map_ofReal_mulVec`: the real part of the quadratic form of a real
  matrix on a vector over `𝕜`, split along the real and imaginary parts of the vector.
- `Matrix.posSemidef_map_ofReal_iff`: positive semidefiniteness is unchanged by `ℝ → 𝕜`.

## Implementation notes

These lemmas are stated for a general index type rather than for `Fin n`, and are candidates
for upstreaming to `Mathlib/Analysis/Matrix/PosDef.lean`.
-/

@[expose] public section

namespace Matrix

variable {n : Type*}

section RCLike

open RCLike
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The diagonal entries of a positive-semidefinite matrix have nonnegative real part. -/
lemma PosSemidef.re_apply_self_nonneg {M : Matrix n n 𝕜} (hM : M.PosSemidef) (i : n) :
    0 ≤ re (M i i) :=
  (RCLike.nonneg_iff.mp hM.diag_nonneg).1

/-- **Entrywise arithmetic-mean bound for a positive-semidefinite matrix.**
Twice the norm of an entry is bounded by the sum of the (real) diagonal entries of its row and
column. This is the arithmetic-mean form of the Cauchy-Schwarz bound
`Matrix.PosSemidef.normSq_le`. Stated multiplied out, without a division, so that it applies with
no field side conditions. -/
lemma PosSemidef.two_mul_norm_apply_le {M : Matrix n n 𝕜} (hM : M.PosSemidef)
    (i j : n) : 2 * ‖M i j‖ ≤ re (M i i) + re (M j j) := by
  have hi := hM.re_apply_self_nonneg i
  have hj := hM.re_apply_self_nonneg j
  have hcs := hM.normSq_le i j
  rw [RCLike.normSq_eq_def'] at hcs
  nlinarith [sq_nonneg (re (M i i) - re (M j j)), norm_nonneg (M i j)]

/-- The real part of the quadratic form of a matrix over `𝕜` on a real vector, coerced to `𝕜`,
is the quadratic form of the entrywise real part of the matrix on that vector. -/
lemma re_star_dotProduct_mulVec_ofReal [Fintype n] (M : Matrix n n 𝕜) (x : n → ℝ) :
    re (star (fun i => (x i : 𝕜)) ⬝ᵥ (M *ᵥ fun i => (x i : 𝕜))) = x ⬝ᵥ (M.map re *ᵥ x) := by
  simp only [dotProduct, mulVec, map_apply, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal,
    map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, mul_zero, sub_zero]

/-- The entrywise real part of a positive-semidefinite matrix is positive semidefinite: its
quadratic form on a real vector is the real part of the quadratic form of the matrix
(`Matrix.re_star_dotProduct_mulVec_ofReal`). -/
lemma PosSemidef.map_re {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    (M.map re).PosSemidef := by
  classical
  refine ⟨hM.1.map re fun z => by simp, fun x => ?_⟩
  have hM' := hM.submatrix ((↑) : x.support → n)
  have h : ((M.submatrix ((↑) : x.support → n) (↑)).map re).PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hM'.1.map re fun z => by simp, fun y => ?_⟩
    exact (hM'.re_dotProduct_nonneg _).trans_eq (re_star_dotProduct_mulVec_ofReal _ y)
  simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using h.2 _

/-- The real part of the quadratic form of a real matrix, coerced to `𝕜`, is the sum of its real
quadratic forms on the real and imaginary parts of the vector. -/
lemma re_star_dotProduct_map_ofReal_mulVec [Fintype n] (M : Matrix n n ℝ) (x : n → 𝕜) :
    re (star x ⬝ᵥ (M.map ((↑) : ℝ → 𝕜) *ᵥ x)) =
      (fun i => re (x i)) ⬝ᵥ (M *ᵥ fun i => re (x i)) +
        (fun i => im (x i)) ⬝ᵥ (M *ᵥ fun i => im (x i)) := by
  simp only [dotProduct, mulVec, map_apply, Pi.star_apply, RCLike.star_def, map_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im]
  ring

/-- A real matrix is positive semidefinite if and only if its image under the coercion
`ℝ → 𝕜` is. -/
lemma posSemidef_map_ofReal_iff {M : Matrix n n ℝ} :
    (M.map ((↑) : ℝ → 𝕜)).PosSemidef ↔ M.PosSemidef := by
  refine ⟨fun h => by simpa [Matrix.map_map, Function.comp_def] using h.map_re, fun h => ?_⟩
  classical
  refine ⟨h.1.map _ fun x => by simp, fun x => ?_⟩
  have hM' := h.submatrix ((↑) : x.support → n)
  have hH : ((M.submatrix ((↑) : x.support → n) (↑)).map ((↑) : ℝ → 𝕜)).IsHermitian :=
    hM'.1.map _ fun z => by simp
  have h' : ((M.submatrix ((↑) : x.support → n) (↑)).map ((↑) : ℝ → 𝕜)).PosSemidef := by
    refine posSemidef_iff_dotProduct_mulVec.mpr ⟨hH, fun y => ?_⟩
    rw [RCLike.nonneg_iff, re_star_dotProduct_map_ofReal_mulVec]
    exact ⟨add_nonneg (by simpa using hM'.dotProduct_mulVec_nonneg _)
      (by simpa using hM'.dotProduct_mulVec_nonneg _), hH.im_star_dotProduct_mulVec_self y⟩
  simpa [Finsupp.sum, ← Finset.sum_attach x.support, ← Finset.subtype_mem_eq_attach,
    ← Finsupp.subtypeDomain_apply, ← Finsupp.support_subtypeDomain] using h'.2 _

end RCLike

/-- **Entrywise geometric-mean bound for a real positive-semidefinite matrix.**
The square of an entry is bounded by the product of the two diagonal entries of its row and
column: the real form of the scalar Cauchy-Schwarz inequality `Matrix.PosSemidef.normSq_le`. -/
lemma PosSemidef.sq_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    M i j ^ 2 ≤ M i i * M j j := by
  simpa [RCLike.normSq_apply, sq] using hM.normSq_le i j

/-- **Entrywise arithmetic-mean bound for a real positive-semidefinite matrix.**
Twice the absolute value of an entry is bounded by the sum of the two diagonal entries of its
row and column. This is the arithmetic-mean consequence (via AM-GM) of nonnegativity of the
principal `2 × 2` minor on `{i, j}`. It is the case `𝕜 = ℝ` of
`Matrix.PosSemidef.two_mul_norm_apply_le`.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  simpa using hM.two_mul_norm_apply_le i j

end Matrix
