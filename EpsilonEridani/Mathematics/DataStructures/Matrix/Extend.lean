/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Data.Matrix.Mul
/-!

# Dot products with a vector extended by zero

For an injective `e : κ → ι`, the vector `Function.extend e c 0 : ι → R` places the entries of
`c : κ → R` on the range of `e` and is zero elsewhere. Pairing it with any vector therefore only
sees the entries on the range of `e`. This file records that fact for `⬝ᵥ` and for quadratic
forms; it is the linear algebra relating a quadratic form on a reindexed family to the quadratic
form on the whole family.

## Main results

* `Matrix.extend_dotProduct`, `Matrix.dotProduct_extend`:
  `Function.extend e c 0 ⬝ᵥ f = c ⬝ᵥ (f ∘ e)` and its mirror image.
* `Matrix.extend_dotProduct_mulVec_extend`: the quadratic form of `M` on
  `Function.extend e c 0` is the quadratic form of `M.submatrix e e` on `c`.
-/

public section

namespace Matrix

open Function

variable {ι κ m R : Type*} [Fintype ι] [Fintype κ] [NonUnitalNonAssocSemiring R] {e : κ → ι}

/-- Pairing a vector extended by zero along an injection with `f` only sees `f` on the range. -/
theorem extend_dotProduct (he : Injective e) (c : κ → R) (f : ι → R) :
    extend e c 0 ⬝ᵥ f = c ⬝ᵥ (f ∘ e) := by
  simp only [dotProduct]
  exact (Fintype.sum_of_injective e he _ _
    (fun i hi => by simp [extend_apply' _ _ _ (by simpa using hi)])
    (fun k => by simp [he.extend_apply])).symm

/-- Pairing `f` with a vector extended by zero along an injection only sees `f` on the range. -/
theorem dotProduct_extend (he : Injective e) (f : ι → R) (c : κ → R) :
    f ⬝ᵥ extend e c 0 = (f ∘ e) ⬝ᵥ c := by
  simp only [dotProduct]
  exact (Fintype.sum_of_injective e he _ _
    (fun i hi => by simp [extend_apply' _ _ _ (by simpa using hi)])
    (fun k => by simp [he.extend_apply])).symm

/-- The quadratic form of a matrix on a vector extended by zero along an injection is the quadratic
form of the submatrix along the injection on the vector. -/
theorem extend_dotProduct_mulVec_extend (he : Injective e) (M : Matrix ι ι R)
    (c : κ → R) : extend e c 0 ⬝ᵥ M *ᵥ extend e c 0 = c ⬝ᵥ M.submatrix e e *ᵥ c := by
  rw [extend_dotProduct he]
  congr 1
  funext k
  simp [mulVec, dotProduct_extend he, comp_def]

end Matrix
