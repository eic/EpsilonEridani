/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith


/-!
# Entrywise bounds for real positive-semidefinite matrices

Evaluating the quadratic form of a real positive-semidefinite matrix `M` on the test vector
`e i + ε • e j` gives a nonnegative quadratic polynomial in `ε` for every pair of indices
`i, j`. Specialising `ε` to `0` and to `±1` yields the two entrywise bounds carried by the
principal `2 × 2` minors:

* `Matrix.PosSemidef.apply_self_nonneg`: `0 ≤ M i i`;
* `Matrix.PosSemidef.two_mul_abs_apply_le`: `2 * |M i j| ≤ M i i + M j j`.

The second is the arithmetic-mean form of the Cauchy-Schwarz inequality
`(M i j) ^ 2 ≤ M i i * M j j` for a positive-semidefinite matrix. It is stated multiplied out,
with no division, so that it applies without field side conditions. This is the form in which
positivity constraints are used in hadronic physics; see
`Physlib/Particles/Parton/PDF/Positivity.lean` for the Soffer bound on the quark transversity
distribution, which is exactly this inequality applied to the parton spin-density matrix.

Real positive-semidefinite matrices also arise as real parts of complex ones: for a Hermitian
`M` and a real vector `x`, `xᵀ (Re M) x = Re (xᴴ M x)`, so `Matrix.PosSemidef.map_re` passes from
a positive-semidefinite matrix over an `RCLike` field to its entrywise real part. This is how a
real kernel such as `exp (-c ‖a - b‖²)` inherits positivity from its complex counterpart.

## Main results

- `Matrix.PosSemidef.quadraticForm_nonneg`: the quadratic form written as an iterated sum.
- `Matrix.PosSemidef.quadraticForm_psdTestVector`: nonnegativity on `e i + ε • e j`.
- `Matrix.PosSemidef.apply_self_nonneg`: nonnegativity of the diagonal.
- `Matrix.PosSemidef.two_mul_abs_apply_le`: the entrywise arithmetic-mean bound.
- `Matrix.PosSemidef.map_re`: the entrywise real part of a positive-semidefinite matrix over an
  `RCLike` field is positive semidefinite.

## Implementation notes

Everything here is stated over `ℝ`, with an `RCLike` matrix only as the input of
`Matrix.PosSemidef.map_re`. `Matrix.PosSemidef` is available over more general
star-ordered rings, and the corresponding statements over `RCLike 𝕜` replace `|·|` by `‖·‖`;
that generalisation is not needed for the leading-twist positivity bounds (whose relevant
block is real) and is left to whoever first needs the T-odd, genuinely complex entries.

These lemmas are stated for a general index type rather than for `Fin n`, and are candidates
for upstreaming to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators ComplexOrder

variable {n : Type*}

/-- The test vector `e i + ε • e j`: it takes the value `1` at `i`, the value `ε` at `j`, and
`0` elsewhere. For `i = j` it degenerates to `(1 + ε) • e i`, which is harmless: every lemma
below holds without an `i ≠ j` hypothesis. -/
def psdTestVector [DecidableEq n] {R : Type*} [Semiring R] (i j : n) (ε : R) : n → R :=
  fun k => (if k = i then 1 else 0) + ε * (if k = j then 1 else 0)

/-- Contracting a function `g` against the test vector on the right picks out `g i + ε * g j`. -/
lemma sum_mul_psdTestVector [Fintype n] [DecidableEq n] (g : n → ℝ) (i j : n) (ε : ℝ) :
    ∑ l, g l * psdTestVector i j ε l = g i + ε * g j := by
  have hterm : ∀ l : n, g l * psdTestVector i j ε l
      = (if l = i then g l else 0) + (if l = j then ε * g l else 0) := by
    intro l
    simp only [psdTestVector, mul_add]
    by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [h1, h2] <;> ring_nf
  calc ∑ l, g l * psdTestVector i j ε l
      = ∑ l, ((if l = i then g l else 0) + (if l = j then ε * g l else 0)) :=
        Finset.sum_congr rfl fun l _ => hterm l
    _ = (∑ l, if l = i then g l else 0) + ∑ l, if l = j then ε * g l else 0 :=
        Finset.sum_add_distrib
    _ = g i + ε * g j := by simp

/-- Contracting a function `g` against the test vector on the left picks out `g i + ε * g j`. -/
lemma sum_psdTestVector_mul [Fintype n] [DecidableEq n] (g : n → ℝ) (i j : n) (ε : ℝ) :
    ∑ l, psdTestVector i j ε l * g l = g i + ε * g j := by
  calc ∑ l, psdTestVector i j ε l * g l = ∑ l, g l * psdTestVector i j ε l :=
        Finset.sum_congr rfl fun l _ => mul_comm _ _
    _ = g i + ε * g j := sum_mul_psdTestVector g i j ε

/-- The quadratic form of a real positive-semidefinite matrix, written as an iterated sum. -/
lemma PosSemidef.quadraticForm_nonneg [Fintype n] {M : Matrix n n ℝ} (hM : M.PosSemidef)
    (w : n → ℝ) :
    0 ≤ ∑ k, w k * ∑ l, M k l * w l := by
  -- At this pin, `Matrix.PosSemidef` is defined via `Finsupp.sum` over `n →₀ ℝ` (not a plain
  -- `∀ w : n → ℝ` dot product), so `hM.2 w` does not typecheck as the dot-product statement.
  -- The `[Fintype n]` bridge is `Matrix.PosSemidef.dotProduct_mulVec_nonneg`
  -- (`Mathlib/LinearAlgebra/Matrix/PosDef.lean`), which is exactly `∀ x : n → R,
  -- 0 ≤ star x ⬝ᵥ (M *ᵥ x)` — confirmed by reading the pinned mathlib source directly.
  simpa [dotProduct, mulVec, Pi.star_apply, star_trivial] using hM.dotProduct_mulVec_nonneg w

/-- Nonnegativity of the quadratic form of a real positive-semidefinite matrix on the test
vector `e i + ε • e j`, expanded as a quadratic polynomial in `ε`. -/
lemma PosSemidef.quadraticForm_psdTestVector [Finite n] {M : Matrix n n ℝ} (hM : M.PosSemidef)
    (i j : n) (ε : ℝ) :
    0 ≤ M i i + ε * (M i j + M j i) + ε ^ 2 * M j j := by
  have := Fintype.ofFinite n
  classical
  have h := hM.quadraticForm_nonneg (psdTestVector i j ε)
  have hinner : ∀ k : n, ∑ l, M k l * psdTestVector i j ε l = M k i + ε * M k j :=
    fun k => sum_mul_psdTestVector (fun l => M k l) i j ε
  have hstep : ∑ k, psdTestVector i j ε k * ∑ l, M k l * psdTestVector i j ε l
      = (M i i + ε * M i j) + ε * (M j i + ε * M j j) := by
    calc ∑ k, psdTestVector i j ε k * ∑ l, M k l * psdTestVector i j ε l
        = ∑ k, psdTestVector i j ε k * (M k i + ε * M k j) :=
          Finset.sum_congr rfl fun k _ => by rw [hinner k]
      _ = (M i i + ε * M i j) + ε * (M j i + ε * M j j) :=
          sum_psdTestVector_mul (fun k => M k i + ε * M k j) i j ε
  rw [hstep] at h
  have hring : M i i + ε * (M i j + M j i) + ε ^ 2 * M j j
      = (M i i + ε * M i j) + ε * (M j i + ε * M j j) := by ring_nf
  rw [hring]
  exact h

/-- The diagonal entries of a real positive-semidefinite matrix are nonnegative. -/
lemma PosSemidef.apply_self_nonneg [Finite n] {M : Matrix n n ℝ} (hM : M.PosSemidef) (i : n) :
    0 ≤ M i i := by
  have := Fintype.ofFinite n
  classical
  linarith [hM.quadraticForm_psdTestVector i i 0]

/-- **Entrywise arithmetic-mean bound for a real positive-semidefinite matrix.**
Twice the absolute value of an entry is bounded by the sum of the two diagonal entries of its
row and column. Equivalently: the principal `2 × 2` minor on `{i, j}` is nonnegative, in the
arithmetic-mean rather than the geometric-mean form.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le [Finite n] {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  have := Fintype.ofFinite n
  classical
  have hsymm : M j i = M i j := by
    -- `Matrix.IsHermitian.apply (h) (i j) : star (A j i) = A i j` — confirmed against the
    -- pinned mathlib source (`Mathlib/LinearAlgebra/Matrix/Hermitian.lean`); over `ℝ` the
    -- star is trivial, so `hM.1.apply i j` is exactly `M j i = M i j`, the stated goal.
    simpa using hM.1.apply i j
  have hplus := hM.quadraticForm_psdTestVector i j 1
  have hminus := hM.quadraticForm_psdTestVector i j (-1)
  rw [hsymm] at hplus hminus
  rcases abs_cases (M i j) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;> linarith

/-- The entrywise real part of a positive-semidefinite matrix over an `RCLike` field is a real
positive-semidefinite matrix: on a real vector its quadratic form is the real part of the
quadratic form of `M`. The index type is arbitrary. -/
theorem PosSemidef.map_re {𝕜 : Type*} [RCLike 𝕜] {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    (M.map RCLike.re).PosSemidef := by
  refine ⟨IsHermitian.ext fun i j => ?_, fun x => ?_⟩
  · rw [map_apply, map_apply, star_trivial, ← hM.isHermitian.apply i j, RCLike.star_def,
      RCLike.conj_re]
  · -- Evaluate the quadratic form of `M` on `x` viewed as a vector over `𝕜`.
    have h := (RCLike.nonneg_iff.mp (hM.2 (x.mapRange ((↑) : ℝ → 𝕜) (by simp)))).1
    rw [Finsupp.sum_mapRange_index (by simp)] at h
    have key (a : n) (b : ℝ) : ((x.mapRange ((↑) : ℝ → 𝕜) (by simp)).sum fun j yj =>
        star (b : 𝕜) * M a j * yj) = x.sum fun j xj => star (b : 𝕜) * M a j * xj :=
      Finsupp.sum_mapRange_index fun _ => mul_zero _
    simp only [key] at h
    simp only [Finsupp.sum, map_sum, RCLike.star_def, RCLike.conj_ofReal,
      RCLike.re_ofReal_mul, RCLike.re_mul_ofReal] at h
    simpa only [Finsupp.sum, map_apply, star_trivial] using h

end Matrix
