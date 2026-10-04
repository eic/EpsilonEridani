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

The principal `2 × 2` minors of a real positive-semidefinite matrix `M` carry two entrywise
bounds:

* `Matrix.PosSemidef.apply_self_nonneg`: `0 ≤ M i i`;
* `Matrix.PosSemidef.two_mul_abs_apply_le`: `2 * |M i j| ≤ M i i + M j j`.

The second is the arithmetic-mean form of the Cauchy-Schwarz inequality
`(M i j) ^ 2 ≤ M i i * M j j` for a positive-semidefinite matrix. It is stated multiplied out,
with no division, so that it applies without field side conditions. This is the form in which
positivity constraints are used in hadronic physics; see
`EpsilonEridani/Particles/Parton/PDF/Positivity.lean` for the Soffer bound on the quark
transversity distribution, which is exactly this inequality applied to the parton spin-density
matrix.

Evaluating the quadratic form of `M` on the test vector `e i + ε • e j` gives a nonnegative
quadratic polynomial in `ε` for every pair of indices `i, j`; at `ε = 0` it is the first bound.

Over `RCLike 𝕜` the same bounds hold with `‖·‖` in place of `|·|` and the real part of the
(real) diagonal entries in place of the entries themselves. The arithmetic-mean bound follows
from the Cauchy-Schwarz bound `Matrix.PosSemidef.normSq_le` of
`TauCeti.Analysis.Matrix.PosSemidef`, and the real statement above is its specialisation to
`𝕜 = ℝ`. A real matrix is positive semidefinite exactly when its image under the coercion
`ℝ → 𝕜` is, which is what lets a complex positive-semidefinite matrix with real entries descend
to a real one.

## Main results

- `Matrix.PosSemidef.quadraticForm_nonneg`: the quadratic form written as an iterated sum.
- `Matrix.PosSemidef.quadraticForm_psdTestVector`: nonnegativity on `e i + ε • e j`.
- `Matrix.PosSemidef.apply_self_nonneg`: nonnegativity of the diagonal.
- `Matrix.PosSemidef.two_mul_norm_apply_le`: the entrywise arithmetic-mean bound over `RCLike`.
- `Matrix.PosSemidef.two_mul_abs_apply_le`: its real specialisation.
- `Matrix.posSemidef_map_ofReal_iff`: positive semidefiniteness is unchanged by `ℝ → 𝕜`.

## Implementation notes

These lemmas are stated for a general index type rather than for `Fin n`, and are candidates
for upstreaming to `Mathlib/Analysis/Matrix/PosDef.lean`.
-/

@[expose] public section

namespace Matrix

open scoped BigOperators

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

section RCLike

open RCLike
open scoped ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜]

/-- **Entrywise arithmetic-mean bound for a positive-semidefinite matrix.**
Twice the norm of an entry is bounded by the sum of the (real) diagonal entries of its row and
column. This is the arithmetic-mean form of the Cauchy-Schwarz bound
`Matrix.PosSemidef.normSq_le`. Stated multiplied out, without a division, so that it applies with
no field side conditions. -/
lemma PosSemidef.two_mul_norm_apply_le {M : Matrix n n 𝕜} (hM : M.PosSemidef)
    (i j : n) : 2 * ‖M i j‖ ≤ re (M i i) + re (M j j) := by
  have hi := (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := i))).1
  have hj := (RCLike.nonneg_iff.mp (hM.diag_nonneg (i := j))).1
  have hcs := hM.normSq_le i j
  rw [RCLike.normSq_eq_def'] at hcs
  nlinarith [sq_nonneg (re (M i i) - re (M j j)), norm_nonneg (M i j)]

/-- A real matrix is positive semidefinite if and only if its image under the coercion
`ℝ → 𝕜` is. The forward direction tests the complex form on real vectors; the reverse direction
splits a vector into its real and imaginary parts, whose cross terms cancel because a real
hermitian matrix is symmetric. -/
lemma posSemidef_map_ofReal_iff [Finite n] {M : Matrix n n ℝ} :
    (M.map ((↑) : ℝ → 𝕜)).PosSemidef ↔ M.PosSemidef := by
  have := Fintype.ofFinite n
  have hstar : Function.Semiconj ((↑) : ℝ → 𝕜) star star := fun x => by simp
  simp only [posSemidef_iff_dotProduct_mulVec, isHermitian_map_iff hstar RCLike.ofReal_injective]
  refine and_congr_right fun hM => ⟨fun h x => ?_, fun h x => ?_⟩
  · have hx := h (fun i => (x i : 𝕜))
    simp only [dotProduct, mulVec, map_apply, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal,
      star_trivial] at hx ⊢
    exact_mod_cast hx
  · have hsym : ∀ i j, M j i = M i j := fun i j => by simpa using hM.apply i j
    have hq := h (fun i => re (x i))
    have hq' := h (fun i => im (x i))
    rw [RCLike.nonneg_iff]
    simp only [dotProduct, mulVec, map_apply, Pi.star_apply, star_trivial, RCLike.star_def,
      map_sum, Finset.mul_sum, mul_re, mul_im, conj_re, conj_im, ofReal_re, ofReal_im, zero_mul,
      sub_zero, add_zero] at hq hq' ⊢
    constructor
    · convert add_nonneg hq hq' using 1
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    · -- The imaginary part is the antisymmetric cross term, which vanishes since `M` is symmetric.
      have hswap : ∑ i, ∑ j, im (x i) * (M i j * re (x j)) =
          ∑ i, ∑ j, re (x i) * (M i j * im (x j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]; ring
      simp only [neg_mul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
      rw [hswap, sub_self]

end RCLike

/-- **Entrywise arithmetic-mean bound for a real positive-semidefinite matrix.**
Twice the absolute value of an entry is bounded by the sum of the two diagonal entries of its
row and column. Equivalently: the principal `2 × 2` minor on `{i, j}` is nonnegative, in the
arithmetic-mean rather than the geometric-mean form. This is the case `𝕜 = ℝ` of
`Matrix.PosSemidef.two_mul_norm_apply_le`.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  simpa using hM.two_mul_norm_apply_le i j

end Matrix
