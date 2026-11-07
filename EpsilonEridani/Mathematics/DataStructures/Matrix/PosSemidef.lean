/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import TauCeti.Analysis.Matrix.PosSemidef


/-!
# Entrywise bounds for real positive-semidefinite matrices

The principal `2 × 2` minors of a real positive-semidefinite matrix `M` are nonnegative. This
file records the resulting entrywise bounds on the off-diagonal entries:

* `Matrix.PosSemidef.sq_apply_le`: `(M i j) ^ 2 ≤ M i i * M j j`, the geometric-mean form of
  the Cauchy-Schwarz inequality (the real case of Tau Ceti's `Matrix.PosSemidef.normSq_le`);
* `Matrix.PosSemidef.two_mul_abs_apply_le`: `2 * |M i j| ≤ M i i + M j j`, its arithmetic-mean
  form.

(Nonnegativity of the diagonal is Mathlib's `Matrix.PosSemidef.diag_nonneg`.)

Both bounds are stated multiplied out, with no division, so that they apply without field side
conditions. This is the form in which positivity constraints are used in hadronic physics; see
`EpsilonEridani/Particles/Parton/PDF/Positivity.lean` for the Soffer bound on the quark
transversity distribution, which is exactly the arithmetic-mean inequality applied to the
parton spin-density matrix.

Real positive-semidefinite matrices also arise as real parts of complex ones: for a Hermitian
`M` and a real vector `x`, `xᵀ (Re M) x = Re (xᴴ M x)`, so `Matrix.PosSemidef.map_re` passes from
a positive-semidefinite matrix over an `RCLike` field to its entrywise real part. This is how a
real kernel such as `exp (-c ‖a - b‖²)` inherits positivity from its complex counterpart.

## Main results

- `Matrix.PosSemidef.sq_apply_le`: the entrywise geometric-mean bound.
- `Matrix.PosSemidef.two_mul_abs_apply_le`: the entrywise arithmetic-mean bound.
- `Matrix.PosSemidef.map_re`: the entrywise real part of a positive-semidefinite matrix over an
  `RCLike` field is positive semidefinite.

## Implementation notes

Everything here is stated over `ℝ`, with an `RCLike` matrix only as the input of
`Matrix.PosSemidef.map_re`. The geometric-mean bound is already available over `RCLike 𝕜`: it
is Tau Ceti's `Matrix.PosSemidef.normSq_le`, of which `sq_apply_le` is the real case. Only the
`|·|`-form `two_mul_abs_apply_le` is specific to `ℝ` here; its `RCLike` version (with `|·|`
replaced by `‖·‖`) is not needed for the leading-twist positivity bounds (whose relevant block
is real) and is left to whoever first needs the T-odd, genuinely complex entries.

These lemmas are stated for a general index type rather than for `Fin n`, and are candidates
for upstreaming to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.
-/

@[expose] public section

namespace Matrix

open scoped ComplexOrder

variable {n : Type*}

/-- **Entrywise geometric-mean bound for a real positive-semidefinite matrix.**
The square of an entry is bounded by the product of the two diagonal entries of its row and
column: the real form of the scalar Cauchy-Schwarz inequality `Matrix.PosSemidef.normSq_le`. -/
lemma PosSemidef.sq_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    M i j ^ 2 ≤ M i i * M j j := by
  simpa [RCLike.normSq_apply, sq] using hM.normSq_le i j

/-- **Entrywise arithmetic-mean bound for a real positive-semidefinite matrix.**
Twice the absolute value of an entry is bounded by the sum of the two diagonal entries of its
row and column. Equivalently: the principal `2 × 2` minor on `{i, j}` is nonnegative, in the
arithmetic-mean rather than the geometric-mean form.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  have := hM.sq_apply_le i j
  have := hM.diag_nonneg (i := i)
  have := hM.diag_nonneg (i := j)
  nlinarith [abs_nonneg (M i j), sq_abs (M i j), sq_nonneg (M i i - M j j)]

/-- The entrywise real part of a positive-semidefinite matrix over an `RCLike` field is a real
positive-semidefinite matrix: on a real vector its quadratic form is the real part of the
quadratic form of `M`. The index type is arbitrary. -/
theorem PosSemidef.map_re {𝕜 : Type*} [RCLike 𝕜] {M : Matrix n n 𝕜} (hM : M.PosSemidef) :
    (M.map RCLike.re).PosSemidef := by
  refine ⟨hM.isHermitian.map RCLike.re fun z => by simp [RCLike.star_def], fun x => ?_⟩
  -- `h` is nonnegativity of `re (yᴴ M y)` for the vector `y` over `𝕜` underlying `x`.
  set y : n →₀ 𝕜 := x.mapRange ((↑) : ℝ → 𝕜) RCLike.ofReal_zero
  have h := (RCLike.nonneg_iff.mp (hM.2 y)).1
  -- Strip the coercion from the outer `Finsupp.sum`, then from the inner one.
  rw [Finsupp.sum_mapRange_index fun _ => by simp] at h
  have inner (a : n) (b : 𝕜) : (y.sum fun j yj => b * M a j * yj) =
      x.sum fun j xj => b * M a j * xj :=
    Finsupp.sum_mapRange_index fun _ => mul_zero _
  -- `re` passes through both sums as an additive map.
  simp only [inner, map_finsuppSum RCLike.re, RCLike.star_def, RCLike.conj_ofReal,
    RCLike.re_ofReal_mul, RCLike.re_mul_ofReal] at h
  simpa only [map_apply, star_trivial] using h

end Matrix
