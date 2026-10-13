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
is Mathlib's `Matrix.PosSemidef.diag_nonneg`. This is the form in which positivity constraints are
used in hadronic physics; see `EpsilonEridani/Particles/Parton/PDF/Positivity.lean` for the Soffer
bound on the quark transversity distribution, which is exactly this inequality applied to the
parton spin-density matrix.

A real matrix is positive semidefinite exactly when its image under the coercion `ℝ → 𝕜` is, which
is what lets a complex positive-semidefinite matrix with real entries descend to a real one.

## Main results

- `Matrix.PosSemidef.re_apply_self_nonneg`: nonnegativity of the real part of the diagonal.
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

/-- A real matrix is positive semidefinite if and only if its image under the coercion
`ℝ → 𝕜` is. -/
lemma posSemidef_map_ofReal_iff [Finite n] {M : Matrix n n ℝ} :
    (M.map ((↑) : ℝ → 𝕜)).PosSemidef ↔ M.PosSemidef := by
  have := Fintype.ofFinite n
  have hstar : Function.Semiconj ((↑) : ℝ → 𝕜) star star := fun x => by simp
  simp only [posSemidef_iff_dotProduct_mulVec, isHermitian_map_iff hstar RCLike.ofReal_injective]
  refine and_congr_right fun hM => ⟨fun h x => ?_, fun h x => ?_⟩
  · -- Test the form over `𝕜` on the real vector `x`.
    have hx := h (fun i => (x i : 𝕜))
    simp only [dotProduct, mulVec, map_apply, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal,
      star_trivial] at hx ⊢
    exact_mod_cast hx
  · -- Split `x` into its real and imaginary parts; the cross terms cancel by symmetry of `M`.
    have hsym : ∀ i j, M j i = M i j := fun i j => by simpa using hM.apply i j
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
row and column. This is the arithmetic-mean consequence (via AM-GM) of nonnegativity of the
principal `2 × 2` minor on `{i, j}`. It is the case `𝕜 = ℝ` of
`Matrix.PosSemidef.two_mul_norm_apply_le`.

Stated multiplied out, without a division, so that it applies with no field side conditions. -/
lemma PosSemidef.two_mul_abs_apply_le {M : Matrix n n ℝ} (hM : M.PosSemidef) (i j : n) :
    2 * |M i j| ≤ M i i + M j j := by
  simpa using hM.two_mul_norm_apply_le i j

end Matrix
