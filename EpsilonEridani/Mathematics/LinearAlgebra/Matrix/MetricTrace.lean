/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry

/-!
# The trace and traceless parts of a tensor with respect to a metric

A tensor `T_{μν}` with two lower indices on a space of dimension `D` with metric `g_{μν}` has the
trace `T^α{}_α = g^{αβ} T_{αβ}`, which for matrices is `trace (g⁻¹ * T)`. It splits uniquely as
`T_{μν} = (1/D) g_{μν} T^α{}_α + S_{μν}`, the sum of a multiple of the metric and a tensor `S`
whose trace vanishes. This file defines the two projections

* `Matrix.tracePart g T = (trace (g⁻¹ * T) / D) • g`, and
* `Matrix.tracelessPart g T = T - Matrix.tracePart g T`,

as linear endomorphisms of the space of matrices, and proves that in a dimension invertible in
the scalars they are complementary idempotents, whose ranges are, for an invertible metric, the
multiples of `g` and the traceless tensors. Both commute with every transformation preserving the
metric, and preserve symmetry when `g` is symmetric. In relativistic field theory this is the
split of an energy-momentum tensor into the part that carries the trace anomaly and the
traceless part that carries the twist-two operators.

The conventions for tensors with lower indices, the metric `g` and its inverse are those of
`EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry`: `g⁻¹` is the inverse of
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, and a transformation `Λ` acts on lower indices
by `T ↦ Λᵀ * T * Λ` and preserves `g` when `Λᵀ * g * Λ = g`.

## Main definitions

* `Matrix.tracePart g`: the projection `T ↦ (1/D) g T^α{}_α` onto the multiples of the metric.
* `Matrix.tracelessPart g`: the complementary projection `T ↦ T - (1/D) g T^α{}_α`.

## Main statements

* `Matrix.tracePart_add_tracelessPart`: `T` is the sum of its two parts.
* `Matrix.trace_inv_mul_tracePart` and `Matrix.trace_inv_mul_tracelessPart`: the trace part
  carries the whole trace and the traceless part has none.
* `Matrix.tracePart_smul_add` and `Matrix.tracelessPart_smul_add`: the decomposition is unique,
  since a multiple of `g` plus a traceless tensor is split into exactly those two summands.
* `Matrix.isIdempotentElem_tracePart`, `Matrix.isIdempotentElem_tracelessPart`: both are
  projections, and `Matrix.tracePart_tracelessPart`, `Matrix.tracelessPart_tracePart` say they
  annihilate each other's ranges.
* `Matrix.tracePart_eq_zero_iff` and `Matrix.tracelessPart_eq_zero_iff`: the kernels are the
  traceless tensors and the multiples of `g`.
* `Matrix.tracePart_equivariant`, `Matrix.tracelessPart_equivariant`: both parts transform as
  tensors under transformations preserving the metric.

## References

* X. Ji, *Phys. Rev. Lett.* **74** (1995) 1071, arXiv:hep-ph/9410274, for the split of the
  energy-momentum tensor into its trace and traceless parts.
-/

public section

noncomputable section

namespace Matrix

open EpsilonEridani

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- The trace part `(1/D) g_{μν} T^α{}_α = (trace (g⁻¹ * T) / D) • g` of a tensor `T` with two
lower indices, with respect to the metric `g`, in dimension `D = card n`. -/
def tracePart (g : Matrix n n K) : Module.End K (Matrix n n K) where
  toFun T := (trace (g⁻¹ * T) / Fintype.card n) • g
  map_add' T S := by simp only [Matrix.mul_add, trace_add, add_div, add_smul]
  map_smul' c T := by
    simp only [Matrix.mul_smul, trace_smul, smul_eq_mul, mul_div_assoc, smul_smul,
      RingHom.id_apply]

lemma tracePart_apply (g T : Matrix n n K) :
    tracePart g T = (trace (g⁻¹ * T) / Fintype.card n) • g := (rfl)

/-- The traceless part `T_{μν} - (1/D) g_{μν} T^α{}_α` of a tensor `T` with two lower indices,
with respect to the metric `g`, in dimension `D = card n`. -/
def tracelessPart (g : Matrix n n K) : Module.End K (Matrix n n K) :=
  1 - tracePart g

lemma tracelessPart_eq_one_sub (g : Matrix n n K) : tracelessPart g = 1 - tracePart g := (rfl)

lemma tracelessPart_apply (g T : Matrix n n K) : tracelessPart g T = T - tracePart g T := (rfl)

/-- A tensor is the sum of its trace part and its traceless part. -/
@[simp]
theorem tracePart_add_tracelessPart (g T : Matrix n n K) :
    tracePart g T + tracelessPart g T = T := by
  rw [tracelessPart_apply, add_sub_cancel]

variable {g : Matrix n n K}

/-- The trace part of a tensor carries its whole trace. -/
@[simp]
theorem trace_inv_mul_tracePart (hn : (Fintype.card n : K) ≠ 0)
    (T : Matrix n n K) : trace (g⁻¹ * tracePart g T) = trace (g⁻¹ * T) := by
  rcases eq_or_ne g.det 0 with hg | hg
  · -- For a singular metric `g⁻¹ = 0`, and both traces vanish.
    simp [nonsing_inv_apply_not_isUnit g (by simpa using hg)]
  · rw [tracePart_apply, Matrix.mul_smul, nonsing_inv_mul g (isUnit_iff_ne_zero.2 hg), trace_smul,
      trace_one, smul_eq_mul, div_mul_cancel₀ _ hn]

/-- The traceless part of a tensor is traceless. -/
@[simp]
theorem trace_inv_mul_tracelessPart (hn : (Fintype.card n : K) ≠ 0)
    (T : Matrix n n K) : trace (g⁻¹ * tracelessPart g T) = 0 := by
  rw [tracelessPart_apply, Matrix.mul_sub, trace_sub, trace_inv_mul_tracePart hn, sub_self]

/-- The trace part of a multiple of the metric plus a traceless tensor is that multiple of the
metric. With `tracelessPart_smul_add`, this says that the decomposition of a tensor into a
multiple of the metric and a traceless tensor is unique. -/
theorem tracePart_smul_add (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0) (c : K)
    {S : Matrix n n K} (hS : trace (g⁻¹ * S) = 0) : tracePart g (c • g + S) = c • g := by
  rw [tracePart_apply, Matrix.mul_add, Matrix.mul_smul, nonsing_inv_mul g (isUnit_iff_ne_zero.2 hg),
    trace_add, trace_smul, hS, trace_one, smul_eq_mul, add_zero, mul_div_cancel_right₀ _ hn]

/-- The traceless part of a multiple of the metric plus a traceless tensor is that traceless
tensor. -/
theorem tracelessPart_smul_add (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0) (c : K)
    {S : Matrix n n K} (hS : trace (g⁻¹ * S) = 0) : tracelessPart g (c • g + S) = S := by
  rw [tracelessPart_apply, tracePart_smul_add hg hn c hS, add_sub_cancel_left]

/-- The metric is its own trace part. -/
@[simp]
theorem tracePart_self (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0) :
    tracePart g g = g := by
  simpa using tracePart_smul_add hg hn 1 (S := 0) (by simp)

/-- The metric has no traceless part. -/
@[simp]
theorem tracelessPart_self (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0) :
    tracelessPart g g = 0 := by
  rw [tracelessPart_apply, tracePart_self hg hn, sub_self]

/-- Taking the trace part twice is taking it once. -/
@[simp]
theorem tracePart_tracePart (hn : (Fintype.card n : K) ≠ 0)
    (T : Matrix n n K) : tracePart g (tracePart g T) = tracePart g T := by
  rw [tracePart_apply g (tracePart g T), trace_inv_mul_tracePart hn, ← tracePart_apply]

/-- The trace part of a traceless part vanishes. -/
@[simp]
theorem tracePart_tracelessPart (hn : (Fintype.card n : K) ≠ 0)
    (T : Matrix n n K) : tracePart g (tracelessPart g T) = 0 := by
  rw [tracelessPart_apply, map_sub, tracePart_tracePart hn, sub_self]

/-- The traceless part of a trace part vanishes. -/
@[simp]
theorem tracelessPart_tracePart (hn : (Fintype.card n : K) ≠ 0)
    (T : Matrix n n K) : tracelessPart g (tracePart g T) = 0 := by
  rw [tracelessPart_apply, tracePart_tracePart hn, sub_self]

/-- Taking the traceless part twice is taking it once. -/
@[simp]
theorem tracelessPart_tracelessPart (hn : (Fintype.card n : K) ≠ 0)
    (T : Matrix n n K) : tracelessPart g (tracelessPart g T) = tracelessPart g T := by
  rw [tracelessPart_apply g (tracelessPart g T), tracePart_tracelessPart hn, sub_zero]

/-- The trace part is a projection. -/
theorem isIdempotentElem_tracePart (hn : (Fintype.card n : K) ≠ 0) :
    IsIdempotentElem (tracePart g) :=
  LinearMap.ext fun T => by rw [Module.End.mul_apply, tracePart_tracePart hn]

/-- The traceless part is a projection, complementary to the trace part. -/
theorem isIdempotentElem_tracelessPart (hn : (Fintype.card n : K) ≠ 0) :
    IsIdempotentElem (tracelessPart g) :=
  (isIdempotentElem_tracePart hn).one_sub

/-- The trace part of a tensor vanishes exactly when the tensor is traceless. -/
theorem tracePart_eq_zero_iff (hn : (Fintype.card n : K) ≠ 0)
    {T : Matrix n n K} : tracePart g T = 0 ↔ trace (g⁻¹ * T) = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [tracePart_apply, h, zero_div, zero_smul]⟩
  rw [← trace_inv_mul_tracePart hn, h, Matrix.mul_zero, trace_zero]

/-- A tensor is its own traceless part exactly when it is traceless. -/
theorem tracelessPart_eq_self_iff (hn : (Fintype.card n : K) ≠ 0)
    {T : Matrix n n K} : tracelessPart g T = T ↔ trace (g⁻¹ * T) = 0 := by
  rw [tracelessPart_apply, sub_eq_self, tracePart_eq_zero_iff hn]

/-- The traceless part of a tensor vanishes exactly when the tensor is a multiple of the
metric. -/
theorem tracelessPart_eq_zero_iff (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0)
    {T : Matrix n n K} : tracelessPart g T = 0 ↔ ∃ c : K, c • g = T := by
  refine ⟨fun h => ⟨trace (g⁻¹ * T) / Fintype.card n, ?_⟩, ?_⟩
  · have hT := tracePart_add_tracelessPart g T
    rwa [h, add_zero, tracePart_apply] at hT
  · rintro ⟨c, rfl⟩
    rw [map_smul, tracelessPart_self hg hn, smul_zero]

/-- The trace part of any tensor is symmetric when the metric is. -/
theorem isSymm_tracePart (hg : g.IsSymm) (T : Matrix n n K) : (tracePart g T).IsSymm := by
  rw [tracePart_apply]
  exact hg.smul _

/-- The traceless part of a symmetric tensor is symmetric when the metric is. -/
theorem isSymm_tracelessPart (hg : g.IsSymm) {T : Matrix n n K} (hT : T.IsSymm) :
    (tracelessPart g T).IsSymm := by
  rw [tracelessPart_apply]
  exact hT.sub (isSymm_tracePart hg T)

/-- The trace part of a tensor transforms as a tensor with two lower indices under a
transformation preserving the metric. -/
theorem tracePart_equivariant {Λ : Matrix n n K} (hΛ : Λᵀ * g * Λ = g) (T : Matrix n n K) :
    tracePart g (Λᵀ * T * Λ) = Λᵀ * tracePart g T * Λ := by
  rw [tracePart_apply, tracePart_apply, trace_inv_mul_transpose_mul_mul hΛ, Matrix.mul_smul,
    Matrix.smul_mul, hΛ]

/-- The traceless part of a tensor transforms as a tensor with two lower indices under a
transformation preserving the metric. -/
theorem tracelessPart_equivariant {Λ : Matrix n n K} (hΛ : Λᵀ * g * Λ = g) (T : Matrix n n K) :
    tracelessPart g (Λᵀ * T * Λ) = Λᵀ * tracelessPart g T * Λ := by
  rw [tracelessPart_apply, tracelessPart_apply, tracePart_equivariant hΛ, Matrix.mul_sub,
    Matrix.sub_mul]

end Matrix
