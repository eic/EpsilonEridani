/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck, The EpsilonEridani contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Bilinear
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Idempotents
public import EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry

/-!
# The trace and traceless parts of a tensor with respect to a metric

A tensor `T_{μν}` with two lower indices on a space of dimension `D` with metric `g_{μν}` has the
trace `T^α{}_α = g^{αβ} T_{αβ}`, which for matrices is `trace (g⁻¹ * T)`. It splits uniquely as
`T_{μν} = (1/D) g_{μν} T^α{}_α + S_{μν}`, the sum of a multiple of the metric and a tensor `S`
whose trace vanishes. This file defines the two projections

* `Matrix.tracePart g T = (trace (g⁻¹ * T) / D) • g`, and
* `Matrix.tracelessPart g T = T - Matrix.tracePart g T`,

as linear endomorphisms of the space of matrices, and proves that they are complementary
idempotents, whose ranges are, in a dimension invertible in the scalars and for an invertible
metric, the multiples of `g` and the traceless tensors. Both commute with every transformation
preserving the metric, and preserve symmetry when `g` is symmetric. In relativistic field theory
this is the split of an energy-momentum tensor into the part that carries the trace anomaly and
the traceless part that carries the twist-two operators. The projector algebra generalizes the
colour singlet and octet projectors `colorSingletProj` and `colorOctetProj` of
`EpsilonEridani.QFT.Quarkonium.NRQCD.ColorDecomposition` from the metric `1` to an arbitrary
metric `g`.

The conventions for tensors with lower indices, the metric `g` and its inverse are those of
`EpsilonEridani.Mathematics.LinearAlgebra.Matrix.Isometry`: `g⁻¹` is the inverse of
`Mathlib.LinearAlgebra.Matrix.NonsingularInverse`, and a transformation `Λ` acts on lower indices
by `T ↦ Λᵀ * T * Λ` and preserves `g` when `Λᵀ * g * Λ = g`.

## Main definitions

* `Matrix.tracePart g`: the projection `T ↦ (1/D) g T^α{}_α` onto the multiples of the metric.
* `Matrix.tracelessPart g`: the complementary projection `T ↦ T - (1/D) g T^α{}_α`.

## Main statements

* `Matrix.tracePart_add_tracelessPart`, `Matrix.tracePart_add_tracelessPart_apply`: `T` is the
  sum of its two parts.
* `Matrix.trace_inv_mul_tracePart` and `Matrix.trace_inv_mul_tracelessPart`: the trace part
  carries the whole trace and the traceless part has none.
* `Matrix.tracePart_smul_add` and `Matrix.tracelessPart_smul_add`: the decomposition is unique,
  since a multiple of `g` plus a traceless tensor is split into exactly those two summands.
* `Matrix.isIdempotentElem_tracePart`, `Matrix.isIdempotentElem_tracelessPart`: both are
  projections, `Matrix.tracePart_tracelessPart`, `Matrix.tracelessPart_tracePart` say they
  annihilate each other's ranges, and
  `Matrix.completeOrthogonalIdempotents_tracePart_tracelessPart` bundles this;
  `Matrix.trace_tracePart` and `Matrix.trace_tracelessPart` give their traces as endomorphisms,
  `1` and `D² - 1`.
* `Matrix.tracePart_eq_zero_iff` and `Matrix.tracelessPart_eq_zero_iff`: the kernels are the
  traceless tensors and the multiples of `g`; `Matrix.tracePart_eq_self_iff` and
  `Matrix.tracelessPart_eq_self_iff` say the ranges are the multiples of `g` and the traceless
  tensors.
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
def tracePart (g : Matrix n n K) : Module.End K (Matrix n n K) :=
  ((Fintype.card n : K)⁻¹ • (traceLinearMap n K K ∘ₗ mulLeftLinearMap n K g⁻¹)).smulRight g

/-- The trace part as the rank-one map `T ↦ (trace (g⁻¹ * T) / D) • g` assembled from
`Matrix.traceLinearMap` and `Matrix.mulLeftLinearMap`. -/
lemma tracePart_def (g : Matrix n n K) :
    tracePart g =
      ((Fintype.card n : K)⁻¹ • (traceLinearMap n K K ∘ₗ mulLeftLinearMap n K g⁻¹)).smulRight g :=
  (rfl)

lemma tracePart_apply (g T : Matrix n n K) :
    tracePart g T = (trace (g⁻¹ * T) / Fintype.card n) • g := by
  rw [tracePart_def, LinearMap.smulRight_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    mulLeftLinearMap_apply, traceLinearMap_apply, smul_eq_mul, div_eq_inv_mul]

/-- The traceless part `T_{μν} - (1/D) g_{μν} T^α{}_α` of a tensor `T` with two lower indices,
with respect to the metric `g`, in dimension `D = card n`. -/
def tracelessPart (g : Matrix n n K) : Module.End K (Matrix n n K) :=
  1 - tracePart g

lemma tracelessPart_eq_one_sub (g : Matrix n n K) : tracelessPart g = 1 - tracePart g := (rfl)

lemma tracelessPart_apply (g T : Matrix n n K) : tracelessPart g T = T - tracePart g T := by
  rw [tracelessPart_eq_one_sub, LinearMap.sub_apply, one_apply_eq_self]

/-- The trace part and the traceless part add up to the identity. -/
@[simp]
theorem tracePart_add_tracelessPart (g : Matrix n n K) : tracePart g + tracelessPart g = 1 := by
  rw [tracelessPart_eq_one_sub, add_sub_cancel]

/-- A tensor is the sum of its trace part and its traceless part. -/
@[simp]
theorem tracePart_add_tracelessPart_apply (g T : Matrix n n K) :
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
      trace_one, smul_eq_mul]
    field_simp

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
    trace_add, trace_smul, hS, trace_one, smul_eq_mul, add_zero]
  congr 1
  field_simp

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
theorem tracePart_tracePart (T : Matrix n n K) : tracePart g (tracePart g T) = tracePart g T := by
  rcases eq_or_ne (Fintype.card n : K) 0 with hn | hn
  · -- In a dimension vanishing in the scalars, the trace part is the zero map.
    simp only [tracePart_apply, hn, div_zero, zero_smul]
  · rw [tracePart_apply g (tracePart g T), trace_inv_mul_tracePart hn, ← tracePart_apply]

/-- The trace part of a traceless part vanishes. -/
@[simp]
theorem tracePart_tracelessPart (T : Matrix n n K) : tracePart g (tracelessPart g T) = 0 := by
  rw [tracelessPart_apply, map_sub, tracePart_tracePart, sub_self]

/-- The traceless part of a trace part vanishes. -/
@[simp]
theorem tracelessPart_tracePart (T : Matrix n n K) : tracelessPart g (tracePart g T) = 0 := by
  rw [tracelessPart_apply, tracePart_tracePart, sub_self]

/-- Taking the traceless part twice is taking it once. -/
@[simp]
theorem tracelessPart_tracelessPart (T : Matrix n n K) :
    tracelessPart g (tracelessPart g T) = tracelessPart g T := by
  rw [tracelessPart_apply g (tracelessPart g T), tracePart_tracelessPart, sub_zero]

/-- The trace part is a projection. -/
theorem isIdempotentElem_tracePart : IsIdempotentElem (tracePart g) :=
  LinearMap.ext fun T => by rw [mul_apply_eq_comp, tracePart_tracePart]

/-- The traceless part is a projection, complementary to the trace part. -/
theorem isIdempotentElem_tracelessPart : IsIdempotentElem (tracelessPart g) :=
  isIdempotentElem_tracePart.one_sub

/-- The trace part squares to itself: it is idempotent at the composition level. -/
@[simp]
theorem tracePart_mul_self : tracePart g * tracePart g = tracePart g :=
  isIdempotentElem_tracePart.eq

/-- The traceless part squares to itself: it is idempotent at the composition level. -/
@[simp]
theorem tracelessPart_mul_self : tracelessPart g * tracelessPart g = tracelessPart g :=
  isIdempotentElem_tracelessPart.eq

/-- The trace part annihilates the range of the traceless part. -/
@[simp]
theorem tracePart_mul_tracelessPart : tracePart g * tracelessPart g = 0 := by
  rw [tracelessPart_eq_one_sub, isIdempotentElem_tracePart.mul_one_sub_self]

/-- The traceless part annihilates the range of the trace part. -/
@[simp]
theorem tracelessPart_mul_tracePart : tracelessPart g * tracePart g = 0 := by
  rw [tracelessPart_eq_one_sub, isIdempotentElem_tracePart.one_sub_mul_self]

/-- The trace part and the traceless part are complete orthogonal idempotents: the space of
tensors is the direct sum of their ranges. -/
theorem completeOrthogonalIdempotents_tracePart_tracelessPart :
    CompleteOrthogonalIdempotents ![tracePart g, tracelessPart g] := by
  rw [tracelessPart_eq_one_sub]
  exact .of_isIdempotentElem isIdempotentElem_tracePart

/-- The trace part projects onto the line of multiples of the metric: its trace as an
endomorphism is `1`. -/
theorem trace_tracePart (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0) :
    LinearMap.trace K (Matrix n n K) (tracePart g) = 1 := by
  rw [tracePart_def, LinearMap.trace_smulRight, LinearMap.smul_apply, LinearMap.comp_apply,
    mulLeftLinearMap_apply, nonsing_inv_mul g (isUnit_iff_ne_zero.2 hg), traceLinearMap_apply,
    trace_one, smul_eq_mul]
  field_simp

/-- The traceless part projects onto the traceless tensors: its trace as an endomorphism is
`D² - 1`. -/
theorem trace_tracelessPart (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0) :
    LinearMap.trace K (Matrix n n K) (tracelessPart g) = (Fintype.card n : K) ^ 2 - 1 := by
  rw [tracelessPart_eq_one_sub, map_sub, trace_tracePart hg hn, LinearMap.trace_one,
    Module.finrank_matrix, Module.finrank_self]
  push_cast
  ring

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
  · have hT := tracePart_add_tracelessPart_apply g T
    rwa [h, add_zero, tracePart_apply] at hT
  · rintro ⟨c, rfl⟩
    rw [map_smul, tracelessPart_self hg hn, smul_zero]

/-- A tensor is its own trace part exactly when it is a multiple of the metric. -/
theorem tracePart_eq_self_iff (hg : g.det ≠ 0) (hn : (Fintype.card n : K) ≠ 0)
    {T : Matrix n n K} : tracePart g T = T ↔ ∃ c : K, c • g = T := by
  rw [← tracelessPart_eq_zero_iff hg hn, tracelessPart_apply, sub_eq_zero, eq_comm]

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
