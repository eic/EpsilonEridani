/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Spheres under linear isometry equivs

A linear isometry equiv preserves norms, so it carries the sphere of radius `r` about the
origin of one normed space onto the sphere of radius `r` about the origin of the other. The
lemma of this file states this in the form that statements transported along such an equiv
need: membership of the sphere, read as an equation between norms.

## Main results

* `LinearIsometryEquiv.norm_map_of_mem_sphere_zero`: the image of a point of
  `Metric.sphere 0 r` under a linear isometry equiv is a vector of norm `r`.
-/

@[expose] public section

namespace LinearIsometryEquiv

variable {R : Type*} {R₂ : Type*} [Semiring R] [Semiring R₂]
  {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  {E : Type*} [SeminormedAddCommGroup E] [Module R E]
  {F : Type*} [SeminormedAddCommGroup F] [Module R₂ F]

/-- A linear isometry equiv carries the sphere of radius `r` about the origin onto the sphere
    of radius `r` about the origin: the image of a point of `Metric.sphere 0 r` is a vector
    of norm `r`. -/
theorem norm_map_of_mem_sphere_zero (e : E ≃ₛₗᵢ[σ₁₂] F) {r : ℝ} {z : E}
    (hz : z ∈ Metric.sphere (0 : E) r) : ‖e z‖ = r := by
  rw [LinearIsometryEquiv.norm_map, mem_sphere_zero_iff_norm.mp hz]

end LinearIsometryEquiv
