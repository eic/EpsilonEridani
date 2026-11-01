/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Spheres under semilinear isometries

A semilinear isometry preserves norms, so it carries the sphere of radius `r` about the origin
of one normed space into the sphere of radius `r` about the origin of the other. The lemma of
this file states this in the form that statements transported along such a map need:
membership of the sphere, read as an equation between norms.

Like the rest of the `SemilinearIsometryClass` family (`norm_map`, `nnnorm_map`, `isometry`),
the lemma is stated at the class level, so it applies to every bundled semilinear isometry,
not only to the equivs.

## Main results

* `SemilinearIsometryClass.norm_map_of_mem_sphere_zero`: the image of a point of
  `Metric.sphere 0 r` under a semilinear isometry is a vector of norm `r`.
-/

@[expose] public section

namespace SemilinearIsometryClass

variable {R R₂ E F 𝓕 : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂}
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module R E] [Module R₂ F]
  [FunLike 𝓕 E F]

/-- A semilinear isometry carries the sphere of radius `r` about the origin into the sphere
    of radius `r` about the origin: the image of a point of `Metric.sphere 0 r` is a vector
    of norm `r`. -/
theorem norm_map_of_mem_sphere_zero [SemilinearIsometryClass 𝓕 σ₁₂ E F] (f : 𝓕) {r : ℝ}
    {z : E} (hz : z ∈ Metric.sphere (0 : E) r) : ‖f z‖ = r := by
  rw [SemilinearIsometryClass.norm_map, mem_sphere_zero_iff_norm.mp hz]

end SemilinearIsometryClass
