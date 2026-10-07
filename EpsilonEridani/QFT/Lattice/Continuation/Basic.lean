/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Physlib.Relativity.Tensors.RealTensor.Vector.Causality.Basic
/-!

# The Euclidean continuation of separations and the null-separation obstruction

A Euclidean calculation evaluates matrix elements of operators whose fields are separated by a
real Euclidean vector, while a parton distribution is defined by fields separated along the light
cone. This file sets up the space in which the two are compared, and proves that they never meet
away from the origin.

Both kinds of separation are embedded in the complexified separation space
`ComplexSeparation d = ℂ^{1+d}`, carrying the complex-bilinear (not sesquilinear) Minkowski
product `complexMinkowskiProduct` of signature `(+,-,…,-)`:

* the *Minkowski section* `minkowskiSection d` is the image of the real Minkowski vectors
  `Lorentz.Vector d` under `ofMinkowski`, on which `complexMinkowskiProduct` restricts to
  Physlib's `⟪·, ·⟫ₘ` (`complexMinkowskiProduct_ofMinkowski`);
* the *Euclidean section* `euclideanSection d` is the image of the real Euclidean vectors
  `EuclideanSeparation d = EuclideanSpace ℝ (Fin 1 ⊕ Fin d)` under the continuation map
  `continuation`, which continues the Euclidean time `τ` to the imaginary Minkowski time
  `t = -i τ` and leaves the spatial components unchanged. A point lies on it exactly when its time
  component is purely imaginary and its spatial components are real
  (`mem_euclideanSection_iff`).

Euclidean and Minkowski vectors are kept as distinct types, and the continuation is a named map,
so that the sign of the invariant square is never lost by rereading one as the other.

## Main results

* `complexMinkowskiProduct_continuation`: the continuation turns the Euclidean inner product
  into minus the Minkowski product, `(continuation x)·(continuation y) = -⟪x, y⟫`. In particular the
  continuation of a nonzero Euclidean vector has strictly negative Minkowski square
  (`complexMinkowskiProduct_continuation_self_re_neg`): it is strictly spacelike.
* `eq_zero_of_mem_closure_euclideanSection_of_complexMinkowskiProduct_self_eq_zero`: the only
  null vector in the closure of the Euclidean section is the origin.
* `causalCharacter_eq_spaceLike_of_ofMinkowski_mem_euclideanSection`: a nonzero real Minkowski
  vector on the Euclidean section is spacelike.
* `ofMinkowski_notMem_euclideanSection_of_lightLike`: a nonzero light-like Minkowski vector is not
  the continuation of any real Euclidean separation. This is the kinematic half of the statement
  that a matrix element at light-like separation, and so a parton distribution, is not the
  continuation of a single Euclidean observation.

## References

* K. Osterwalder and R. Schrader, *Axioms for Euclidean Green's functions*, Commun. Math. Phys.
  31 (1973) 83.
* X. Ji, Y.-S. Liu, Y. Liu, J.-H. Zhang and Y. Zhao, *Large-momentum effective theory*,
  Rev. Mod. Phys. 93 (2021) 035005, Sections II and III.
-/

@[expose] public section

namespace EpsilonEridani
namespace QFT
namespace Lattice
namespace Continuation

open Complex Lorentz Lorentz.Vector

variable {d : ℕ}

/-- The complexified separation space `ℂ^{1+d}`, in which both real Minkowski separations and
continued Euclidean separations live. The component `Sum.inl 0` is the time component. -/
abbrev ComplexSeparation (d : ℕ) : Type := Fin 1 ⊕ Fin d → ℂ

/-- A real Euclidean separation in `1 + d` dimensions. The component `Sum.inl 0` is the Euclidean
time `τ`. It is deliberately a different type from the Minkowski vectors `Lorentz.Vector d`. -/
abbrev EuclideanSeparation (d : ℕ) : Type := EuclideanSpace ℝ (Fin 1 ⊕ Fin d)

/-- The complex-bilinear Minkowski product `z·w = z⁰ w⁰ - ∑ᵢ zⁱ wⁱ` on the complexified separation
space: the bilinear (not sesquilinear) form of the complexified Minkowski matrix
`minkowskiMatrix.map ofRealHom`, extending Physlib's `⟪·, ·⟫ₘ`. -/
noncomputable def complexMinkowskiProduct : LinearMap.BilinForm ℂ (ComplexSeparation d) :=
  Matrix.toBilin' (minkowskiMatrix.map ofRealHom)

/-- The complex Minkowski product in components. -/
theorem complexMinkowskiProduct_apply (z w : ComplexSeparation d) :
    complexMinkowskiProduct z w =
      z (Sum.inl 0) * w (Sum.inl 0) - ∑ i, z (Sum.inr i) * w (Sum.inr i) := by
  simp [complexMinkowskiProduct, Matrix.toBilin'_apply', minkowskiMatrix.as_diagonal,
    Matrix.diagonal_map, Matrix.mulVec_diagonal, dotProduct, Fintype.sum_sum_type, sub_eq_add_neg]

/-- The complex Minkowski product is symmetric. -/
theorem complexMinkowskiProduct_symm (z w : ComplexSeparation d) :
    complexMinkowskiProduct z w = complexMinkowskiProduct w z := by
  simp only [complexMinkowskiProduct_apply, mul_comm]

/-! ### The Minkowski section -/

/-- The inclusion of real Minkowski vectors into the complexified separation space. -/
noncomputable def ofMinkowski : Vector d →ₗ[ℝ] ComplexSeparation d :=
  ofRealCLM.toLinearMap.compLeft _

/-- The inclusion of real Minkowski vectors is the componentwise inclusion `ℝ → ℂ`. -/
@[simp]
theorem ofMinkowski_apply (v : Vector d) (μ : Fin 1 ⊕ Fin d) : ofMinkowski v μ = (v μ : ℂ) :=
  (rfl)

/-- Distinct real Minkowski vectors stay distinct in the complexified space. -/
theorem ofMinkowski_injective : Function.Injective (ofMinkowski (d := d)) := fun v w h => by
  ext μ
  simpa using congrFun h μ

/-- On real Minkowski vectors the complex Minkowski product is Physlib's `⟪·, ·⟫ₘ`. -/
@[simp]
theorem complexMinkowskiProduct_ofMinkowski (v w : Vector d) :
    complexMinkowskiProduct (ofMinkowski v) (ofMinkowski w) = (⟪v, w⟫ₘ : ℂ) := by
  simp [complexMinkowskiProduct_apply, minkowskiProduct_toCoord]

/-- The *Minkowski section*: the real Minkowski vectors inside the complexified separation
space. -/
noncomputable def minkowskiSection (d : ℕ) : Submodule ℝ (ComplexSeparation d) :=
  LinearMap.range ofMinkowski

/-- A point lies on the Minkowski section exactly when all its components are real. -/
@[simp]
theorem mem_minkowskiSection_iff {z : ComplexSeparation d} :
    z ∈ minkowskiSection d ↔ ∀ μ, (z μ).im = 0 := by
  refine ⟨?_, fun h => ⟨fun μ => (z μ).re, funext fun μ => ?_⟩⟩
  · rintro ⟨v, rfl⟩ μ
    simp
  · simpa [Complex.ext_iff] using (h μ).symm

/-! ### The continuation and the Euclidean section -/

/-- The continuation of a real Euclidean separation into the complexified separation space: the
Euclidean time `τ` becomes the imaginary Minkowski time `t = -i τ`, and the spatial components are
unchanged. -/
noncomputable def continuation : EuclideanSeparation d →ₗ[ℝ] ComplexSeparation d where
  toFun x := Sum.elim (fun a => -I * (x (Sum.inl a) : ℂ)) (fun i => (x (Sum.inr i) : ℂ))
  map_add' x y := by
    funext μ
    rcases μ with a | i <;> simp [mul_add]
  map_smul' c x := by
    funext μ
    rcases μ with a | i <;> simp [mul_left_comm]

/-- The time component of the continuation is `-i τ`. -/
@[simp]
theorem continuation_apply_inl (x : EuclideanSeparation d) (a : Fin 1) :
    continuation x (Sum.inl a) = -I * (x (Sum.inl a) : ℂ) :=
  (rfl)

/-- The spatial components of the continuation are the Euclidean spatial components. -/
@[simp]
theorem continuation_apply_inr (x : EuclideanSeparation d) (i : Fin d) :
    continuation x (Sum.inr i) = (x (Sum.inr i) : ℂ) :=
  (rfl)

/-- The continuation is injective. -/
theorem continuation_injective : Function.Injective (continuation (d := d)) := fun x y h => by
  ext μ
  rcases μ with a | i
  · have := congrFun h (Sum.inl a)
    simp only [continuation_apply_inl, mul_eq_mul_left_iff, neg_eq_zero, I_ne_zero,
      or_false] at this
    exact_mod_cast this
  · simpa using congrFun h (Sum.inr i)

/-- The *Euclidean section*: the continuations of real Euclidean separations. -/
noncomputable def euclideanSection (d : ℕ) : Submodule ℝ (ComplexSeparation d) :=
  LinearMap.range continuation

/-- A point of the complexified separation space lies on the Euclidean section exactly when its
time component is purely imaginary and its spatial components are real. -/
@[simp]
theorem mem_euclideanSection_iff {z : ComplexSeparation d} :
    z ∈ euclideanSection d ↔ (z (Sum.inl 0)).re = 0 ∧ ∀ i, (z (Sum.inr i)).im = 0 := by
  refine ⟨?_, fun ⟨h₀, h⟩ => ?_⟩
  · rintro ⟨x, rfl⟩
    simp
  · refine ⟨WithLp.toLp 2 (Sum.elim (fun _ => -(z (Sum.inl 0)).im) fun i => (z (Sum.inr i)).re),
      funext fun μ => ?_⟩
    rcases μ with a | i
    · rw [Subsingleton.elim a 0]
      apply Complex.ext <;> simp [h₀]
    · apply Complex.ext <;> simp [h i]

/-- The Minkowski section is closed. -/
theorem isClosed_minkowskiSection : IsClosed (minkowskiSection d : Set (ComplexSeparation d)) :=
  Submodule.closed_of_finiteDimensional _

/-- The Euclidean section is closed. -/
theorem isClosed_euclideanSection : IsClosed (euclideanSection d : Set (ComplexSeparation d)) :=
  Submodule.closed_of_finiteDimensional _

/-! ### The null-separation obstruction -/

/-- The continuation turns the Euclidean inner product into minus the Minkowski product. -/
@[simp]
theorem complexMinkowskiProduct_continuation (x y : EuclideanSeparation d) :
    complexMinkowskiProduct (continuation x) (continuation y) = -((inner ℝ x y : ℝ) : ℂ) := by
  rw [← real_inner_comm]
  simp only [complexMinkowskiProduct_apply, continuation_apply_inl, continuation_apply_inr,
    PiLp.inner_apply, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, RCLike.inner_apply, conj_trivial, ofReal_add, ofReal_mul, ofReal_sum]
  ring_nf
  rw [I_sq]
  ring

/-- The Minkowski square of a continued Euclidean separation is minus its Euclidean squared
length. -/
theorem complexMinkowskiProduct_continuation_self (x : EuclideanSeparation d) :
    complexMinkowskiProduct (continuation x) (continuation x) = -((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [complexMinkowskiProduct_continuation, real_inner_self_eq_norm_sq]

/-- **The image of the continuation is strictly spacelike**: the continuation of a nonzero
Euclidean separation has strictly negative Minkowski square. -/
theorem complexMinkowskiProduct_continuation_self_re_neg {x : EuclideanSeparation d}
    (hx : x ≠ 0) :
    (complexMinkowskiProduct (continuation x) (continuation x)).re < 0 := by
  simpa [complexMinkowskiProduct_continuation_self, ← ofReal_pow, sq_pos_iff] using hx

/-- The only null vector in the closure of the Euclidean section is the origin. -/
theorem eq_zero_of_mem_closure_euclideanSection_of_complexMinkowskiProduct_self_eq_zero
    {z : ComplexSeparation d} (hz : z ∈ closure (euclideanSection d : Set (ComplexSeparation d)))
    (hnull : complexMinkowskiProduct z z = 0) : z = 0 := by
  obtain ⟨x, rfl⟩ := isClosed_euclideanSection.closure_subset hz
  simp_all

/-- The Euclidean section contains no nonzero null vector. -/
theorem eq_zero_of_mem_euclideanSection_of_complexMinkowskiProduct_self_eq_zero
    {z : ComplexSeparation d} (hz : z ∈ euclideanSection d)
    (hnull : complexMinkowskiProduct z z = 0) : z = 0 :=
  eq_zero_of_mem_closure_euclideanSection_of_complexMinkowskiProduct_self_eq_zero
    (subset_closure hz) hnull

/-- A nonzero real Minkowski vector that lies on the Euclidean section is spacelike. -/
theorem causalCharacter_eq_spaceLike_of_ofMinkowski_mem_euclideanSection {v : Vector d}
    (hv : ofMinkowski v ∈ euclideanSection d) (hne : v ≠ 0) :
    causalCharacter v = .spaceLike := by
  obtain ⟨x, hx⟩ := hv
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hne (ofMinkowski_injective (by rw [← hx, map_zero, map_zero]))
  have h := complexMinkowskiProduct_continuation_self_re_neg hx0
  rw [hx, complexMinkowskiProduct_ofMinkowski, ofReal_re] at h
  exact (spaceLike_iff_norm_sq_neg v).mpr h

/-- **No Euclidean preimage of a null separation**: a nonzero light-like Minkowski vector is not
the continuation of any real Euclidean separation. -/
theorem ofMinkowski_notMem_euclideanSection_of_lightLike {v : Vector d}
    (hv : causalCharacter v = .lightLike) (hne : v ≠ 0) :
    ofMinkowski v ∉ euclideanSection d := fun h => by
  rw [causalCharacter_eq_spaceLike_of_ofMinkowski_mem_euclideanSection h hne] at hv
  cases hv

end Continuation
end Lattice
end QFT
end EpsilonEridani
