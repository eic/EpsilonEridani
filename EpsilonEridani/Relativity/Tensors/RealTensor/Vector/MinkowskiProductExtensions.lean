/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Extensions of the Minkowski product on Lorentz vectors

* The Minkowski orthogonal complement of a non-zero causal (time-like or light-like) vector `n`
  contains no time-like vector: every `w` with `⟪n, w⟫ₘ = 0` has `⟪w, w⟫ₘ ≤ 0`
  (`minkowskiProduct_self_nonpos_of_orthogonal_causal`). For light-like `n`, in light-cone
  coordinates adapted to `n` the condition `⟪n, w⟫ₘ = 0` says that one light-cone component of
  `w` vanishes, so that `⟪w, w⟫ₘ = -‖w⊥‖²` is minus the square of the transverse part. This is
  the inequality behind lower bounds on momentum transfers at fixed light-cone momentum
  fractions, such as the minimal momentum transfer of off-forward parton kinematics.
* For two distinct spatial directions `i ≠ j`, the vectors `ofTimeAndTwoSpatial i j x y z =
  x e₀ + y eᵢ + z eⱼ` span a three-dimensional Minkowski subspace on which the Minkowski product
  is the diagonal form `x x' - y y' - z z'` (`minkowskiProduct_ofTimeAndTwoSpatial`). This gives
  explicit configurations, such as light-cone frames, in any spacetime with at least two spatial
  dimensions.
-/

public section

noncomputable section

namespace Lorentz
namespace Vector

open InnerProductSpace

/-- A vector Minkowski-orthogonal to a non-zero causal vector is space-like or light-like:
if `0 ≤ ⟪n, n⟫ₘ`, `n ≠ 0` and `⟪n, w⟫ₘ = 0`, then `⟪w, w⟫ₘ ≤ 0`. -/
lemma minkowskiProduct_self_nonpos_of_orthogonal_causal {d : ℕ} (n : Vector d) {w : Vector d}
    (hn : 0 ≤ ⟪n, n⟫ₘ) (hn0 : n ≠ 0) (hnw : ⟪n, w⟫ₘ = 0) : ⟪w, w⟫ₘ ≤ 0 := by
  rw [minkowskiProduct_eq_timeComponent_spatialPart] at hn hnw ⊢
  have hs := real_inner_self_nonneg (x := n.spatialPart)
  have ha : n.timeComponent ≠ 0 := by
    intro ha
    refine hn0 (eq_zero_of_timeComponent_of_spatialPart ha ?_)
    simp only [ha, mul_zero, zero_sub, neg_nonneg] at hn
    exact inner_self_eq_zero.mp (le_antisymm hn hs)
  have hcs := real_inner_mul_inner_self_le n.spatialPart w.spatialPart
  have hw := real_inner_self_nonneg (x := w.spatialPart)
  rw [← sub_eq_zero.mp hnw] at hcs
  have ha2 : 0 < n.timeComponent ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hn hw]

end Vector
end Lorentz

namespace EpsilonEridani

open Real Inner ProductGeometry Lorentz.Vector
open scoped InnerProductSpace Lorentz.Vector

/-- The vector `x e₀ + y eᵢ + z eⱼ` built from the time direction and the spatial directions
`i` and `j`. -/
def ofTimeAndTwoSpatial {d : ℕ} (i j : Fin d) (x y z : ℝ) : Lorentz.Vector d :=
  x • Lorentz.Vector.basis (Sum.inl 0) + y • Lorentz.Vector.basis (Sum.inr i) +
  z • Lorentz.Vector.basis (Sum.inr j)

lemma ofTimeAndTwoSpatial_def {d : ℕ} (i j : Fin d) (x y z : ℝ) :
    ofTimeAndTwoSpatial i j x y z =
      x • Lorentz.Vector.basis (Sum.inl 0) + y • Lorentz.Vector.basis (Sum.inr i) +
      z • Lorentz.Vector.basis (Sum.inr j) := (rfl)

/-- For distinct spatial directions the Minkowski product of two vectors
`x e₀ + y eᵢ + z eⱼ` and `x' e₀ + y' eᵢ + z' eⱼ` is `x x' - y y' - z z'`. -/
@[simp]
lemma minkowskiProduct_ofTimeAndTwoSpatial {d : ℕ} {i j : Fin d} (hij : i ≠ j)
    (x y z x' y' z' : ℝ) :
    ⟪ofTimeAndTwoSpatial i j x y z, ofTimeAndTwoSpatial i j x' y' z'⟫ₘ =
      x * x' - y * y' - z * z' := by
  simp only [ofTimeAndTwoSpatial_def, map_add, map_smul, add_apply, smul_apply,
    minkowskiProduct_basis_left, minkowskiMatrix.inl_0_inl_0, basis_apply, ↓reduceIte, mul_one,
    reduceCtorEq, mul_zero, add_zero, smul_eq_mul, minkowskiMatrix.inr_i_inr_i, zero_add,
    Sum.inr.injEq, hij.symm, mul_neg, hij]
  ring

@[simp]
lemma ofTimeAndTwoSpatial_sub_ofTimeAndTwoSpatial {d : ℕ} (i j : Fin d) (x y z x' y' z' : ℝ) :
    ofTimeAndTwoSpatial i j x y z - ofTimeAndTwoSpatial i j x' y' z' =
      ofTimeAndTwoSpatial i j (x - x') (y - y') (z - z') := by
  simp only [ofTimeAndTwoSpatial_def, sub_smul]
  abel

end EpsilonEridani
