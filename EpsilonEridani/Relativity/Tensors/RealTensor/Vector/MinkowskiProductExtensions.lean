/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.MinkowskiProduct

/-!
# Vectors in a time-space-space frame

For two distinct spatial directions `i ≠ j`, the vectors `x e₀ + y eᵢ + z eⱼ` span a
three-dimensional Minkowski subspace on which the Minkowski product is the diagonal form
`x x' - y y' - z z'`. This gives explicit configurations, such as light-cone frames, in any
spacetime with at least two spatial dimensions.
-/

public section

noncomputable section

namespace Lorentz
namespace Vector

/-- The vector `x e₀ + y eᵢ + z eⱼ` built from the time direction and the spatial directions
`i` and `j`. -/
def frameVector {d : ℕ} (i j : Fin d) (x y z : ℝ) : Vector d :=
  x • basis (Sum.inl 0) + y • basis (Sum.inr i) + z • basis (Sum.inr j)

lemma frameVector_def {d : ℕ} (i j : Fin d) (x y z : ℝ) :
    frameVector i j x y z =
      x • basis (Sum.inl 0) + y • basis (Sum.inr i) + z • basis (Sum.inr j) := (rfl)

/-- For distinct spatial directions the Minkowski product of frame vectors is
`x x' - y y' - z z'`. -/
lemma minkowskiProduct_frameVector {d : ℕ} {i j : Fin d} (hij : i ≠ j) (x y z x' y' z' : ℝ) :
    ⟪frameVector i j x y z, frameVector i j x' y' z'⟫ₘ = x * x' - y * y' - z * z' := by
  simp [frameVector_def, minkowskiProduct_basis_left, hij, hij.symm, minkowskiMatrix.inl_0_inl_0,
    minkowskiMatrix.inr_i_inr_i]
  ring

lemma frameVector_sub_frameVector {d : ℕ} (i j : Fin d) (x y z x' y' z' : ℝ) :
    frameVector i j x' y' z' - frameVector i j x y z =
      frameVector i j (x' - x) (y' - y) (z' - z) := by
  simp only [frameVector_def, sub_smul]
  abel

end Vector
end Lorentz
