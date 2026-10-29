/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Vector.Basic

/-!
# Extensions of the basic Lorentz vector API

Facts about `Physlib`'s elementary Lorentz-vector API, companions to
`Physlib.Relativity.Tensors.RealTensor.Vector.Basic`: the additivity of the time component and
of the spatial part, `(u + v)⁰ = u⁰ + v⁰` and `(u + v).spatialPart = u.spatialPart + v.spatialPart`;
the closure of collinearity under sums, `(u + v).spatialPart = (a + b) • n` when
`u.spatialPart = a • n` and `v.spatialPart = b • n`; and the component `⟪v.spatialPart, n⟫ = a`
along a unit vector `n` of the spatial part `a • n` of a four-vector.
-/

public section

namespace Lorentz
namespace Vector

open scoped InnerProductSpace

/-- The time component of a sum is the sum of the time components. -/
@[simp]
lemma timeComponent_add {d : ℕ} (u v : Vector d) :
    (u + v).timeComponent = u.timeComponent + v.timeComponent :=
  rfl

/-- The spatial part of a sum is the sum of the spatial parts. -/
@[simp]
lemma spatialPart_add {d : ℕ} (u v : Vector d) :
    (u + v).spatialPart = u.spatialPart + v.spatialPart := by
  ext i
  simp

/-- The spatial part of a sum of four-vectors whose spatial parts lie along `n` lies along `n`
too: if `u.spatialPart = a • n` and `v.spatialPart = b • n`, then
`(u + v).spatialPart = (a + b) • n`. -/
theorem spatialPart_add_eq_smul_of_spatialPart_eq_smul {d : ℕ} {u v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} {a b : ℝ} (hu : u.spatialPart = a • n)
    (hv : v.spatialPart = b • n) : (u + v).spatialPart = (a + b) • n := by
  rw [spatialPart_add, hu, hv, add_smul]

/-- The component along a unit vector `n` of a spatial part `a • n` is `a`. -/
theorem inner_spatialPart_eq_of_spatialPart_eq_smul {d : ℕ} {v : Vector d}
    {n : EuclideanSpace ℝ (Fin d)} (hn : ‖n‖ = 1) {a : ℝ} (hv : v.spatialPart = a • n) :
    ⟪v.spatialPart, n⟫_ℝ = a := by
  rw [hv, real_inner_smul_self_left, hn, mul_one, mul_one]

end Vector
end Lorentz
