/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

/-!
# Extensions of the basic API of four-velocities

* The rest velocity `0 : Velocity d` is the basis vector `e₀ = (1, 0)` (`Velocity.val_zero`), so
  it has vanishing spatial part (`Velocity.zero_spatialPart`), companion to Physlib's
  `Velocity.zero_timeComponent`. It is why the generalised boost taking a velocity `u` to rest
  (`EpsilonEridani.Relativity.LorentzGroup.Boosts.GeneralizedExtensions`) maps `u` to a vector
  with no spatial part.
-/

public section

namespace Lorentz
namespace Velocity

/-- The rest velocity is the basis vector `e₀ = (1, 0)`. -/
lemma val_zero {d : ℕ} : (0 : Velocity d).1 = Vector.basis (Sum.inl 0) := rfl

/-- The rest velocity `(1, 0)` has vanishing spatial part. -/
@[simp]
lemma zero_spatialPart {d : ℕ} : (0 : Velocity d).1.spatialPart = 0 := by
  rw [val_zero]
  ext i
  exact Vector.spatialPart_basis_sum_inl i

end Velocity
end Lorentz
