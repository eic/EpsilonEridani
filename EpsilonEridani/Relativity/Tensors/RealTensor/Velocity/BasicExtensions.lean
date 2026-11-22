/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

/-!
# Extensions of the basic API of four-velocities

* The rest velocity `0 : Velocity d`, the vector `(1, 0)`, has vanishing spatial part
  (`Velocity.zero_spatialPart`), companion to Physlib's `Velocity.zero_timeComponent`. It is the
  fact that the generalised boost taking a velocity `u` to rest
  (`EpsilonEridani.Relativity.LorentzGroup.Boosts.GeneralizedExtensions`) produces a vector with
  no spatial part.
-/

public section

namespace Lorentz
namespace Velocity

/-- The rest velocity `(1, 0)` has vanishing spatial part. -/
@[simp]
lemma zero_spatialPart {d : ℕ} : (0 : Velocity d).1.spatialPart = 0 := by
  change (Vector.basis (Sum.inl 0) : Vector d).spatialPart = 0
  ext i
  exact Vector.spatialPart_basis_sum_inl i

end Velocity
end Lorentz
