/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic

/-!
# Extensions of the basic API of four-velocities

* The rest velocity `0 : Velocity d` has vanishing spatial part (`Velocity.spatialPart_zero`),
  companion to Physlib's `Velocity.zero_timeComponent`. It is the fact that the generalised boost
  taking a velocity `u` to rest
  (`EpsilonEridani.Relativity.LorentzGroup.Boosts.GeneralizedExtensions`) produces a vector with no
  spatial part.
-/

public section

namespace Lorentz
namespace Velocity

/-- The rest velocity has vanishing spatial part. -/
@[simp]
lemma spatialPart_zero {d : ℕ} : (0 : Velocity d).1.spatialPart = 0 := by
  have h := norm_spatialPart_sq_eq (0 : Velocity d)
  -- `timeComponent` is an `abbrev` for evaluation at `Sum.inl 0`
  have h1 : (0 : Velocity d).1 (Sum.inl 0) = 1 := zero_timeComponent
  rwa [h1, one_pow, sub_self, sq_eq_zero_iff, norm_eq_zero] at h

end Velocity
end Lorentz
