/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Causality.Basic

/-!
# Extensions of the causal character of Lorentz vectors

Facts about `Physlib`'s causal character `Lorentz.Vector.causalCharacter` that go beyond
`Physlib`'s own API: the spatial part of a spacelike vector does not vanish
(`spatialPart_ne_zero_of_spaceLike`).
-/

public section

namespace Lorentz
namespace Vector

open scoped Lorentz.Vector

/-- The spatial part of a spacelike vector does not vanish: a spacelike vector is never purely
temporal. -/
lemma spatialPart_ne_zero_of_spaceLike {d : ℕ} (v : Vector d)
    (hv : causalCharacter v = CausalCharacter.spaceLike) : spatialPart v ≠ 0 := by
  intro h
  have h' : ⟪v, v⟫ₘ < 0 := (spaceLike_iff_norm_sq_neg v).mp hv
  rw [minkowskiProduct_self_eq_sq_sub, h, norm_zero] at h'
  nlinarith [sq_nonneg v.timeComponent]

end Vector
end Lorentz
