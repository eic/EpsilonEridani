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
(`spatialPart_ne_zero_of_spaceLike`), and the equal-time projection of a spacelike vector is
again spacelike (`causalCharacter_sub_timeComponent_smul_basis_eq_spaceLike`).
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

/-- The equal-time projection `v - v⁰ e₀` of a spacelike vector is again spacelike. -/
lemma causalCharacter_sub_timeComponent_smul_basis_eq_spaceLike {d : ℕ} (v : Vector d)
    (hv : causalCharacter v = CausalCharacter.spaceLike) :
    causalCharacter (v - v.timeComponent • basis (Sum.inl 0)) = CausalCharacter.spaceLike := by
  -- The projection has vanishing time component and the same spatial part as `v`, so its
  -- Minkowski square is `-‖v.spatialPart‖ ^ 2 < 0`.
  have h₀ : (v - v.timeComponent • basis (Sum.inl 0)).timeComponent ^ 2 = 0 := by
    simp [timeComponent]
  have hsp : (v - v.timeComponent • basis (Sum.inl 0)).spatialPart = v.spatialPart := by
    ext i
    simp [basis_apply]
  refine (spaceLike_iff_norm_sq_neg _).mpr ?_
  rw [minkowskiProduct_self_eq_sq_sub, h₀, hsp]
  have hpos : 0 < ‖v.spatialPart‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (spatialPart_ne_zero_of_spaceLike v hv)) 2
  linarith

end Vector
end Lorentz
