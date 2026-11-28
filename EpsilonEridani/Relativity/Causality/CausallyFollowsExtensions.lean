/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Causality.CausallyFollows

/-!
# Extensions of the causal future of the origin

* A vector in the causal future of the origin with positive Minkowski square has positive time
  component (`timeComponent_pos_of_causallyFollows_zero`): `causallyFollows_zero_iff` gives
  `0 ≤ y⁰`, and a time-like vector has `y⁰ ≠ 0` (`time_component_ne_zero_of_timelike`). It is
  what keeps the energy of an on-shell momentum of positive mass positive under an orthochronous
  Lorentz transformation.
-/

public section

namespace Lorentz
namespace Vector

open scoped Lorentz.Vector

/-- A vector in the causal future of the origin with positive Minkowski square, `0 < ⟪y, y⟫ₘ`,
has positive time component. -/
lemma timeComponent_pos_of_causallyFollows_zero {d : ℕ} {y : Vector d} (h : causallyFollows 0 y)
    (hy : 0 < ⟪y, y⟫ₘ) : 0 < y.timeComponent :=
  (causallyFollows_zero_iff.mp h).2.lt_of_ne'
    (time_component_ne_zero_of_timelike ((timeLike_iff_norm_sq_pos y).mpr hy))

end Vector
end Lorentz
