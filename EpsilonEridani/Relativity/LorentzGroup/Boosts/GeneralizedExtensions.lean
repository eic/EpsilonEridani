/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Generalized
public import EpsilonEridani.Relativity.Tensors.RealTensor.Velocity.BasicExtensions

/-!
# Extensions of the generalised boosts

* Pairing with a four-velocity `u` reads off the energy in the rest frame of `u`: for the
  generalised boost `Λ = generalizedBoost u 0` taking `u` to rest, `⟪u, x⟫ₘ = (Λ x)⁰`
  (`LorentzGroup.minkowskiProduct_eq_timeComponent_generalizedBoost_smul`). This is how the boost
  to the rest frame of a time-like momentum keeps positive energies positive.
-/

public section

namespace LorentzGroup

open Lorentz Lorentz.Vector

/-- Pairing with a four-velocity `u` is the energy in the rest frame of `u`: `⟪u, x⟫ₘ = (Λ x)⁰`
for the generalised boost `Λ` taking `u` to the rest velocity. -/
lemma minkowskiProduct_eq_timeComponent_generalizedBoost_smul {d : ℕ} (u : Velocity d)
    (x : Vector d) : ⟪u.1, x⟫ₘ = (generalizedBoost u 0 • x).timeComponent := by
  rw [← minkowskiProduct_invariant u.1 x (generalizedBoost u 0), generalizedBoost_apply_fst,
    minkowskiProduct_eq_timeComponent_spatialPart, Velocity.zero_timeComponent,
    Velocity.spatialPart_zero, inner_zero_left, one_mul, sub_zero]

end LorentzGroup
