/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Generalized
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions
public import EpsilonEridani.Relativity.Tensors.RealTensor.Velocity.BasicExtensions

/-!
# Extensions of the generalised boosts

* Pairing with a four-velocity `u` reads off the energy in the rest frame of `u`: for the
  generalised boost `Λ = generalizedBoost u 0` taking `u` to rest, `⟪u, x⟫ₘ = (Λ x)⁰`
  (`LorentzGroup.minkowskiProduct_eq_timeComponent_generalizedBoost_smul`).
* A time-like vector `P` of positive energy is brought to rest by a restricted Lorentz
  transformation that gives positive energy to every `x` with `0 < ⟪P, x⟫ₘ`
  (`LorentzGroup.exists_mem_restricted_spatialPart_smul_eq_zero`). This is how an elastic
  transition is brought to its Breit frame, with the boosted momenta keeping positive energy.
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
    Velocity.zero_spatialPart, inner_zero_left, one_mul, sub_zero]

/-- A time-like vector `P` of positive energy is brought to rest by a restricted Lorentz
transformation `Λ`, so that `Λ P` has no spatial part, and `Λ x` has positive energy whenever
`0 < ⟪P, x⟫ₘ`. -/
lemma exists_mem_restricted_spatialPart_smul_eq_zero {d : ℕ} {P : Vector d}
    (hPP : 0 < ⟪P, P⟫ₘ) (hP0 : 0 < P.timeComponent) :
    ∃ Λ ∈ restricted d, (Λ • P).spatialPart = 0 ∧
      ∀ x : Vector d, 0 < ⟪P, x⟫ₘ → 0 < (Λ • x).timeComponent := by
  -- `Λ` is the generalised boost taking the velocity `u = P / m`, `m = √(P²)`, to rest
  set m := √⟪P, P⟫ₘ with hm
  have hm0 : 0 < m := Real.sqrt_pos.mpr hPP
  have hu : m⁻¹ • P ∈ Velocity d := by
    refine Velocity.mem_iff.mpr ⟨?_, ?_⟩
    · rw [minkowskiProduct_smul_self, inv_pow, hm, Real.sq_sqrt hPP.le, inv_mul_cancel₀ hPP.ne']
    · simp only [timeComponent, apply_smul]
      exact mul_pos (inv_pos.mpr hm0) hP0
  let u : Velocity d := ⟨m⁻¹ • P, hu⟩
  have hP : P = m • u.1 := by
    change P = m • m⁻¹ • P
    rw [smul_smul, mul_inv_cancel₀ hm0.ne', one_smul]
  refine ⟨generalizedBoost u 0, generalizedBoost_mem_restricted u 0, ?_, fun x hx => ?_⟩
  · rw [hP, smul_comm, generalizedBoost_apply_fst, spatialPart_smul, Velocity.zero_spatialPart,
      _root_.smul_zero]
  · rw [hP, map_smul, _root_.smul_apply, smul_eq_mul,
      minkowskiProduct_eq_timeComponent_generalizedBoost_smul] at hx
    exact pos_of_mul_pos_right hx hm0.le

end LorentzGroup
