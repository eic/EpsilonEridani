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

* The generalised boost `generalizedBoost u 0` takes the velocity `u` to rest, so the image of
  `u` has no spatial part (`LorentzGroup.spatialPart_generalizedBoost_smul_eq_zero`).
* A time-like vector `P` of positive energy is brought to rest by a restricted Lorentz
  transformation (`LorentzGroup.exists_mem_restricted_spatialPart_smul_eq_zero`), namely the
  generalised boost taking its velocity `P / √(P²)` to rest. This is how an elastic transition is
  brought to its Breit frame.
-/

public section

namespace LorentzGroup

open Lorentz Lorentz.Vector

/-- The generalised boost taking a velocity `u` to rest leaves `u` with no spatial part. -/
lemma spatialPart_generalizedBoost_smul_eq_zero {d : ℕ} (u : Velocity d) :
    (generalizedBoost u 0 • u.1).spatialPart = 0 := by
  rw [generalizedBoost_apply_fst, Velocity.zero_spatialPart]

/-- A time-like vector `P` of positive energy is brought to rest by a restricted Lorentz
transformation `Λ`: `Λ P` has no spatial part. -/
lemma exists_mem_restricted_spatialPart_smul_eq_zero {d : ℕ} {P : Vector d}
    (hPP : 0 < ⟪P, P⟫ₘ) (hP0 : 0 < P.timeComponent) :
    ∃ Λ ∈ restricted d, (Λ • P).spatialPart = 0 := by
  -- `Λ` is the generalised boost taking the velocity `u = P / m`, `m = √(P²)`, to rest
  set m := √⟪P, P⟫ₘ with hm
  have hm0 : 0 < m := Real.sqrt_pos.mpr hPP
  have hu : m⁻¹ • P ∈ Velocity d := by
    refine Velocity.mem_iff.mpr ⟨?_, ?_⟩
    · rw [minkowskiProduct_smul_self, inv_pow, hm, Real.sq_sqrt hPP.le, inv_mul_cancel₀ hPP.ne']
    · simp only [timeComponent, apply_smul]
      exact mul_pos (inv_pos.mpr hm0) hP0
  obtain ⟨u, hu1⟩ : ∃ u : Velocity d, u.1 = m⁻¹ • P := ⟨⟨m⁻¹ • P, hu⟩, rfl⟩
  have hP : P = m • u.1 := by
    rw [hu1, smul_smul, mul_inv_cancel₀ hm0.ne', one_smul]
  refine ⟨generalizedBoost u 0, generalizedBoost_mem_restricted u 0, ?_⟩
  rw [hP, smul_comm, spatialPart_smul, spatialPart_generalizedBoost_smul_eq_zero,
    _root_.smul_zero]

end LorentzGroup
