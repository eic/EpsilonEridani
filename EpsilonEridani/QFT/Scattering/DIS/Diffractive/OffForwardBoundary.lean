/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.GPD.Kinematics
public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics.Boundary
/-!

# The target-elastic diffractive boundary as the off-forward boundary

The target-elastic boundary `tMinElastic M ξ = -ξ²M²/(1-ξ)` of diffractive DIS, a function of the
light-cone fraction `ξ = Δ⁺/P⁺` lost by the target, and the boundary
`Particles.Parton.GPD.tZero M η = -4η²M²/(1-η²)` of the off-forward kinematics, a function of the
skewness `η = Δ⁺/(P + P')⁺`, are the same kinematic boundary under the change of variables
`η = ξ/(2-ξ)`, i.e. `ξ = 2η/(1+η)` (`tMinElastic_eq_tZero`, `tZero_eq_tMinElastic`).

This bridge is kept apart from `Diffractive.Kinematics.Boundary` and
`Diffractive.Kinematics.MomentumTransferBound` so that the abstract bilinear-form development
there does not import the Minkowski-space GPD kinematics.

-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive

/-- The target-elastic boundary is the off-forward boundary `Particles.Parton.GPD.tZero` at
skewness `η = ξ/(2-ξ)`, i.e. `ξ = 2η/(1+η)`: `-ξ²M²/(1-ξ) = -4η²M²/(1-η²)`. The light-cone
fraction `ξ = Δ⁺/P⁺` and the skewness `η = Δ⁺/(P + P')⁺` parametrize the same boundary. The
excluded value `ξ = 2` is where the change of variables is singular. -/
theorem tMinElastic_eq_tZero (M : ℝ) {ξ : ℝ} (hξ : ξ ≠ 2) :
    tMinElastic M ξ = Particles.Parton.GPD.tZero M (ξ / (2 - ξ)) := by
  have h2 : 2 - ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm hξ)
  rw [tMinElastic_def, Particles.Parton.GPD.tZero_def]
  by_cases h1 : ξ = 1
  · subst h1
    norm_num
  have h1' : 1 - ξ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hη : 1 - (ξ / (2 - ξ)) ^ 2 = 4 * (1 - ξ) / (2 - ξ) ^ 2 := by
    field_simp
    ring
  rw [hη]
  field_simp

/-- The off-forward boundary `Particles.Parton.GPD.tZero` at skewness `η` is the target-elastic
boundary at light-cone fraction `ξ = 2η/(1+η)`, the inverse change of variables of
`tMinElastic_eq_tZero`. The excluded value `η = -1` is where the change of variables is
singular. -/
theorem tZero_eq_tMinElastic (M : ℝ) {η : ℝ} (hη : η ≠ -1) :
    Particles.Parton.GPD.tZero M η = tMinElastic M (2 * η / (1 + η)) := by
  have h1 : 1 + η ≠ 0 := fun h => hη (by linarith)
  have h2 : 2 * η / (1 + η) ≠ 2 := by
    rw [Ne, div_eq_iff h1]
    intro h
    linarith
  have h3 : 2 - 2 * η / (1 + η) = 2 / (1 + η) := by
    field_simp
    ring
  rw [tMinElastic_eq_tZero M h2, h3, div_div_div_cancel_right₀ h1]
  ring_nf

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
