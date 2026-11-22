/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis
public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics.Basic
/-!

# The light-cone momentum fraction lost by the target

In a diffractive event `e(k) + p(P) → e(k') + X + Y(P')`, light-cone components are taken with
respect to a light-cone basis `(n₊, n₋)` of an abstract bilinear form `g`. The target loses the
light-cone fraction `ξ = Δ⁺/P⁺` of its plus momentum (`xiLC`), where `Δ = P - P'` (`deltaLost`).
This is the argument of the boundaries `tMin` and `tMinElastic` in `t`, and is distinct from the
invariant fraction `Invariants.xi = Δ·q / P·q`.

This file relates `ξ` to the plus momenta, `1 - ξ = P'⁺/P⁺` (`one_sub_xiLC`,
`plus_pPrime_eq`), characterises `ξ ≠ 1` as `P'⁺ ≠ 0` (`plus_pPrime_ne_zero_iff`), and bounds
`ξ` for positive plus momenta (`xiLC_lt_one`, `xiLC_nonneg`).

-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Diffractive
namespace Kinematics

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)
open LinearMap.BilinForm (LightConeBasis)

variable {V : Type} [AddCommGroup V] [Module ℝ V] {g : Bilin V}

/-- The light-cone fraction `ξ = Δ⁺/P⁺` of its plus momentum lost by the target, with
`Δ = P - P'` (`deltaLost`) and plus components taken in the light-cone basis `L`. It is the
argument of the boundaries `tMin` and `tMinElastic`, and differs from the invariant fraction
`xi g K = Δ·q / P·q`. -/
def xiLC (L : LightConeBasis g) (K : DisKinematics V) : ℝ :=
  L.plus (deltaLost K) / L.plus K.p

/-- Defining expression for `xiLC`. -/
theorem xiLC_def (L : LightConeBasis g) (K : DisKinematics V) :
    xiLC L K = L.plus (deltaLost K) / L.plus K.p := (rfl)

/-- The plus momentum retained by the target-side system is the fraction `1 - ξ` of the
target's: `1 - ξ = P'⁺/P⁺`. -/
theorem one_sub_xiLC (L : LightConeBasis g) (K : DisKinematics V) (hp : L.plus K.p ≠ 0) :
    1 - xiLC L K = L.plus K.pPrime / L.plus K.p := by
  rw [xiLC_def, deltaLost_def, map_sub]
  field_simp
  ring

/-- The plus momentum of the target-side system in terms of the fraction lost,
`P'⁺ = (1 - ξ) P⁺`. -/
theorem plus_pPrime_eq (L : LightConeBasis g) (K : DisKinematics V) (hp : L.plus K.p ≠ 0) :
    L.plus K.pPrime = (1 - xiLC L K) * L.plus K.p := by
  rw [one_sub_xiLC L K hp, div_mul_cancel₀ _ hp]

/-- The target-side system has non-vanishing plus momentum exactly when the target does not lose
all of its plus momentum, `ξ ≠ 1`. -/
theorem plus_pPrime_ne_zero_iff (L : LightConeBasis g) (K : DisKinematics V)
    (hp : L.plus K.p ≠ 0) : L.plus K.pPrime ≠ 0 ↔ xiLC L K ≠ 1 := by
  rw [plus_pPrime_eq L K hp, mul_ne_zero_iff, sub_ne_zero, ne_comm, and_iff_left hp]

/-- With positive plus momenta, the light-cone fraction lost by the target is below one. -/
theorem xiLC_lt_one (L : LightConeBasis g) (K : DisKinematics V) (hp : 0 < L.plus K.p)
    (hp' : 0 < L.plus K.pPrime) : xiLC L K < 1 := by
  have h := one_sub_xiLC L K hp.ne'
  have : 0 < L.plus K.pPrime / L.plus K.p := div_pos hp' hp
  linarith

/-- When the target does not gain plus momentum, `P'⁺ ≤ P⁺` with `0 < P⁺`, the light-cone
fraction it loses is non-negative. -/
theorem xiLC_nonneg (L : LightConeBasis g) (K : DisKinematics V) (hp : 0 < L.plus K.p)
    (hp' : L.plus K.pPrime ≤ L.plus K.p) : 0 ≤ xiLC L K := by
  have h := one_sub_xiLC L K hp.ne'
  have : L.plus K.pPrime / L.plus K.p ≤ 1 := (div_le_one hp).mpr hp'
  linarith

end Kinematics
end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
