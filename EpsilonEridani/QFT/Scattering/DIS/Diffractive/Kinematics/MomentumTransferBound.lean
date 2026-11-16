/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis
public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics
public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics.Basic
/-!

# The boundary of the momentum transfer from the on-shell target kinematics

In a diffractive event `e(k) + p(P) → e(k') + X + Y(P')` the incoming target has mass `M`,
`P² = M²`, and the target-side system has mass `M_Y`, `P'² = M_Y²`. Taking light-cone components
with respect to a light-cone basis `(n₊, n₋)` along the collision axis, so that the target has no
transverse momentum, the target loses the light-cone fraction `ξ = Δ⁺/P⁺` of its plus momentum
(`xiLC`), where `Δ = P - P'`. This file derives from these two on-shell conditions alone the
exact relation

  `t = tMin M M_Y ξ + Δ_T² / (1 - ξ)`  (`tMom_eq_tMin_add`),

where `Δ_T` is the transverse part of the momentum transfer. With a metric that is negative
semidefinite on transverse vectors (signature `(+, -, -, -)`), this is the two-body threshold
condition: `t ≤ tMin M M_Y ξ` (`tMom_le_tMin`), with equality exactly when `Δ_T² = 0`
(`tMom_eq_tMin_iff`). When some transverse vector is space-like every `t` below the boundary is
attained by an explicit event (`exists_tMom_eq_of_le_tMin`), so the accessible momentum
transfers at fixed `P`, `M_Y` and `ξ < 1` are exactly the half-line `t ≤ tMin M M_Y ξ`
(`setOf_tMom_eq_Iic_tMin`). In the target-elastic case `M_Y = M` the boundary is
`tMinElastic M ξ = -ξ²M²/(1-ξ)` (`tMom_le_tMinElastic`, `setOf_tMom_eq_Iic_tMinElastic`), and
above the threshold `(1 - ξ) M² ≤ M_Y²` the momentum transfer is non-positive (`tMom_nonpos`).

As in the rest of the DIS kinematics layer, scalar products are taken with respect to an abstract
bilinear form `g`, here assumed reflexive, for which the scalar product splits as
`u · v = u⁺ v⁻ + u⁻ v⁺ + u_T · v_T` (`LightConeBasis.bilinForm_eq_plus_mul_minus_add`).

## References

* G. Wolf, *Review of high energy diffraction in real and virtual photon proton scattering at
  HERA*, Rept. Prog. Phys. **73** (2010) 116202, §2.
* V. Barone and E. Predazzi, *High-Energy Particle Diffraction*, Springer (2002), ch. 1–2.

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

/-! ### The light-cone momentum fraction lost by the target -/

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

/-- With positive plus momenta, the light-cone fraction lost by the target is below one. -/
theorem xiLC_lt_one (L : LightConeBasis g) (K : DisKinematics V) (hp : 0 < L.plus K.p)
    (hp' : 0 < L.plus K.pPrime) : xiLC L K < 1 := by
  have h := one_sub_xiLC L K hp.ne'
  have : 0 < L.plus K.pPrime / L.plus K.p := div_pos hp' hp
  linarith

/-! ### The momentum transfer in light-cone components -/

/-- For a target with no transverse momentum, the transverse part of `Δ = P - P'` is that of
`-P'`, so the two have the same square. -/
private theorem apply_transverseProj_deltaLost (L : LightConeBasis g) (K : DisKinematics V)
    (hT : L.transverseProj K.p = 0) :
    g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) =
      g (L.transverseProj K.pPrime) (L.transverseProj K.pPrime) := by
  simp [deltaLost_def, hT]

/-- The exact relation between the momentum transfer and its boundary: for a target with no
transverse momentum, `P² = M²` and `P'² = M_Y²`,
`t = tMin M M_Y ξ + Δ_T² / (1 - ξ)`, where `ξ = Δ⁺/P⁺` and `Δ_T` is the transverse part of
`Δ = P - P'`. No mass or high-energy approximation is made. -/
theorem tMom_eq_tMin_add (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V)
    {M MY : ℝ} (hT : L.transverseProj K.p = 0) (hp : L.plus K.p ≠ 0)
    (hp' : L.plus K.pPrime ≠ 0) (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2) :
    tMom g K = tMin M MY (xiLC L K) +
      g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) / (1 - xiLC L K) := by
  have hξ : xiLC L K = 1 - L.plus K.pPrime / L.plus K.p := by
    linarith [one_sub_xiLC L K hp]
  rw [MY2_def, L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg] at hMY
  rw [L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg] at hM
  simp only [hT, map_zero, add_zero] at hM
  rw [apply_transverseProj_deltaLost L K hT, hξ, tMin_def, sub_sub_cancel, ← hM, ← hMY,
    tMom_def, L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg,
    apply_transverseProj_deltaLost L K hT, deltaLost_def, map_sub, map_sub]
  field_simp
  ring

/-- The two-body threshold condition: for a target with no transverse momentum, positive plus
momenta, `P² = M²`, `P'² = M_Y²` and a space-like or null transverse momentum transfer
`Δ_T² ≤ 0`, the momentum transfer lies below the boundary, `t ≤ tMin M M_Y ξ`. -/
theorem tMom_le_tMin (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V) {M MY : ℝ}
    (hT : L.transverseProj K.p = 0) (hp : 0 < L.plus K.p) (hp' : 0 < L.plus K.pPrime)
    (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2)
    (hΔT : g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) ≤ 0) :
    tMom g K ≤ tMin M MY (xiLC L K) := by
  rw [tMom_eq_tMin_add hg L K hT hp.ne' hp'.ne' hM hMY, add_le_iff_nonpos_right]
  exact div_nonpos_of_nonpos_of_nonneg hΔT (sub_nonneg.mpr (xiLC_lt_one L K hp hp').le)

/-- The boundary `t = tMin M M_Y ξ` is attained exactly when the transverse momentum transfer is
null, `Δ_T² = 0`; for a metric that is definite on transverse vectors this is the forward
configuration `Δ_T = 0`. -/
theorem tMom_eq_tMin_iff (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V)
    {M MY : ℝ} (hT : L.transverseProj K.p = 0) (hp : L.plus K.p ≠ 0)
    (hp' : L.plus K.pPrime ≠ 0) (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2) :
    tMom g K = tMin M MY (xiLC L K) ↔
      g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) = 0 := by
  have h1 : 1 - xiLC L K ≠ 0 := by
    rw [one_sub_xiLC L K hp]
    exact div_ne_zero hp' hp
  rw [tMom_eq_tMin_add hg L K hT hp hp' hM hMY, add_eq_left, div_eq_zero_iff, or_iff_left h1]

/-- The target-elastic two-body threshold condition: when the target emerges intact,
`P'² = M²`, the momentum transfer satisfies `t ≤ tMinElastic M ξ = -ξ²M²/(1-ξ)`. -/
theorem tMom_le_tMinElastic (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V)
    {M : ℝ} (hT : L.transverseProj K.p = 0) (hp : 0 < L.plus K.p) (hp' : 0 < L.plus K.pPrime)
    (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = M ^ 2)
    (hΔT : g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) ≤ 0) :
    tMom g K ≤ tMinElastic M (xiLC L K) := by
  rw [← tMin_self]
  exact tMom_le_tMin hg L K hT hp hp' hM hMY hΔT

/-- The momentum transfer to the target is non-positive, which is the sign convention
`t ≤ 0` derived rather than imposed: it holds whenever the target loses a non-negative plus
momentum fraction, `0 ≤ ξ`, and the target-side system lies above the threshold
`(1 - ξ) M² ≤ M_Y²`, in particular whenever `M² ≤ M_Y²`. -/
theorem tMom_nonpos (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V) {M MY : ℝ}
    (hT : L.transverseProj K.p = 0) (hp : 0 < L.plus K.p) (hp' : 0 < L.plus K.pPrime)
    (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2)
    (hΔT : g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) ≤ 0)
    (hξ : 0 ≤ xiLC L K) (hth : (1 - xiLC L K) * M ^ 2 ≤ MY ^ 2) :
    tMom g K ≤ 0 :=
  (tMom_le_tMin hg L K hT hp hp' hM hMY hΔT).trans
    (tMin_nonpos hξ (xiLC_lt_one L K hp hp').le hth)

/-! ### The accessible momentum transfers -/

/-- Every momentum transfer below the boundary is attained: for a target `P` with no transverse
momentum, positive plus momentum and `P² = M²`, a final mass `M_Y`, a light-cone fraction
`ξ < 1` and any `t ≤ tMin M M_Y ξ`, there is an event with incoming target `P`, `P'² = M_Y²`,
`Δ⁺/P⁺ = ξ` and momentum transfer `t`. The transverse momentum transfer is taken along a
transverse vector `e` with `e · e < 0`. -/
theorem exists_tMom_eq_of_le_tMin (hg : g.IsRefl) (L : LightConeBasis g) {e : V}
    (he : e ∈ L.transverse) (hee : g e e < 0) {P : V} {M MY ξ t : ℝ}
    (hT : L.transverseProj P = 0) (hp : 0 < L.plus P) (hM : g P P = M ^ 2) (hξ : ξ < 1)
    (ht : t ≤ tMin M MY ξ) :
    ∃ K : DisKinematics V, K.p = P ∧ MY2 g K = MY ^ 2 ∧ xiLC L K = ξ ∧ tMom g K = t := by
  have h1ξ : 0 < 1 - ξ := sub_pos.mpr hξ
  -- The target-side momentum is `P' = (1 - ξ) P⁺ n₊ + c n₋ + s e`, with the transverse size `s`
  -- fixed by `t` and the minus component `c` by the on-shell condition `P'² = M_Y²`.
  set s := √((tMin M MY ξ - t) * (1 - ξ) / -g e e) with hs
  have hs2 : s ^ 2 * g e e = -((tMin M MY ξ - t) * (1 - ξ)) := by
    rw [hs, Real.sq_sqrt (div_nonneg (mul_nonneg (sub_nonneg.mpr ht) h1ξ.le)
      (neg_nonneg.mpr hee.le))]
    field_simp [hee.ne]
  set a := (1 - ξ) * L.plus P with ha
  have ha0 : 0 < a := mul_pos h1ξ hp
  set c := (MY ^ 2 - s ^ 2 * g e e) / (2 * a) with hc
  have heT : L.transverseProj e = e := L.isProj_transverseProj.map_id e he
  obtain ⟨hep, hem⟩ := L.mem_transverse_iff.1 he
  let K : DisKinematics V :=
    { p := P, pPrime := a • L.nPlus + c • L.nMinus + s • e, k := 0, kPrime := 0, q := 0,
      hq := by simp }
  have hKp : L.plus K.pPrime = a := by simp [K, hep]
  have hKm : L.minus K.pPrime = c := by simp [K, hem]
  have hKT : L.transverseProj K.pPrime = s • e := by simp [K, heT]
  have hMY : MY2 g K = MY ^ 2 := by
    rw [MY2_def, L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg, hKp, hKm, hKT, hc]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hξK : xiLC L K = ξ := by
    have := one_sub_xiLC L K hp.ne'
    rw [hKp, ha, mul_div_assoc, div_self hp.ne', mul_one] at this
    linarith
  refine ⟨K, rfl, hMY, hξK, ?_⟩
  rw [tMom_eq_tMin_add hg L K hT hp.ne' (hKp ▸ ha0.ne') hM hMY, hξK,
    apply_transverseProj_deltaLost L K hT, hKT]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← sq, hs2]
  field_simp
  ring

/-- The accessible momentum transfers are exactly the half-line below the boundary: for a target
`P` with no transverse momentum, positive plus momentum and `P² = M²`, a final mass `M_Y`, and a
light-cone fraction `ξ < 1`, the momentum transfers `t` of the events with incoming target `P`,
`P'² = M_Y²` and `Δ⁺/P⁺ = ξ` form `Set.Iic (tMin M M_Y ξ)`. The metric is assumed negative
semidefinite on transverse vectors and to admit one space-like transverse vector `e`, as the
Minkowski metric of signature `(+, -, -, -)` does in more than two dimensions. -/
theorem setOf_tMom_eq_Iic_tMin (hg : g.IsRefl) (L : LightConeBasis g)
    (htr : ∀ w ∈ L.transverse, g w w ≤ 0) {e : V} (he : e ∈ L.transverse) (hee : g e e < 0)
    {P : V} {M MY ξ : ℝ} (hT : L.transverseProj P = 0) (hp : 0 < L.plus P)
    (hM : g P P = M ^ 2) (hξ : ξ < 1) :
    {t | ∃ K : DisKinematics V, K.p = P ∧ MY2 g K = MY ^ 2 ∧ xiLC L K = ξ ∧ tMom g K = t} =
      Set.Iic (tMin M MY ξ) := by
  ext t
  refine ⟨?_, exists_tMom_eq_of_le_tMin hg L he hee hT hp hM hξ⟩
  rintro ⟨K, rfl, hMY, rfl, rfl⟩
  have hp' : 0 < L.plus K.pPrime := by
    have := one_sub_xiLC L K hp.ne'
    rw [eq_div_iff hp.ne'] at this
    nlinarith
  exact tMom_le_tMin hg L K hT hp hp' hM hMY (htr _ (L.isProj_transverseProj.map_mem _))

/-- In the target-elastic case `M_Y = M` the accessible momentum transfers are exactly
`t ≤ tMinElastic M ξ = -ξ²M²/(1-ξ)`, under the hypotheses of `setOf_tMom_eq_Iic_tMin`. -/
theorem setOf_tMom_eq_Iic_tMinElastic (hg : g.IsRefl) (L : LightConeBasis g)
    (htr : ∀ w ∈ L.transverse, g w w ≤ 0) {e : V} (he : e ∈ L.transverse) (hee : g e e < 0)
    {P : V} {M ξ : ℝ} (hT : L.transverseProj P = 0) (hp : 0 < L.plus P)
    (hM : g P P = M ^ 2) (hξ : ξ < 1) :
    {t | ∃ K : DisKinematics V, K.p = P ∧ MY2 g K = M ^ 2 ∧ xiLC L K = ξ ∧ tMom g K = t} =
      Set.Iic (tMinElastic M ξ) := by
  rw [← tMin_self]
  exact setOf_tMom_eq_Iic_tMin hg L htr he hee hT hp hM hξ

end Kinematics
end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
