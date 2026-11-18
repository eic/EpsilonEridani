/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis
public import EpsilonEridani.Particles.Parton.GPD.Kinematics
public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics
public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics.Basic
/-!

# The boundary of the momentum transfer from the on-shell target kinematics

In a diffractive event `e(k) + p(P) → e(k') + X + Y(P')` the incoming target has mass `M`,
`P² = M²`, and the target-side system has mass `M_Y`, `P'² = M_Y²`. Taking light-cone components
with respect to a light-cone basis `(n₊, n₋)` along the collision axis, so that the target has no
transverse momentum, the target loses the light-cone fraction `ξ = Δ⁺/P⁺` of its plus momentum
(`xiLC`), where `Δ = P - P'`. This file derives from these two on-shell conditions, for
non-vanishing plus momenta `P⁺` and `P'⁺`, the exact relation

  `t = tMin M M_Y ξ + Δ_T² / (1 - ξ)`  (`tMom_eq_tMin_add`),

where `Δ_T` is the transverse part of the momentum transfer, that of `-P'`
(`transverseProj_deltaLost`). For `ξ ≤ 1` and a transverse momentum transfer with `Δ_T² ≤ 0`, as
for a metric of signature `(+, -, -, -)`, this is the two-body threshold condition
`t ≤ tMin M M_Y ξ` (`tMom_le_tMin`), with equality exactly when `Δ_T² = 0`
(`tMom_eq_tMin_iff`). Above the threshold `(1 - ξ) M² ≤ M_Y²` and for `0 ≤ ξ` the momentum
transfer is non-positive (`tMom_nonpos`). In the target-elastic case `M_Y = M` the boundary is
`tMinElastic M ξ = -ξ²M²/(1-ξ)` (`tMin_self`).

Conversely, when the metric is negative semidefinite on transverse vectors and some transverse
vector is space-like, every `t` below the boundary is the momentum transfer of some
`DisKinematics` with the prescribed target-side data (`exists_tMom_eq_of_le_tMin`), so that the
momentum transfers compatible with the target-side constraints `P`, `P'² = M_Y²` and `ξ < 1` are
exactly the half-line `t ≤ tMin M M_Y ξ` (`setOf_tMom_eq_Iic_tMin`). Only the target-side momenta
are constrained there: the lepton and photon momenta are left free (the exhibited witness takes
`k = k' = q = 0`, so `Q² = 0`), and this converse is therefore a statement about the target-side
kinematics, not attainability within the diffractive physical region (`Q² > 0`, `M_X² ≥ 0`).
The bound `tMom_le_tMin` is unaffected by this caveat.

In the target-elastic case this is the same kinematic boundary as the off-forward
`Particles.Parton.GPD.tZero` (with `Particles.Parton.GPD.OffForwardKinematics.tMom_le_tZero`):
`tMinElastic M ξ = tZero M η` at skewness `η = ξ/(2-ξ)`, i.e. `ξ = 2η/(1+η)`
(`tMinElastic_eq_tZero`). What is new here is the dissociated target, `M_Y ≠ M`, and the abstract
bilinear form `g`.

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

/-! ### The momentum transfer in light-cone components -/

/-- For a target with no transverse momentum, the transverse part of `Δ = P - P'` is that of
`-P'`. -/
theorem transverseProj_deltaLost (L : LightConeBasis g) (K : DisKinematics V)
    (hT : L.transverseProj K.p = 0) :
    L.transverseProj (deltaLost K) = -L.transverseProj K.pPrime := by
  rw [deltaLost_def, map_sub, hT, zero_sub]

/-- For a target with no transverse momentum, the transverse parts of `Δ = P - P'` and of `P'`
have the same square (`transverseProj_deltaLost`). -/
theorem apply_transverseProj_deltaLost (L : LightConeBasis g) (K : DisKinematics V)
    (hT : L.transverseProj K.p = 0) :
    g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) =
      g (L.transverseProj K.pPrime) (L.transverseProj K.pPrime) := by
  simp [transverseProj_deltaLost L K hT]

/-- The exact relation between the momentum transfer and its boundary: for a target with no
transverse momentum, non-vanishing plus momenta `P⁺` and `P'⁺`, `P² = M²` and `P'² = M_Y²`,
`t = tMin M M_Y ξ + Δ_T² / (1 - ξ)`, where `ξ = Δ⁺/P⁺` and `Δ_T` is the transverse part of
`Δ = P - P'`. No mass or high-energy approximation is made. -/
theorem tMom_eq_tMin_add (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V)
    {M MY : ℝ} (hT : L.transverseProj K.p = 0) (hp : L.plus K.p ≠ 0)
    (hp' : L.plus K.pPrime ≠ 0) (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2) :
    tMom g K = tMin M MY (xiLC L K) +
      g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) / (1 - xiLC L K) := by
  have hξ : xiLC L K = 1 - L.plus K.pPrime / L.plus K.p := by
    rw [← one_sub_xiLC L K hp, sub_sub_cancel]
  rw [MY2_def, L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg] at hMY
  rw [L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg] at hM
  simp only [hT, map_zero, add_zero] at hM
  rw [apply_transverseProj_deltaLost L K hT, hξ, tMin_def, sub_sub_cancel, ← hM, ← hMY,
    tMom_def, L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg,
    apply_transverseProj_deltaLost L K hT, deltaLost_def, map_sub, map_sub]
  field_simp
  ring

/-- The two-body threshold condition: for a target with no transverse momentum, non-vanishing
plus momenta `P⁺` and `P'⁺`, a light-cone fraction `ξ ≤ 1` (for instance from positive plus
momenta, `xiLC_lt_one`), `P² = M²`, `P'² = M_Y²` and a space-like or null transverse momentum
transfer `Δ_T² ≤ 0`, the momentum transfer lies below the boundary, `t ≤ tMin M M_Y ξ`. -/
theorem tMom_le_tMin (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V) {M MY : ℝ}
    (hT : L.transverseProj K.p = 0) (hp : L.plus K.p ≠ 0) (hp' : L.plus K.pPrime ≠ 0)
    (hξ1 : xiLC L K ≤ 1) (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2)
    (hΔT : g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) ≤ 0) :
    tMom g K ≤ tMin M MY (xiLC L K) := by
  rw [tMom_eq_tMin_add hg L K hT hp hp' hM hMY, add_le_iff_nonpos_right]
  exact div_nonpos_of_nonpos_of_nonneg hΔT (sub_nonneg.mpr hξ1)

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

/-- The momentum transfer to the target is non-positive, which is the sign convention
`t ≤ 0` derived rather than imposed: under the hypotheses of `tMom_le_tMin` (no transverse target
momentum, non-vanishing plus momenta, `ξ ≤ 1`, `P² = M²`, `P'² = M_Y²` and `Δ_T² ≤ 0`), it holds
when the target loses a non-negative plus momentum fraction, `0 ≤ ξ` (`xiLC_nonneg`), and the
target-side system lies above the threshold `(1 - ξ) M² ≤ M_Y²`, in particular when
`M² ≤ M_Y²`. -/
theorem tMom_nonpos (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V) {M MY : ℝ}
    (hT : L.transverseProj K.p = 0) (hp : L.plus K.p ≠ 0) (hp' : L.plus K.pPrime ≠ 0)
    (hξ1 : xiLC L K ≤ 1) (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2)
    (hΔT : g (L.transverseProj (deltaLost K)) (L.transverseProj (deltaLost K)) ≤ 0)
    (hξ : 0 ≤ xiLC L K) (hth : (1 - xiLC L K) * M ^ 2 ≤ MY ^ 2) :
    tMom g K ≤ 0 :=
  (tMom_le_tMin hg L K hT hp hp' hξ1 hM hMY hΔT).trans (tMin_nonpos hξ hξ1 hth)

/-! ### The momentum transfers compatible with the target-side kinematics -/

/-- Every momentum transfer below the boundary is compatible with the target-side kinematics:
for a target `P` with no transverse momentum, non-vanishing plus momentum and `P² = M²`, a final
mass `M_Y`, a light-cone fraction `ξ < 1` and any `t ≤ tMin M M_Y ξ`, there is a
`DisKinematics` with incoming target `P`, `P'² = M_Y²`, `Δ⁺/P⁺ = ξ` and momentum transfer `t`.
The transverse momentum transfer is taken along a transverse vector `e` with `e · e < 0`.

Only the target-side momenta are constrained: the witness takes `k = k' = q = 0`, so `Q² = 0`
and it is not a diffractive DIS event; this is not attainability within the diffractive physical
region (`Q² > 0`, `M_X² ≥ 0`). -/
theorem exists_tMom_eq_of_le_tMin (hg : g.IsRefl) (L : LightConeBasis g) {e : V}
    (he : e ∈ L.transverse) (hee : g e e < 0) {P : V} {M MY ξ t : ℝ}
    (hT : L.transverseProj P = 0) (hp : L.plus P ≠ 0) (hM : g P P = M ^ 2) (hξ : ξ < 1)
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
  have ha0 : a ≠ 0 := mul_ne_zero h1ξ.ne' hp
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
    have := plus_pPrime_eq L K hp
    rw [hKp, ha] at this
    linarith [mul_right_cancel₀ hp this]
  refine ⟨K, rfl, hMY, hξK, ?_⟩
  rw [tMom_eq_tMin_add hg L K hT hp (hKp ▸ ha0) hM hMY, hξK,
    apply_transverseProj_deltaLost L K hT, hKT]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← sq, hs2]
  field_simp
  ring

/-- The momentum transfers compatible with the target-side kinematics are exactly the half-line
below the boundary: for a target `P` with no transverse momentum, non-vanishing plus momentum and
`P² = M²`, a final mass `M_Y`, and a light-cone fraction `ξ < 1`, the momentum transfers `t` of
the `DisKinematics` with incoming target `P`, `P'² = M_Y²` and `Δ⁺/P⁺ = ξ` form
`Set.Iic (tMin M M_Y ξ)`. The metric is assumed negative semidefinite on transverse vectors and to
admit one space-like transverse vector `e`, as the Minkowski metric of signature `(+, -, -, -)`
does in more than two dimensions. In the target-elastic case `M_Y = M` the right-hand side is
`Set.Iic (tMinElastic M ξ)` by `tMin_self`.

The set constrains only the target-side momenta: the lepton and photon momenta are free (the
witness of `exists_tMom_eq_of_le_tMin` takes them zero), so this characterises the target-side
kinematics, not the diffractive physical region (`Q² > 0`, `M_X² ≥ 0`). -/
theorem setOf_tMom_eq_Iic_tMin (hg : g.IsRefl) (L : LightConeBasis g)
    (htr : ∀ w ∈ L.transverse, g w w ≤ 0) {e : V} (he : e ∈ L.transverse) (hee : g e e < 0)
    {P : V} {M MY ξ : ℝ} (hT : L.transverseProj P = 0) (hp : L.plus P ≠ 0)
    (hM : g P P = M ^ 2) (hξ : ξ < 1) :
    {t | ∃ K : DisKinematics V, K.p = P ∧ MY2 g K = MY ^ 2 ∧ xiLC L K = ξ ∧ tMom g K = t} =
      Set.Iic (tMin M MY ξ) := by
  ext t
  refine ⟨?_, exists_tMom_eq_of_le_tMin hg L he hee hT hp hM hξ⟩
  rintro ⟨K, rfl, hMY, rfl, rfl⟩
  have hp' : L.plus K.pPrime ≠ 0 := (plus_pPrime_ne_zero_iff L K hp).2 hξ.ne
  exact tMom_le_tMin hg L K hT hp hp' hξ.le hM hMY (htr _ (L.isProj_transverseProj.map_mem _))

/-! ### Relation to the off-forward boundary -/

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

end Kinematics
end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
