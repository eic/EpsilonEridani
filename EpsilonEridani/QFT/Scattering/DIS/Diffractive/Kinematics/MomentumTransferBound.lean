/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics.Boundary
public import EpsilonEridani.QFT.Scattering.DIS.Diffractive.Kinematics.LightCone
/-!

# The boundary of the momentum transfer from the on-shell target kinematics

In a diffractive event `e(k) + p(P) → e(k') + X + Y(P')` the incoming target has mass `M`,
`P² = M²`, and the target-side system has mass `M_Y`, `P'² = M_Y²`. Taking light-cone components
with respect to a light-cone basis `(n₊, n₋)`, the target loses the light-cone fraction
`ξ = Δ⁺/P⁺` of its plus momentum (`xiLC`, in `Diffractive.Kinematics.LightCone`), where
`Δ = P - P'`. This file derives from these two on-shell conditions, for non-vanishing `P⁺` and
`ξ ≠ 1` (equivalently non-vanishing `P'⁺`), the exact relation

  `t = tMin M M_Y ξ + w² / (1 - ξ)`  (`tMom_eq_tMin_add`),

where `w = Δ_T - ξ P_T` (`deltaLostRelativeTransverse`) is the transverse momentum transfer
relative to the target direction, `Δ_T` and `P_T` being the transverse parts of `Δ` and of `P`;
for a basis along the collision axis the target has no transverse momentum and `w = Δ_T`. For
`ξ < 1` and `w² ≤ 0`, as for a metric of signature `(+, -, -, -)`, this is the two-body threshold
condition `t ≤ tMin M M_Y ξ` (`tMom_le_tMin`), with equality exactly when `w² = 0`
(`tMom_eq_tMin_iff`). Above the threshold `(1 - ξ) M² ≤ M_Y²` and for `0 ≤ ξ` the momentum
transfer is non-positive (`tMom_nonpos`). In the target-elastic case `M_Y = M` the boundary is
`tMinElastic M ξ = -ξ²M²/(1-ξ)` (`tMin_self`).

Conversely, when the metric is negative semidefinite on transverse vectors and some transverse
vector is space-like, every `t` below the boundary is the momentum transfer of some
`DisKinematics` with the prescribed target-side data and arbitrary prescribed lepton momenta
`k`, `k'` (`exists_tMom_eq_of_le_tMin`), so that the momentum transfers compatible with the
target-side constraints `P`, `P'² = M_Y²` and `ξ < 1` are exactly the half-line
`t ≤ tMin M M_Y ξ` (`setOf_tMom_eq_Iic_tMin`). The photon-side mass `M_X² ≥ 0` is not imposed
there, so this converse is a statement about the target-side kinematics, not attainability within
the full diffractive physical region. The bound `tMom_le_tMin` is unaffected by this caveat.

In the target-elastic case this is the same kinematic boundary as the off-forward
`Particles.Parton.GPD.tZero` (with `Particles.Parton.GPD.OffForwardKinematics.tMom_le_tZero`):
`tMinElastic M ξ = tZero M η` at skewness `η = ξ/(2-ξ)`, i.e. `ξ = 2η/(1+η)`
(`tMinElastic_eq_tZero`, in `Diffractive.Kinematics.OffForwardBoundary`). What is new here is
the dissociated target, `M_Y ≠ M`, and the abstract bilinear form `g`.

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

/-! ### The momentum transfer in light-cone components -/

/-- The exact relation between the momentum transfer and its boundary: for non-vanishing plus
momentum `P⁺`, a light-cone fraction `ξ ≠ 1` (so that `P'⁺ ≠ 0`, `plus_pPrime_ne_zero_iff`),
`P² = M²` and `P'² = M_Y²`, `t = tMin M M_Y ξ + w² / (1 - ξ)`, where `ξ = Δ⁺/P⁺` and
`w = Δ_T - ξ P_T` is the transverse momentum transfer relative to the target direction, `Δ_T` and
`P_T` being the transverse parts of `Δ = P - P'` and of `P`. For a target with no transverse
momentum, `w = Δ_T`. No mass or high-energy approximation is made. -/
theorem tMom_eq_tMin_add (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V)
    {M MY : ℝ} (hp : L.plus K.p ≠ 0) (hξ1 : xiLC L K ≠ 1)
    (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2) :
    tMom g K = tMin M MY (xiLC L K) +
      g (deltaLostRelativeTransverse L K) (deltaLostRelativeTransverse L K) / (1 - xiLC L K) := by
  have hp' := (plus_pPrime_ne_zero_iff L K hp).2 hξ1
  rw [MY2_def, L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg] at hMY
  rw [L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg] at hM
  rw [deltaLostRelativeTransverse_def, tMin_def, one_sub_xiLC L K hp, xiLC_def, ← hM, ← hMY,
    tMom_def, L.bilinForm_self_eq_two_mul_plus_mul_minus_add hg, deltaLost_def]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  field_simp [hp']
  ring

/-- The two-body threshold condition: for non-vanishing plus momentum `P⁺`, a light-cone fraction
`ξ < 1` (for instance from positive plus momenta, `xiLC_lt_one`), `P² = M²`, `P'² = M_Y²` and a
space-like or null relative transverse momentum transfer `w = Δ_T - ξ P_T`, `w² ≤ 0`, the
momentum transfer lies below the boundary, `t ≤ tMin M M_Y ξ`. -/
theorem tMom_le_tMin (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V) {M MY : ℝ}
    (hp : L.plus K.p ≠ 0) (hξ1 : xiLC L K < 1)
    (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2)
    (hw : g (deltaLostRelativeTransverse L K) (deltaLostRelativeTransverse L K) ≤ 0) :
    tMom g K ≤ tMin M MY (xiLC L K) := by
  rw [tMom_eq_tMin_add hg L K hp hξ1.ne hM hMY, add_le_iff_nonpos_right]
  exact div_nonpos_of_nonpos_of_nonneg hw (sub_nonneg.mpr hξ1.le)

/-- The boundary `t = tMin M M_Y ξ` is attained exactly when the relative transverse momentum
transfer `w = Δ_T - ξ P_T` is null, `w² = 0`; for a metric that is definite on transverse vectors
this is the forward configuration `Δ_T = ξ P_T`. -/
theorem tMom_eq_tMin_iff (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V)
    {M MY : ℝ} (hp : L.plus K.p ≠ 0) (hξ1 : xiLC L K ≠ 1)
    (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2) :
    tMom g K = tMin M MY (xiLC L K) ↔
      g (deltaLostRelativeTransverse L K) (deltaLostRelativeTransverse L K) = 0 := by
  rw [tMom_eq_tMin_add hg L K hp hξ1 hM hMY, add_eq_left, div_eq_zero_iff,
    or_iff_left (sub_ne_zero.mpr (Ne.symm hξ1))]

/-- The momentum transfer to the target is non-positive, which is the sign convention
`t ≤ 0` derived rather than imposed: under the hypotheses of `tMom_le_tMin` (non-vanishing plus
momentum `P⁺`, `ξ < 1`, `P² = M²`, `P'² = M_Y²` and `w² ≤ 0` for `w = Δ_T - ξ P_T`), it holds
when the target loses a non-negative plus momentum fraction, `0 ≤ ξ` (`xiLC_nonneg`), and the
target-side system lies above the threshold `(1 - ξ) M² ≤ M_Y²`, in particular when
`M² ≤ M_Y²`. -/
theorem tMom_nonpos (hg : g.IsRefl) (L : LightConeBasis g) (K : DisKinematics V) {M MY : ℝ}
    (hp : L.plus K.p ≠ 0) (hξ1 : xiLC L K < 1)
    (hM : g K.p K.p = M ^ 2) (hMY : MY2 g K = MY ^ 2)
    (hw : g (deltaLostRelativeTransverse L K) (deltaLostRelativeTransverse L K) ≤ 0)
    (hξ : 0 ≤ xiLC L K) (hth : (1 - xiLC L K) * M ^ 2 ≤ MY ^ 2) :
    tMom g K ≤ 0 :=
  (tMom_le_tMin hg L K hp hξ1 hM hMY hw).trans (tMin_nonpos_of_one_sub_mul_sq_le_sq hξ hξ1.le hth)

/-! ### The momentum transfers compatible with the target-side kinematics -/

/-- Every momentum transfer below the boundary is compatible with the target-side kinematics:
for a target `P` with non-vanishing plus momentum and `P² = M²`, any lepton momenta `k`, `k'`, a
final mass `M_Y`, a light-cone fraction `ξ < 1` and any `t ≤ tMin M M_Y ξ`, there is a
`DisKinematics` with incoming target `P`, lepton momenta `k`, `k'`, `P'² = M_Y²`, `Δ⁺/P⁺ = ξ` and
momentum transfer `t`. The relative transverse momentum transfer `Δ_T - ξ P_T`
(`deltaLostRelativeTransverse`) is taken along a transverse vector `e` with `e · e < 0`.

The lepton side, and hence `Q²`, is arbitrary, but the photon-side mass `M_X² = (q + Δ)²` is
not constrained: this is not yet attainability within the diffractive physical region
(`M_X² ≥ 0`). -/
theorem exists_tMom_eq_of_le_tMin (hg : g.IsRefl) (L : LightConeBasis g) {e : V}
    (he : e ∈ L.transverse) (hee : g e e < 0) {P : V} (k kPrime : V) {M MY ξ t : ℝ}
    (hp : L.plus P ≠ 0) (hM : g P P = M ^ 2) (hξ : ξ < 1) (ht : t ≤ tMin M MY ξ) :
    ∃ K : DisKinematics V, K.p = P ∧ K.k = k ∧ K.kPrime = kPrime ∧ MY2 g K = MY ^ 2 ∧
      xiLC L K = ξ ∧ tMom g K = t := by
  have h1ξ : 0 < 1 - ξ := sub_pos.mpr hξ
  -- The target-side momentum `P'` has plus component `(1 - ξ) P⁺`, transverse part
  -- `P'_T = (1 - ξ) P_T - s e`, so that `Δ_T - ξ P_T = s e`, and square `M_Y²`; the transverse
  -- size `s` is fixed by `t`.
  set s := √((tMin M MY ξ - t) * (1 - ξ) / -g e e) with hs
  have hs2 : s ^ 2 * g e e = -((tMin M MY ξ - t) * (1 - ξ)) := by
    rw [hs, Real.sq_sqrt (div_nonneg (mul_nonneg (sub_nonneg.mpr ht) h1ξ.le)
      (neg_nonneg.mpr hee.le))]
    field_simp [hee.ne]
  set pT := (1 - ξ) • L.transverseProj P - s • e with hpT
  have hpTmem : pT ∈ L.transverse :=
    sub_mem (L.transverse.smul_mem _ (L.isProj_transverseProj.map_mem _))
      (L.transverse.smul_mem _ he)
  obtain ⟨pPrime, hKp, hKT, hMY⟩ := L.exists_plus_eq_transverseProj_eq_bilinForm_self_eq hg
    (mul_ne_zero h1ξ.ne' hp) hpTmem (MY ^ 2)
  let K : DisKinematics V :=
    { p := P, pPrime := pPrime, k := k, kPrime := kPrime, q := k - kPrime, hq := rfl }
  have hMYK : MY2 g K = MY ^ 2 := (MY2_def g K).trans hMY
  have hξK : xiLC L K = ξ := by
    have := plus_pPrime_eq L K hp
    rw [hKp] at this
    linarith [mul_right_cancel₀ hp this]
  have hw : deltaLostRelativeTransverse L K = s • e := by
    rw [deltaLostRelativeTransverse_def, hξK, deltaLost_def, map_sub, hKT, hpT]
    module
  refine ⟨K, rfl, rfl, rfl, hMYK, hξK, ?_⟩
  rw [tMom_eq_tMin_add hg L K hp (hξK ▸ hξ.ne) hM hMYK, hξK, hw]
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← sq, hs2]
  field_simp
  ring

/-- The momentum transfers compatible with the target-side kinematics are exactly the half-line
below the boundary: for a target `P` with non-vanishing plus momentum and `P² = M²`, any lepton
momenta `k`, `k'`, a final mass `M_Y`, and a light-cone fraction `ξ < 1`, the momentum transfers
`t` of the `DisKinematics` with incoming target `P`, lepton momenta `k`, `k'`, `P'² = M_Y²` and
`Δ⁺/P⁺ = ξ` form `Set.Iic (tMin M M_Y ξ)`. The metric is assumed negative semidefinite on
transverse vectors and to admit one space-like transverse vector `e`, as the Minkowski metric of
signature `(+, -, -, -)` does in more than two dimensions. In the target-elastic case `M_Y = M`
the right-hand side is `Set.Iic (tMinElastic M ξ)` by `tMin_self`.

The lepton momenta, and hence `Q²`, are prescribed arbitrarily, but the photon-side mass
`M_X² ≥ 0` is not imposed, so this characterises the target-side kinematics, not the full
diffractive physical region. -/
theorem setOf_tMom_eq_Iic_tMin (hg : g.IsRefl) (L : LightConeBasis g)
    (htr : ∀ w ∈ L.transverse, g w w ≤ 0) {e : V} (he : e ∈ L.transverse) (hee : g e e < 0)
    {P : V} (k kPrime : V) {M MY ξ : ℝ} (hp : L.plus P ≠ 0) (hM : g P P = M ^ 2) (hξ : ξ < 1) :
    {t | ∃ K : DisKinematics V, K.p = P ∧ K.k = k ∧ K.kPrime = kPrime ∧ MY2 g K = MY ^ 2 ∧
      xiLC L K = ξ ∧ tMom g K = t} = Set.Iic (tMin M MY ξ) := by
  ext t
  refine ⟨?_, exists_tMom_eq_of_le_tMin hg L he hee k kPrime hp hM hξ⟩
  rintro ⟨K, rfl, -, -, hMY, rfl, rfl⟩
  exact tMom_le_tMin hg L K hp hξ hM hMY (htr _ (deltaLostRelativeTransverse_mem_transverse L K))

end Kinematics

end Diffractive
end DIS
end Scattering
end QFT
end EpsilonEridani
