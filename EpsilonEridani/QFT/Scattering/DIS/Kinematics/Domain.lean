/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Bounds
public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.TargetMass

/-!
# The kinematic domain of inclusive deep-inelastic scattering

For inclusive lepton-nucleon scattering `e(k) + N(P) → e(k') + X` at a fixed value of the
lepton-target invariant `S := 2 P·k`, the invariants `(x, Q²)` of a scattering event are
contained in the kinematic domain

  `kinematicDomain S = {(x, Q²) | 0 < x ≤ 1, 0 < Q², Q² ≤ x S}`.

Since `y = (P·q)/(P·k) = Q² / (x S)`, the last inequality is `y ≤ 1`, and since
`W² = M² + 2 P·q - Q²`, the inequality `x ≤ 1` is the inelastic threshold `W² ≥ M²`
(`DisKinematics.invariants_mem_kinematicDomain_iff`). A Born cross section `d²σ / dx dQ²` is a
density on this domain, and the radiative tail of an observed cross section is an integral over
it; the elastic edge `x = 1` is where that tail accumulates, so it is named (`elasticLine`) rather
than merely excluded.

This is the region cut out by `W² ≥ M²` and `y ≤ 1`, the bounds of `DisKinematics.BasicAssumptions`.
For massless leptons and a target of mass `M > 0` the reachable invariants satisfy the stronger
bound `y (1 + x M² / S) ≤ 1`; nothing in this file uses that refinement.

## Main definitions

* `kinematicDomain S`: the domain of `(x, Q²)` at `S = 2 P·k`.
* `elasticLine S`: its edge `x = 1`, `0 < Q² ≤ S`.

## Main results

* `DisKinematics.invariants_mem_kinematicDomain_iff`: for a symmetric `g` and a spacelike probe
  with `P·k > 0`, the invariants `(x, Q²)` of a `DisKinematics` lie in `kinematicDomain (2 P·k)`
  exactly when `W² ≥ M²` and `y ≤ 1`.
* `DisKinematics.invariants_mem_elasticLine_iff`: they lie on the elastic line exactly when
  `W² = M²` and `y ≤ 1`.
* `DisKinematics.invariants_mem_kinematicDomain_iff'`: the same membership stated without a
  symmetry assumption, as `Q² ≤ 2 P·q` and `P·q ≤ P·k`; either side already forces `P·q > 0`.
* `DisKinematics.BasicAssumptions.invariants_mem_kinematicDomain`: every configuration satisfying
  the bounds of `DisKinematics.BasicAssumptions` has its invariants in the domain.
* `interior_kinematicDomain` and `mem_interior_kinematicDomain`: the interior is given by the
  strict inequalities `0 < x < 1`, `0 < Q² < x S`, with membership in that form.
* `kinematicDomain_inter_fst_eq_one_eq_elasticLine` and
  `elasticLine_subset_frontier_kinematicDomain`: the part of the domain on `x = 1` is exactly the
  elastic line, and it lies on the boundary of the domain.
* `kinematicDomain_nonempty_iff` and `interior_kinematicDomain_nonempty_iff`: the domain, and
  equally its interior, is nonempty exactly when `S > 0`.

## References

* L. W. Mo and Y. S. Tsai, *Radiative corrections to elastic and inelastic ep and μp scattering*,
  Rev. Mod. Phys. **41** (1969) 205, §II.
* Particle Data Group, *Review of Particle Physics*, section "Kinematics", for the deep-inelastic
  invariants and their ranges.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

open Set

/-- The kinematic domain of inclusive deep-inelastic scattering in the variables `z = (x, Q²)` at
a fixed lepton-target invariant `S = 2 P·k`: `0 < x ≤ 1`, `0 < Q²` and `Q² ≤ x S`, the last being
`y ≤ 1` for `y = Q² / (x S)`. -/
def kinematicDomain (S : ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.1 ∧ z.1 ≤ 1 ∧ 0 < z.2 ∧ z.2 ≤ z.1 * S}

@[simp] lemma mem_kinematicDomain {S : ℝ} {z : ℝ × ℝ} :
    z ∈ kinematicDomain S ↔ 0 < z.1 ∧ z.1 ≤ 1 ∧ 0 < z.2 ∧ z.2 ≤ z.1 * S := (Iff.rfl)

/-- The elastic line `x = 1`, `0 < Q² ≤ S`, the edge of the kinematic domain on which elastic
scattering `W² = M²` takes place. -/
def elasticLine (S : ℝ) : Set (ℝ × ℝ) :=
  ({1} : Set ℝ) ×ˢ Ioc 0 S

@[simp] lemma mem_elasticLine {S : ℝ} {z : ℝ × ℝ} :
    z ∈ elasticLine S ↔ z.1 = 1 ∧ 0 < z.2 ∧ z.2 ≤ S := by
  simp [elasticLine]

/-- The domain is nonempty exactly when `S = 2 P·k` is positive. -/
theorem kinematicDomain_nonempty_iff {S : ℝ} : (kinematicDomain S).Nonempty ↔ 0 < S := by
  constructor
  · rintro ⟨z, hx, -, hQ, hy⟩
    exact pos_of_mul_pos_right (hQ.trans_le hy) hx.le
  · intro hS
    exact ⟨(1, S), by simp [mem_kinematicDomain, hS]⟩

/-- The interior of the kinematic domain is cut out by the strict inequalities
`0 < x < 1`, `0 < Q² < x S`. -/
theorem interior_kinematicDomain (S : ℝ) :
    interior (kinematicDomain S) = {z | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ z.2 < z.1 * S} := by
  -- Write the domain as an intersection of four constraints and take interiors termwise; the
  -- upper edge is a sublevel set of `Q² - x S`, a surjective continuous linear functional.
  let L : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ - S • ContinuousLinearMap.fst ℝ ℝ ℝ
  have hL : Function.Surjective L := fun a => ⟨(0, a), by simp [L]⟩
  have h (s t : Set ℝ) : {z : ℝ × ℝ | 0 < z.1} ∩ (Prod.fst ⁻¹' s ∩ ({z | 0 < z.2} ∩ L ⁻¹' t)) =
      {z | 0 < z.1 ∧ z.1 ∈ s ∧ 0 < z.2 ∧ z.2 - S * z.1 ∈ t} := by
    ext z
    simp [L]
  have hD : kinematicDomain S =
      {z : ℝ × ℝ | 0 < z.1} ∩ (Prod.fst ⁻¹' Iic 1 ∩ ({z | 0 < z.2} ∩ L ⁻¹' Iic 0)) := by
    rw [h]
    ext z
    simp [mul_comm]
  have hI : {z : ℝ × ℝ | 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ z.2 < z.1 * S} =
      {z : ℝ × ℝ | 0 < z.1} ∩ (Prod.fst ⁻¹' Iio 1 ∩ ({z | 0 < z.2} ∩ L ⁻¹' Iio 0)) := by
    rw [h]
    ext z
    simp [mul_comm]
  rw [hD, hI, interior_inter, interior_inter, interior_inter,
    (isOpen_lt continuous_const continuous_fst).interior_eq,
    (isOpen_lt continuous_const continuous_snd).interior_eq,
    ← isOpenMap_fst.preimage_interior_eq_interior_preimage continuous_fst, interior_Iic,
    L.interior_preimage hL, interior_Iic]

/-- Membership in the interior of the kinematic domain: the strict inequalities
`0 < x < 1`, `0 < Q² < x S`. -/
@[simp] theorem mem_interior_kinematicDomain {S : ℝ} {z : ℝ × ℝ} :
    z ∈ interior (kinematicDomain S) ↔ 0 < z.1 ∧ z.1 < 1 ∧ 0 < z.2 ∧ z.2 < z.1 * S := by
  rw [interior_kinematicDomain]
  exact Iff.rfl

/-- The interior of the domain is nonempty exactly when `S = 2 P·k` is positive. -/
theorem interior_kinematicDomain_nonempty_iff {S : ℝ} :
    (interior (kinematicDomain S)).Nonempty ↔ 0 < S := by
  refine ⟨fun h => kinematicDomain_nonempty_iff.1 (h.mono interior_subset), fun hS => ?_⟩
  refine ⟨(1 / 2, S / 4), ?_⟩
  rw [mem_interior_kinematicDomain]
  exact ⟨by norm_num, by norm_num, by positivity, by linarith⟩

/-- The part of the kinematic domain on the line `x = 1` is exactly the elastic line. -/
theorem kinematicDomain_inter_fst_eq_one_eq_elasticLine (S : ℝ) :
    kinematicDomain S ∩ {z | z.1 = 1} = elasticLine S := by
  ext z
  simp only [mem_inter_iff, mem_kinematicDomain, mem_ofPred_eq, mem_elasticLine]
  constructor
  · rintro ⟨⟨-, -, hQ, hy⟩, hx⟩
    exact ⟨hx, hQ, by simpa [hx] using hy⟩
  · rintro ⟨hx, hQ, hy⟩
    exact ⟨⟨by simp [hx], hx.le, hQ, by simpa [hx] using hy⟩, hx⟩

lemma elasticLine_subset_kinematicDomain (S : ℝ) : elasticLine S ⊆ kinematicDomain S := by
  rw [← kinematicDomain_inter_fst_eq_one_eq_elasticLine]
  exact inter_subset_left

/-- The elastic line lies on the boundary of the kinematic domain: it belongs to the domain but
not to its interior. -/
theorem elasticLine_subset_frontier_kinematicDomain (S : ℝ) :
    elasticLine S ⊆ frontier (kinematicDomain S) := by
  intro z hz
  refine ⟨subset_closure (elasticLine_subset_kinematicDomain S hz), fun h => ?_⟩
  rw [interior_kinematicDomain] at h
  exact h.2.1.ne (mem_elasticLine.1 hz).1

namespace DisKinematics

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- For a spacelike probe with `P·q > 0`, the upper edge `Q² ≤ x S` of the kinematic domain at
`S = 2 P·k` is the inelasticity bound `y ≤ 1` in raw form: `Q² ≤ xBj ⬝ (2 P·k)` iff `P·q ≤ P·k`. -/
lemma Q2_le_xBj_mul_two_p_dot_k_iff (g : Bilin V) (K : DisKinematics V)
    (hQ : 0 < K.Q2 g) (hpq : 0 < g K.p K.q) :
    K.Q2 g ≤ K.xBj g * (2 * g K.p K.k) ↔ g K.p K.q ≤ g K.p K.k := by
  have h2pq : 0 < 2 * g K.p K.q := by linarith
  rw [xBj, div_mul_eq_mul_div, le_div_iff₀ h2pq]
  constructor <;> intro h <;> nlinarith

/-- For a spacelike probe, the invariants `(x, Q²)` lie in the kinematic domain at
`S = 2 P·k` exactly when `Q² ≤ 2 P·q` and `P·q ≤ P·k`; this statement needs no symmetry of the
bilinear form. When `g` is symmetric and `P·k > 0`, the two inequalities are the threshold
`W² ≥ M²` and the inelasticity bound `y ≤ 1` (`invariants_mem_kinematicDomain_iff`). Positivity of
`P·q` is not assumed: `Q² > 0` together with either side already forces it. -/
theorem invariants_mem_kinematicDomain_iff' (g : Bilin V) (K : DisKinematics V)
    (hQ : 0 < K.Q2 g) :
    (K.xBj g, K.Q2 g) ∈ kinematicDomain (2 * g K.p K.k) ↔
      K.Q2 g ≤ 2 * g K.p K.q ∧ g K.p K.q ≤ g K.p K.k := by
  simp only [mem_kinematicDomain]
  constructor
  · rintro ⟨hx, hx1, -, hy⟩
    -- `0 < xBj = Q² / (2 P·q)` together with `Q² > 0` forces `2 P·q > 0`.
    rw [xBj] at hx hx1
    rcases div_pos_iff.1 hx with ⟨-, h2pq⟩ | ⟨hqs, -⟩
    · have hpq : 0 < g K.p K.q := by linarith
      exact ⟨(div_le_one h2pq).1 hx1, (Q2_le_xBj_mul_two_p_dot_k_iff g K hQ hpq).1 hy⟩
    · exact absurd hqs.le hQ.not_ge
  · rintro ⟨h1, h2⟩
    -- `Q² ≤ 2 P·q` together with `Q² > 0` forces `2 P·q > 0`.
    have h2pq : 0 < 2 * g K.p K.q := hQ.trans_le h1
    have hpq : 0 < g K.p K.q := by linarith
    refine ⟨xBj_pos g K hQ hpq, xBj_le_one g K hpq h1, hQ, ?_⟩
    exact (Q2_le_xBj_mul_two_p_dot_k_iff g K hQ hpq).2 h2

/-- For a symmetric `g` and a spacelike probe with `P·k > 0`, the invariants `(x, Q²)` of a
`DisKinematics` lie in the kinematic domain at `S = 2 P·k` exactly when the hadronic final state
is above the elastic threshold, `W² ≥ M²`, and the inelasticity satisfies `y ≤ 1`. -/
theorem invariants_mem_kinematicDomain_iff (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V)
    (hQ : 0 < K.Q2 g) (hpk : 0 < g K.p K.k) :
    (K.xBj g, K.Q2 g) ∈ kinematicDomain (2 * g K.p K.k) ↔ K.M2 g ≤ K.W2 g ∧ K.yInel g ≤ 1 := by
  rw [invariants_mem_kinematicDomain_iff' g K hQ]
  refine and_congr ?_ ?_
  · rw [W2_eq_with_Q2 g K hg, M2_def]
    constructor <;> intro h <;> linarith
  · refine ⟨yInel_le_one g K hpk, fun h => ?_⟩
    rw [yInel] at h
    exact (div_le_one hpk).1 h

/-- For a symmetric `g` and a spacelike probe with `P·k > 0`, the invariants `(x, Q²)` of a
`DisKinematics` lie on the elastic line at `S = 2 P·k` exactly when the scattering is elastic,
`W² = M²`, and the inelasticity satisfies `y ≤ 1`. -/
theorem invariants_mem_elasticLine_iff (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V)
    (hQ : 0 < K.Q2 g) (hpk : 0 < g K.p K.k) :
    (K.xBj g, K.Q2 g) ∈ elasticLine (2 * g K.p K.k) ↔ K.W2 g = K.M2 g ∧ K.yInel g ≤ 1 := by
  rw [← kinematicDomain_inter_fst_eq_one_eq_elasticLine, mem_inter_iff,
    invariants_mem_kinematicDomain_iff g hg K hQ hpk, mem_ofPred_eq, W2_eq_with_Q2 g K hg, M2_def]
  constructor
  · rintro ⟨⟨-, hy⟩, hx⟩
    -- `xBj = Q² / (2 P·q) = 1` forces `2 P·q ≠ 0`, and then `Q² = 2 P·q`.
    have h2pq : 2 * g K.p K.q ≠ 0 := fun h0 => by simp [xBj, h0] at hx
    rw [xBj, div_eq_one_iff_eq h2pq] at hx
    exact ⟨by linarith, hy⟩
  · rintro ⟨hW, hy⟩
    have h2pq : 2 * g K.p K.q = K.Q2 g := by linarith
    refine ⟨⟨hW.ge, hy⟩, ?_⟩
    rw [xBj, h2pq, div_self hQ.ne']

/-- Every configuration satisfying the bounds of `DisKinematics.BasicAssumptions` has its
invariants `(x, Q²)` in the kinematic domain at `S = 2 P·k`. -/
theorem BasicAssumptions.invariants_mem_kinematicDomain {g : Bilin V} {K : DisKinematics V}
    (h : BasicAssumptions g K) : (K.xBj g, K.Q2 g) ∈ kinematicDomain (2 * g K.p K.k) :=
  (invariants_mem_kinematicDomain_iff' g K h.q2_pos).2
    ⟨h.q2_le_two_p_dot_q, h.p_dot_q_le_p_dot_k⟩

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
