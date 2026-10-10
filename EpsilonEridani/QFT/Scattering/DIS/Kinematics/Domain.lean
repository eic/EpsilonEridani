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
lepton-target invariant `S := 2 P·k`, the invariants `(x, Q²)` range over the kinematic domain

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

* `DisKinematics.invariants_mem_kinematicDomain_iff`: for a spacelike probe with `P·q > 0` and
  `P·k > 0`, the invariants `(x, Q²)` of a `DisKinematics` lie in `kinematicDomain (2 P·k)`
  exactly when `W² ≥ M²` and `y ≤ 1`.
* `DisKinematics.BasicAssumptions.invariants_mem_kinematicDomain`: every configuration satisfying
  the bounds of `Kinematics.Bounds` has its invariants in the domain.
* `interior_kinematicDomain`: the interior is given by the strict inequalities
  `0 < x < 1`, `0 < Q² < x S`.
* `kinematicDomain_inter_fst_eq_one` and `elasticLine_subset_frontier`: the part of the domain on
  `x = 1` is exactly the elastic line, and it lies on the boundary of the domain.
* `kinematicDomain_nonempty_iff`: the domain is nonempty exactly when `S > 0`.

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

open Set Filter Topology

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
  {z | z.1 = 1 ∧ 0 < z.2 ∧ z.2 ≤ S}

@[simp] lemma mem_elasticLine {S : ℝ} {z : ℝ × ℝ} :
    z ∈ elasticLine S ↔ z.1 = 1 ∧ 0 < z.2 ∧ z.2 ≤ S := (Iff.rfl)

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
  refine Subset.antisymm (fun z hz => ?_) (interior_maximal ?_ ?_)
  · obtain ⟨hx, -, hQ, -⟩ := interior_subset hz
    -- From an interior point one can move a little in any direction and stay in the domain;
    -- moving in `x` and in `Q²` makes both non-strict upper bounds strict.
    have key : ∀ v : ℝ × ℝ, ∃ t : ℝ, 0 < t ∧ z + t • v ∈ kinematicDomain S := by
      intro v
      have hc : Tendsto (fun t : ℝ => z + t • v) (𝓝[>] 0) (𝓝 z) := by
        have hcont : Continuous fun t : ℝ => z + t • v := by fun_prop
        simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      obtain ⟨t, hmem, ht⟩ :=
        ((hc.eventually (mem_interior_iff_mem_nhds.1 hz)).and self_mem_nhdsWithin).exists
      exact ⟨t, ht, hmem⟩
    obtain ⟨t, ht, -, hx1, -⟩ := key (1, 0)
    obtain ⟨u, hu, -, -, -, hy⟩ := key (0, 1)
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_one,
      mul_zero, add_zero] at hx1 hy
    exact ⟨hx, by linarith, hQ, by linarith⟩
  · rintro z ⟨hx, hx1, hQ, hy⟩
    exact ⟨hx, hx1.le, hQ, hy.le⟩
  · exact (isOpen_lt continuous_const continuous_fst).and <|
      (isOpen_lt continuous_fst continuous_const).and <|
      (isOpen_lt continuous_const continuous_snd).and <|
      isOpen_lt continuous_snd (continuous_fst.mul continuous_const)

/-- The part of the kinematic domain on the line `x = 1` is exactly the elastic line. -/
theorem kinematicDomain_inter_fst_eq_one (S : ℝ) :
    kinematicDomain S ∩ {z | z.1 = 1} = elasticLine S := by
  ext z
  simp only [mem_inter_iff, mem_kinematicDomain, mem_ofPred_eq, mem_elasticLine]
  constructor
  · rintro ⟨⟨-, -, hQ, hy⟩, hx⟩
    exact ⟨hx, hQ, by simpa [hx] using hy⟩
  · rintro ⟨hx, hQ, hy⟩
    exact ⟨⟨by simp [hx], hx.le, hQ, by simpa [hx] using hy⟩, hx⟩

lemma elasticLine_subset_kinematicDomain (S : ℝ) : elasticLine S ⊆ kinematicDomain S := by
  rw [← kinematicDomain_inter_fst_eq_one]
  exact inter_subset_left

/-- The elastic line lies on the boundary of the kinematic domain: it belongs to the domain but
not to its interior. -/
theorem elasticLine_subset_frontier (S : ℝ) : elasticLine S ⊆ frontier (kinematicDomain S) := by
  intro z hz
  refine ⟨subset_closure (elasticLine_subset_kinematicDomain S hz), fun h => ?_⟩
  rw [interior_kinematicDomain] at h
  exact h.2.1.ne hz.1

namespace DisKinematics

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- For a spacelike probe `Q² > 0` with `P·q > 0` and `P·k > 0`, the invariants `(x, Q²)` lie in
the kinematic domain at `S = 2 P·k` exactly when the hadronic final state is above the elastic
threshold, `W² ≥ M²`, and the inelasticity satisfies `y ≤ 1`. -/
theorem invariants_mem_kinematicDomain_iff (g : Bilin V) (hg : g.IsSymm) (K : DisKinematics V)
    (hQ : 0 < K.Q2 g) (hpq : 0 < g K.p K.q) (hpk : 0 < g K.p K.k) :
    (K.xBj g, K.Q2 g) ∈ kinematicDomain (2 * g K.p K.k) ↔ K.M2 g ≤ K.W2 g ∧ K.yInel g ≤ 1 := by
  have h2pq : 0 < 2 * g K.p K.q := by linarith
  have hW : K.M2 g ≤ K.W2 g ↔ K.Q2 g ≤ 2 * g K.p K.q := by
    rw [W2_eq_with_Q2 g K hg, M2_def]
    constructor <;> intro h <;> linarith
  have hy : K.Q2 g ≤ K.xBj g * (2 * g K.p K.k) ↔ g K.p K.q ≤ g K.p K.k := by
    rw [xBj, div_mul_eq_mul_div, le_div_iff₀ h2pq]
    constructor <;> intro h <;> nlinarith
  have hx : 0 < K.xBj g := div_pos hQ h2pq
  have hx1 : K.xBj g ≤ 1 ↔ K.Q2 g ≤ 2 * g K.p K.q := div_le_one h2pq
  have hy1 : K.yInel g ≤ 1 ↔ g K.p K.q ≤ g K.p K.k := div_le_one hpk
  simp only [mem_kinematicDomain, hx, hQ, true_and, hx1, hW, hy, hy1]

/-- Every configuration satisfying the bounds of `Kinematics.Bounds` has its invariants `(x, Q²)`
in the kinematic domain at `S = 2 P·k`. -/
theorem BasicAssumptions.invariants_mem_kinematicDomain {g : Bilin V} {K : DisKinematics V}
    (h : BasicAssumptions g K) : (K.xBj g, K.Q2 g) ∈ kinematicDomain (2 * g K.p K.k) := by
  refine ⟨xBj_pos g K h, xBj_le_one g K h, h.q2_pos, ?_⟩
  have h2pq : 0 < 2 * g K.p K.q := by linarith [h.p_dot_q_pos]
  dsimp only
  rw [xBj, div_mul_eq_mul_div, le_div_iff₀ h2pq]
  nlinarith [h.q2_pos, h.p_dot_q_le_p_dot_k]

end DisKinematics

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
