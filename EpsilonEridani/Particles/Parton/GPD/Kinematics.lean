/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions

/-!
# Off-forward kinematics and the minimal momentum transfer

A generalized parton distribution is a function of the momentum fraction `x`, the skewness `ξ`
and the invariant momentum transfer `t` of an elastic hadron transition `h(p) → h(p')`. This
module defines the hadron-side variables and proves the kinematic constraint that ties `ξ` to
`t`.

The data (`OffForwardKinematics d M`) are two on-shell momenta `p`, `p'` of a hadron of mass `M`
in `d + 1`-dimensional Minkowski space and a light-like vector `n`; the plus-component of a
momentum `a` is `a⁺ = ⟪n, a⟫ₘ`, and both hadrons carry positive plus-momentum. The derived
variables are

* the average momentum `P = (p + p') / 2` and the momentum transfer `Δ = p' - p`,
* the invariant `tMom = t = Δ²`,
* the skewness `ξ = -Δ⁺ / (2 P⁺)`, so that `p⁺ = (1 + ξ) P⁺` and `p'⁺ = (1 - ξ) P⁺`.

The main results are:

* `OffForwardKinematics.abs_skewness_lt_one`: positivity of both plus-momenta gives `|ξ| < 1`.
* `OffForwardKinematics.minkowskiProduct_transverseDelta_self`: the covariant form of
  `t = -(4 ξ² M² + Δ⊥²) / (1 - ξ²)`, namely `⟪w, w⟫ₘ = (1 - ξ²) t + 4 ξ² M²` for the vector
  `w = transverseDelta = Δ + 2 ξ P`, which is orthogonal to `n` and plays the role of the
  transverse momentum transfer (`⟪w, w⟫ₘ = -Δ⊥²` in a frame where `P` has no transverse
  component).
* `OffForwardKinematics.tMom_le_tZero`: the bound `t ≤ t₀(ξ) = -4 ξ² M² / (1 - ξ²) ≤ 0`.
* `OffForwardKinematics.range_skewness_tMom`: in at least two spatial dimensions the set of
  attainable pairs `(ξ, t)` is exactly `physicalRegion M = {(ξ, t) | |ξ| < 1 ∧ t ≤ t₀(ξ)}`; in
  particular `t₀(ξ)` is attained (`isGreatest_tZero`), and the region is non-empty.

The bound `t ≤ t₀(ξ)` is why `|t|` cannot be taken to zero at non-zero skewness, and hence why
the impact-parameter interpretation of a generalized parton distribution is clean only at
`ξ = 0`.

The skewness here is the light-cone variable of the hadronic transition alone. The variable
`ExclKinematics.xiSkew` of `EpsilonEridani.QFT.Scattering.DIS.Exclusive.Kinematics.Basic` is a
different invariant, built from the photon momenta of the exclusive process.

## References

* X. Ji, *Deeply virtual Compton scattering*, Phys. Rev. D **55** (1997) 7114
  (arXiv:hep-ph/9609381).
* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41
  (arXiv:hep-ph/0307382), §3.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GPD

open Lorentz Lorentz.Vector

/-- The minimal momentum transfer `t₀(ξ) = -4 ξ² M² / (1 - ξ²)` of an elastic transition of a
hadron of mass `M` at skewness `ξ`. For `|ξ| < 1` and in at least two spatial dimensions it is
the largest value of `t` (the smallest value of `|t|`) compatible with the kinematics, see
`OffForwardKinematics.isGreatest_tZero`. -/
def tZero (M ξ : ℝ) : ℝ := -4 * ξ ^ 2 * M ^ 2 / (1 - ξ ^ 2)

lemma tZero_def (M ξ : ℝ) : tZero M ξ = -4 * ξ ^ 2 * M ^ 2 / (1 - ξ ^ 2) := (rfl)

@[simp]
lemma tZero_zero_right (M : ℝ) : tZero M 0 = 0 := by
  simp [tZero]

@[simp]
lemma tZero_neg_right (M ξ : ℝ) : tZero M (-ξ) = tZero M ξ := by
  simp [tZero]

/-- The minimal momentum transfer is non-positive in the physical range `|ξ| < 1`. -/
lemma tZero_nonpos (M : ℝ) {ξ : ℝ} (hξ : |ξ| < 1) : tZero M ξ ≤ 0 := by
  have h : 0 < 1 - ξ ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ξ).mpr hξ)
  rw [tZero]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (ξ * M)]) h.le

/-- For `|ξ| < 1`, `t ≤ t₀(ξ)` is equivalent to `(1 - ξ²) t + 4 ξ² M² ≤ 0`. -/
lemma le_tZero_iff (M : ℝ) {ξ : ℝ} (hξ : |ξ| < 1) (t : ℝ) :
    t ≤ tZero M ξ ↔ (1 - ξ ^ 2) * t + 4 * ξ ^ 2 * M ^ 2 ≤ 0 := by
  have h : 0 < 1 - ξ ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one ξ).mpr hξ)
  rw [tZero, le_div_iff₀ h]
  constructor <;> intro h' <;> linarith

/-- The physical region of the off-forward variables `(ξ, t)` for a hadron of mass `M`: the
skewness satisfies `|ξ| < 1` and the momentum transfer satisfies `t ≤ t₀(ξ)`. In at least two
spatial dimensions it is exactly the set of attainable pairs
(`OffForwardKinematics.range_skewness_tMom`). -/
def physicalRegion (M : ℝ) : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ q.2 ≤ tZero M q.1}

@[simp]
lemma mem_physicalRegion_iff (M : ℝ) (q : ℝ × ℝ) :
    q ∈ physicalRegion M ↔ |q.1| < 1 ∧ q.2 ≤ tZero M q.1 := Iff.rfl

lemma physicalRegion_nonempty (M : ℝ) : (physicalRegion M).Nonempty :=
  ⟨0, by simp⟩

/-- Off-forward kinematics of the elastic transition `h(p) → h(p')` of a hadron of mass `M` in
`d + 1`-dimensional Minkowski space, together with the light-like direction `n` that defines
plus-momenta `a⁺ = ⟪n, a⟫ₘ`. Both hadrons are on their mass shell and carry positive
plus-momentum. -/
@[ext]
structure OffForwardKinematics (d : ℕ) (M : ℝ) where
  /-- The incoming hadron momentum. -/
  p : Vector d
  /-- The outgoing hadron momentum. -/
  p' : Vector d
  /-- The light-like direction defining plus-momenta. -/
  n : Vector d
  /-- The incoming hadron is on its mass shell. -/
  minkowskiProduct_p_self : ⟪p, p⟫ₘ = M ^ 2
  /-- The outgoing hadron is on its mass shell. -/
  minkowskiProduct_p'_self : ⟪p', p'⟫ₘ = M ^ 2
  /-- The direction `n` is light-like. -/
  minkowskiProduct_n_self : ⟪n, n⟫ₘ = 0
  /-- The incoming hadron has positive plus-momentum. -/
  minkowskiProduct_n_p_pos : 0 < ⟪n, p⟫ₘ
  /-- The outgoing hadron has positive plus-momentum. -/
  minkowskiProduct_n_p'_pos : 0 < ⟪n, p'⟫ₘ

namespace OffForwardKinematics

variable {d : ℕ} {M : ℝ} (K : OffForwardKinematics d M)

/-- The average hadron momentum `P = (p + p') / 2`. -/
def avgMomentum : Vector d := (2⁻¹ : ℝ) • (K.p + K.p')

lemma avgMomentum_def : K.avgMomentum = (2⁻¹ : ℝ) • (K.p + K.p') := (rfl)

/-- The momentum transfer `Δ = p' - p`. -/
def delta : Vector d := K.p' - K.p

lemma delta_def : K.delta = K.p' - K.p := (rfl)

/-- The invariant momentum transfer `t = Δ²`. -/
def tMom : ℝ := ⟪K.delta, K.delta⟫ₘ

lemma tMom_def : K.tMom = ⟪K.delta, K.delta⟫ₘ := (rfl)

/-- The skewness `ξ = -Δ⁺ / (2 P⁺)`, with plus-components taken along `n`. -/
def skewness : ℝ := -⟪K.n, K.delta⟫ₘ / (2 * ⟪K.n, K.avgMomentum⟫ₘ)

lemma skewness_def : K.skewness = -⟪K.n, K.delta⟫ₘ / (2 * ⟪K.n, K.avgMomentum⟫ₘ) := (rfl)

/-- The transverse momentum transfer `w = Δ + 2 ξ P`, the part of `Δ` with vanishing
plus-component (`minkowskiProduct_n_transverseDelta_eq_zero`). -/
def transverseDelta : Vector d := K.delta + (2 * K.skewness) • K.avgMomentum

lemma transverseDelta_def : K.transverseDelta = K.delta + (2 * K.skewness) • K.avgMomentum :=
  (rfl)

lemma p_eq_avgMomentum_sub : K.p = K.avgMomentum - (2⁻¹ : ℝ) • K.delta := by
  rw [avgMomentum_def, delta_def]
  module

lemma p'_eq_avgMomentum_add : K.p' = K.avgMomentum + (2⁻¹ : ℝ) • K.delta := by
  rw [avgMomentum_def, delta_def]
  module

lemma minkowskiProduct_n_avgMomentum_eq :
    ⟪K.n, K.avgMomentum⟫ₘ = (⟪K.n, K.p⟫ₘ + ⟪K.n, K.p'⟫ₘ) / 2 := by
  simp only [avgMomentum_def, map_smul, map_add, smul_eq_mul]
  ring

/-- The average hadron momentum has positive plus-momentum. -/
lemma minkowskiProduct_n_avgMomentum_pos : 0 < ⟪K.n, K.avgMomentum⟫ₘ := by
  rw [minkowskiProduct_n_avgMomentum_eq]
  linarith [K.minkowskiProduct_n_p_pos, K.minkowskiProduct_n_p'_pos]

/-- The light-like direction is non-zero, since it gives the hadrons non-zero plus-momentum. -/
lemma n_ne_zero : K.n ≠ 0 := by
  intro hn
  have h := K.minkowskiProduct_n_p_pos
  simp [hn] at h

/-- The skewness in terms of the two plus-momenta, `ξ = (p⁺ - p'⁺) / (p⁺ + p'⁺)`. -/
lemma skewness_eq_div :
    K.skewness = (⟪K.n, K.p⟫ₘ - ⟪K.n, K.p'⟫ₘ) / (⟪K.n, K.p⟫ₘ + ⟪K.n, K.p'⟫ₘ) := by
  simp only [skewness_def, minkowskiProduct_n_avgMomentum_eq, delta_def, map_sub, neg_sub,
    mul_div_cancel₀ _ (two_ne_zero (α := ℝ))]

/-- The incoming plus-momentum is `p⁺ = (1 + ξ) P⁺`. -/
lemma minkowskiProduct_n_p_eq : ⟪K.n, K.p⟫ₘ = (1 + K.skewness) * ⟪K.n, K.avgMomentum⟫ₘ := by
  have h : ⟪K.n, K.p⟫ₘ + ⟪K.n, K.p'⟫ₘ ≠ 0 :=
    (add_pos K.minkowskiProduct_n_p_pos K.minkowskiProduct_n_p'_pos).ne'
  rw [minkowskiProduct_n_avgMomentum_eq, skewness_eq_div]
  field_simp
  ring

/-- The outgoing plus-momentum is `p'⁺ = (1 - ξ) P⁺`. -/
lemma minkowskiProduct_n_p'_eq : ⟪K.n, K.p'⟫ₘ = (1 - K.skewness) * ⟪K.n, K.avgMomentum⟫ₘ := by
  have h : ⟪K.n, K.p⟫ₘ + ⟪K.n, K.p'⟫ₘ ≠ 0 :=
    (add_pos K.minkowskiProduct_n_p_pos K.minkowskiProduct_n_p'_pos).ne'
  rw [minkowskiProduct_n_avgMomentum_eq, skewness_eq_div]
  field_simp
  ring

/-- Positivity of both plus-momenta bounds the skewness: `|ξ| < 1`. -/
lemma abs_skewness_lt_one : |K.skewness| < 1 := by
  have hp := K.minkowskiProduct_n_p_pos
  have hp' := K.minkowskiProduct_n_p'_pos
  rw [skewness_eq_div, abs_lt, lt_div_iff₀ (add_pos hp hp'), div_lt_one (add_pos hp hp')]
  constructor <;> linarith

/-- For an elastic transition the average momentum is orthogonal to the transfer, `P · Δ = 0`. -/
@[simp]
lemma minkowskiProduct_avgMomentum_delta_eq_zero : ⟪K.avgMomentum, K.delta⟫ₘ = 0 := by
  have h : ⟪K.avgMomentum, K.delta⟫ₘ = (⟪K.p', K.p'⟫ₘ - ⟪K.p, K.p⟫ₘ) / 2 := by
    simp only [avgMomentum_def, delta_def, map_smul, map_add, map_sub, _root_.smul_apply,
      _root_.add_apply, smul_eq_mul]
    rw [minkowskiProduct_symm K.p' K.p]
    ring
  simp [h, K.minkowskiProduct_p_self, K.minkowskiProduct_p'_self]

/-- The invariant mass of the average momentum, `P² = M² - t / 4`. -/
lemma minkowskiProduct_avgMomentum_self :
    ⟪K.avgMomentum, K.avgMomentum⟫ₘ = M ^ 2 - K.tMom / 4 := by
  have h := K.minkowskiProduct_p_self
  rw [p_eq_avgMomentum_sub] at h
  simp only [map_sub, map_smul, _root_.sub_apply, _root_.smul_apply,
    smul_eq_mul] at h
  rw [minkowskiProduct_symm K.delta K.avgMomentum,
    K.minkowskiProduct_avgMomentum_delta_eq_zero] at h
  rw [tMom_def]
  linarith

/-- The plus-component of the momentum transfer is `Δ⁺ = -2 ξ P⁺`. -/
lemma minkowskiProduct_n_delta_eq :
    ⟪K.n, K.delta⟫ₘ = -(2 * K.skewness) * ⟪K.n, K.avgMomentum⟫ₘ := by
  have h := K.minkowskiProduct_n_avgMomentum_pos
  rw [skewness_def]
  field_simp

/-- The transverse momentum transfer `w = Δ + 2 ξ P` has vanishing plus-component. -/
@[simp]
lemma minkowskiProduct_n_transverseDelta_eq_zero : ⟪K.n, K.transverseDelta⟫ₘ = 0 := by
  rw [transverseDelta_def, map_add, map_smul, smul_eq_mul, minkowskiProduct_n_delta_eq]
  ring

/-- The covariant form of `t = -(4 ξ² M² + Δ⊥²) / (1 - ξ²)`: for `w = Δ + 2 ξ P`,
`⟪w, w⟫ₘ = (1 - ξ²) t + 4 ξ² M²`. -/
lemma minkowskiProduct_transverseDelta_self :
    ⟪K.transverseDelta, K.transverseDelta⟫ₘ =
      (1 - K.skewness ^ 2) * K.tMom + 4 * K.skewness ^ 2 * M ^ 2 := by
  simp only [transverseDelta_def, minkowskiProduct_add_self, minkowskiProduct_smul_self,
    K.minkowskiProduct_avgMomentum_self]
  simp only [map_smul, smul_eq_mul, minkowskiProduct_symm K.delta K.avgMomentum,
    K.minkowskiProduct_avgMomentum_delta_eq_zero, tMom_def]
  ring

/-- The momentum transfer is bounded by the minimal momentum transfer, `t ≤ t₀(ξ)`. -/
theorem tMom_le_tZero : K.tMom ≤ tZero M K.skewness := by
  rw [le_tZero_iff M K.abs_skewness_lt_one, ← minkowskiProduct_transverseDelta_self]
  exact K.n.minkowskiProduct_self_nonpos_of_orthogonal_causal K.minkowskiProduct_n_self.ge
    K.n_ne_zero K.minkowskiProduct_n_transverseDelta_eq_zero

/-- The momentum transfer of an elastic transition is non-positive, `t ≤ 0`. -/
lemma tMom_nonpos : K.tMom ≤ 0 :=
  K.tMom_le_tZero.trans (tZero_nonpos M K.abs_skewness_lt_one)

/-! ### Attainability of the physical region -/

/-- In at least two spatial dimensions every point of the physical region is attained by an
off-forward configuration. -/
theorem exists_of_mem_physicalRegion (hd : 2 ≤ d) {q : ℝ × ℝ} (hq : q ∈ physicalRegion M) :
    ∃ K : OffForwardKinematics d M, K.skewness = q.1 ∧ K.tMom = q.2 := by
  obtain ⟨ξ, t⟩ := q
  obtain ⟨hξ, ht⟩ := hq
  dsimp only at hξ ht ⊢
  rw [le_tZero_iff M hξ] at ht
  have hξ' : -1 < ξ ∧ ξ < 1 := abs_lt.mp hξ
  -- Light-cone frame in the directions `e₀`, `eᵢ`, `eⱼ`: the light-like `n₀ = e₀ + eⱼ`, and
  -- `p₀`, `p₀'` with average `P = A e₀ + B eⱼ` and transfer `Δ = 2ξB e₀ + D eᵢ + 2ξA eⱼ`.
  -- `A`, `B` are fixed by `P⁺ = A - B = 1` and `P² = A² - B² = M² - t/4`, which gives
  -- `Δ⁺ = -2ξ`, so the skewness is `ξ`. The transverse component `D` is fixed by
  -- `D² = -((1 - ξ²) t + 4 ξ² M²)`, which gives `Δ² = -4ξ²(M² - t/4) - D² = t`.
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  set m2 : ℝ := M ^ 2 - t / 4
  set A : ℝ := (m2 + 1) / 2
  set B : ℝ := (m2 - 1) / 2
  set D : ℝ := √(-((1 - ξ ^ 2) * t + 4 * ξ ^ 2 * M ^ 2))
  have hD : D ^ 2 = -((1 - ξ ^ 2) * t + 4 * ξ ^ 2 * M ^ 2) := Real.sq_sqrt (by linarith)
  set p₀ : Vector d :=
      EpsilonEridani.ofTimeAndTwoSpatial i j (A - ξ * B) (-D / 2) (B - ξ * A) with hp₀
  set p₀' : Vector d :=
      EpsilonEridani.ofTimeAndTwoSpatial i j (A + ξ * B) (D / 2) (B + ξ * A) with hp₀'
  set n₀ : Vector d := EpsilonEridani.ofTimeAndTwoSpatial i j 1 0 1 with hn₀
  have hp : ⟪p₀, p₀⟫ₘ = M ^ 2 := by
    rw [hp₀, minkowskiProduct_ofTimeAndTwoSpatial hij]
    linear_combination (-1 / 4 : ℝ) * hD
  have hp' : ⟪p₀', p₀'⟫ₘ = M ^ 2 := by
    rw [hp₀', minkowskiProduct_ofTimeAndTwoSpatial hij]
    linear_combination (-1 / 4 : ℝ) * hD
  have hnn : ⟪n₀, n₀⟫ₘ = 0 := by
    rw [hn₀, minkowskiProduct_ofTimeAndTwoSpatial hij]
    ring
  have hnp : ⟪n₀, p₀⟫ₘ = 1 + ξ := by
    rw [hn₀, hp₀, minkowskiProduct_ofTimeAndTwoSpatial hij]
    ring
  have hnp' : ⟪n₀, p₀'⟫ₘ = 1 - ξ := by
    rw [hn₀, hp₀', minkowskiProduct_ofTimeAndTwoSpatial hij]
    ring
  have hΔ : ⟪p₀' - p₀, p₀' - p₀⟫ₘ = t := by
    rw [hp₀, hp₀', EpsilonEridani.ofTimeAndTwoSpatial_sub_ofTimeAndTwoSpatial,
      minkowskiProduct_ofTimeAndTwoSpatial hij]
    linear_combination (-1 : ℝ) * hD
  let K₀ : OffForwardKinematics d M :=
    ⟨p₀, p₀', n₀, hp, hp', hnn, by rw [hnp]; linarith, by rw [hnp']; linarith⟩
  refine ⟨K₀, ?_, ?_⟩
  · rw [K₀.skewness_eq_div, hnp, hnp']
    field_simp
    ring
  · rw [K₀.tMom_def, K₀.delta_def]
    exact hΔ

/-- In at least two spatial dimensions the attainable pairs `(ξ, t)` form exactly the physical
region `|ξ| < 1`, `t ≤ t₀(ξ)`. -/
theorem range_skewness_tMom (hd : 2 ≤ d) :
    Set.range (fun K : OffForwardKinematics d M => (K.skewness, K.tMom)) = physicalRegion M := by
  ext q
  constructor
  · rintro ⟨K, rfl⟩
    exact ⟨K.abs_skewness_lt_one, K.tMom_le_tZero⟩
  · intro hq
    obtain ⟨K, h1, h2⟩ := exists_of_mem_physicalRegion hd hq
    exact ⟨K, Prod.ext h1 h2⟩

/-- At fixed skewness `|ξ| < 1`, the minimal momentum transfer `t₀(ξ)` is the largest attainable
value of `t`, in at least two spatial dimensions. -/
theorem isGreatest_tZero (hd : 2 ≤ d) {ξ : ℝ} (hξ : |ξ| < 1) :
    IsGreatest {t | ∃ K : OffForwardKinematics d M, K.skewness = ξ ∧ K.tMom = t} (tZero M ξ) := by
  refine ⟨exists_of_mem_physicalRegion hd (q := (ξ, tZero M ξ)) ⟨hξ, le_rfl⟩, ?_⟩
  rintro t ⟨K, rfl, rfl⟩
  exact K.tMom_le_tZero

end OffForwardKinematics

end GPD
end Parton
end Particles
end EpsilonEridani
