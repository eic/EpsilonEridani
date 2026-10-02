/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The scale hierarchy of a heavy quark-antiquark pair

A heavy quark-antiquark bound state involves three dynamical scales: the heavy-quark mass `m`,
the typical relative momentum `p = m v`, and the binding energy `E`, together with the hadronic
scale `Λ` of QCD. Non-relativistic QCD and potential NRQCD are organised by the hierarchy
`m ≫ m v ≫ E`, with the relative velocity `v` a second small parameter independent of the strong
coupling.

This module records the scales as data, `HeavyQuarkScales`, with the ordering `0 < E < p < m` as
hypothesis fields, and derives the velocity `v = p / m`, which satisfies `0 < v < 1`.

The familiar estimate `E ~ m v²` does *not* follow from the ordering. Writing
`κ = E m / p²` (`HeavyQuarkScales.coulombRatio`), one has the identity `E = m v² κ`, so the
estimate is the statement that `κ` is of order one. That is the additional assumption
`HeavyQuarkScales.CoulombicScaling`, which fixes a constant `K` and asks `K⁻¹ ≤ κ ≤ K`. It is
consistent with every choice of `m`, `p` and `Λ` (`exists_coulombicScaling_one`), and implied by
none (`exists_not_coulombicScaling`), so a statement that needs it must carry it as a hypothesis.

The position of `Λ` relative to the binding energy separates two regimes: the weakly coupled
regime `Λ < E` (`HeavyQuarkScales.WeaklyCoupled`), in which the potential is perturbatively
computable, and the strongly coupled regime `E < Λ < p` (`HeavyQuarkScales.StronglyCoupled`), in
which it is a non-perturbative matching coefficient. They are mutually exclusive, and between them
they exhaust the configurations with `Λ < p` and `Λ ≠ E`. Which regime a given quarkonium occupies
is an empirical input, not a consequence of the ordering of `m`, `p` and `E`
(`exists_weaklyCoupled`, `exists_stronglyCoupled`).

## Main definitions

* `HeavyQuarkScales`: the scales `m`, `p`, `E`, `Λ` with `0 < E < p < m`.
* `HeavyQuarkScales.velocity`: the relative velocity `v = p / m`.
* `HeavyQuarkScales.coulombRatio`: the ratio `κ = E / (m v²) = E m / p²`.
* `HeavyQuarkScales.CoulombicScaling`: the assumption `E ~ m v²`, with an explicit constant.
* `HeavyQuarkScales.WeaklyCoupled`, `HeavyQuarkScales.StronglyCoupled`: the two regimes.

## Main results

* `HeavyQuarkScales.velocity_mem_Ioo`: `0 < v < 1`.
* `HeavyQuarkScales.binding_div_mass_eq`: `E / m = v² · (E / p²) · m`.
* `HeavyQuarkScales.mass_mul_velocity_sq_lt_momentum`: `m v² < m v = p < m`.
* `HeavyQuarkScales.coulombicScaling_one_iff`: `κ` lies in `[1, 1]` exactly when `E = m v²`.
* `HeavyQuarkScales.exists_not_coulombicScaling`: the ordering never forces Coulombic scaling.
* `HeavyQuarkScales.WeaklyCoupled.not_stronglyCoupled` and
  `HeavyQuarkScales.weaklyCoupled_or_stronglyCoupled`: the two regimes are exclusive, and
  exhaustive away from their common boundary.

## References

* W. E. Caswell and G. P. Lepage, *Effective Lagrangians for bound state problems in QED, QCD and
  other field theories*, Phys. Lett. B 167 (1986) 437.
* G. T. Bodwin, E. Braaten and G. P. Lepage, *Rigorous QCD analysis of inclusive annihilation and
  production of heavy quarkonium*, Phys. Rev. D 51 (1995) 1125.
* N. Brambilla, A. Pineda, J. Soto and A. Vairo, *Effective field theories for heavy quarkonium*,
  Rev. Mod. Phys. 77 (2005) 1423, Section II.
-/

public section

namespace EpsilonEridani.QFT.Quarkonium

/-- The dynamical scales of a heavy quark-antiquark pair: the heavy-quark mass `m`, the typical
relative momentum `p`, the binding energy `E`, and the hadronic scale `Λ`. The strict ordering
`0 < E < p < m` is part of the data. -/
@[ext]
structure HeavyQuarkScales where
  /-- The heavy-quark mass `m`. -/
  mass : ℝ
  /-- The typical relative momentum `p` of the pair. -/
  momentum : ℝ
  /-- The binding energy `E` of the pair. -/
  binding : ℝ
  /-- The hadronic scale `Λ` of QCD. -/
  hadronic : ℝ
  /-- The binding energy is positive. -/
  binding_pos : 0 < binding
  /-- The binding energy lies below the relative momentum. -/
  binding_lt_momentum : binding < momentum
  /-- The relative momentum lies below the heavy-quark mass. -/
  momentum_lt_mass : momentum < mass

namespace HeavyQuarkScales

variable (s : HeavyQuarkScales)

theorem momentum_pos : 0 < s.momentum := s.binding_pos.trans s.binding_lt_momentum

theorem mass_pos : 0 < s.mass := s.momentum_pos.trans s.momentum_lt_mass

theorem binding_lt_mass : s.binding < s.mass := s.binding_lt_momentum.trans s.momentum_lt_mass

/-! ### The relative velocity -/

/-- The relative velocity `v = p / m` of the pair. -/
noncomputable def velocity : ℝ := s.momentum / s.mass

theorem velocity_def : s.velocity = s.momentum / s.mass := (rfl)

@[simp]
theorem mass_mul_velocity : s.mass * s.velocity = s.momentum := by
  rw [velocity_def, mul_div_cancel₀ _ s.mass_pos.ne']

theorem velocity_pos : 0 < s.velocity := div_pos s.momentum_pos s.mass_pos

theorem velocity_lt_one : s.velocity < 1 := (div_lt_one s.mass_pos).2 s.momentum_lt_mass

/-- The relative velocity is a genuine small parameter: `0 < v < 1`. -/
theorem velocity_mem_Ioo : s.velocity ∈ Set.Ioo (0 : ℝ) 1 := ⟨s.velocity_pos, s.velocity_lt_one⟩

/-- The scale `m v²` lies strictly below the relative momentum `m v = p`, so that
`m v² < m v < m`. -/
theorem mass_mul_velocity_sq_lt_momentum : s.mass * s.velocity ^ 2 < s.momentum := by
  calc s.mass * s.velocity ^ 2 = s.momentum * s.velocity := by
        rw [← s.mass_mul_velocity]; ring
    _ < s.momentum * 1 := mul_lt_mul_of_pos_left s.velocity_lt_one s.momentum_pos
    _ = s.momentum := mul_one _

/-! ### The Coulombic ratio -/

/-- The ratio `κ = E / (m v²) = E m / p²` of the binding energy to the Coulombic estimate
`m v²`. The estimate `E ~ m v²` is the statement that `κ` is of order one. -/
noncomputable def coulombRatio : ℝ := s.binding * s.mass / s.momentum ^ 2

theorem coulombRatio_def : s.coulombRatio = s.binding * s.mass / s.momentum ^ 2 := (rfl)

theorem coulombRatio_pos : 0 < s.coulombRatio :=
  div_pos (mul_pos s.binding_pos s.mass_pos) (pow_pos s.momentum_pos 2)

/-- The binding energy is the Coulombic estimate `m v²` times the ratio `κ`. -/
theorem mass_mul_velocity_sq_mul_coulombRatio :
    s.mass * s.velocity ^ 2 * s.coulombRatio = s.binding := by
  rw [coulombRatio_def, velocity_def]
  field_simp [s.mass_pos.ne', s.momentum_pos.ne']

/-- `E / m = v² · (E / p²) · m`: the ratio of the binding energy to the mass is `v²` times the
dimensionless factor `E m / p²`, which the ordering of the scales does not fix. -/
theorem binding_div_mass_eq :
    s.binding / s.mass = s.velocity ^ 2 * (s.binding / s.momentum ^ 2) * s.mass := by
  rw [velocity_def]
  field_simp [s.mass_pos.ne', s.momentum_pos.ne']

/-- `E / p = v κ`: the second ratio in the hierarchy is the velocity times `κ`. -/
theorem binding_div_momentum_eq : s.binding / s.momentum = s.velocity * s.coulombRatio := by
  rw [coulombRatio_def, velocity_def]
  field_simp [s.mass_pos.ne', s.momentum_pos.ne']

/-- Coulombic scaling `E ~ m v²` with constant `K`: the ratio `κ = E / (m v²)` lies in
`[K⁻¹, K]`. This is an assumption about the scales, not a consequence of their ordering
(`exists_not_coulombicScaling`). -/
def CoulombicScaling (K : ℝ) : Prop :=
  K⁻¹ ≤ s.coulombRatio ∧ s.coulombRatio ≤ K

variable {s}

theorem coulombicScaling_iff {K : ℝ} :
    s.CoulombicScaling K ↔ K⁻¹ ≤ s.coulombRatio ∧ s.coulombRatio ≤ K := Iff.rfl

/-- Coulombic scaling with constant `K` bounds the binding energy between `K⁻¹ m v²` and
`K m v²`. -/
theorem coulombicScaling_iff_binding {K : ℝ} :
    s.CoulombicScaling K ↔
      K⁻¹ * (s.mass * s.velocity ^ 2) ≤ s.binding ∧ s.binding ≤ K * (s.mass * s.velocity ^ 2) := by
  have h : 0 < s.mass * s.velocity ^ 2 := mul_pos s.mass_pos (pow_pos s.velocity_pos 2)
  rw [coulombicScaling_iff, ← s.mass_mul_velocity_sq_mul_coulombRatio, mul_comm _ s.coulombRatio,
    mul_le_mul_iff_of_pos_right h, mul_le_mul_iff_of_pos_right h]

/-- The constant in a Coulombic-scaling bound is at least one. -/
theorem CoulombicScaling.one_le {K : ℝ} (h : s.CoulombicScaling K) : 1 ≤ K := by
  have hK : 0 < K := s.coulombRatio_pos.trans_le h.2
  have := h.1.trans h.2
  rwa [inv_le_iff_one_le_mul₀ hK, ← sq, one_le_sq_iff₀ hK.le] at this

/-- Coulombic scaling is preserved by enlarging the constant. -/
theorem CoulombicScaling.mono {K K' : ℝ} (h : s.CoulombicScaling K) (hKK' : K ≤ K') :
    s.CoulombicScaling K' :=
  ⟨(inv_anti₀ (zero_lt_one.trans_le h.one_le) hKK').trans h.1, h.2.trans hKK'⟩

/-- Coulombic scaling with constant one is the exact relation `E = m v²`. -/
theorem coulombicScaling_one_iff : s.CoulombicScaling 1 ↔ s.binding = s.mass * s.velocity ^ 2 := by
  rw [coulombicScaling_iff_binding, inv_one, one_mul, ← le_antisymm_iff, eq_comm]

/-- Coulombic scaling is consistent with every mass, relative momentum and hadronic scale: the
binding energy `p² / m` satisfies it exactly. -/
theorem exists_coulombicScaling_one (s : HeavyQuarkScales) :
    ∃ s' : HeavyQuarkScales, s'.mass = s.mass ∧ s'.momentum = s.momentum ∧
      s'.hadronic = s.hadronic ∧ s'.CoulombicScaling 1 := by
  have hm := s.mass_pos
  have hp := s.momentum_pos
  refine ⟨⟨s.mass, s.momentum, s.momentum ^ 2 / s.mass, s.hadronic, by positivity, ?_,
    s.momentum_lt_mass⟩, rfl, rfl, rfl, ?_⟩
  · rw [div_lt_iff₀ hm, sq]
    exact mul_lt_mul_of_pos_left s.momentum_lt_mass hp
  · rw [coulombicScaling_one_iff, velocity_def]
    field_simp

/-- Coulombic scaling is not a consequence of the ordering `0 < E < p < m`: for every mass,
relative momentum and hadronic scale, and every constant `K`, some binding energy violates it. -/
theorem exists_not_coulombicScaling (s : HeavyQuarkScales) (K : ℝ) :
    ∃ s' : HeavyQuarkScales, s'.mass = s.mass ∧ s'.momentum = s.momentum ∧
      s'.hadronic = s.hadronic ∧ ¬ s'.CoulombicScaling K := by
  have hm := s.mass_pos
  have hp := s.momentum_pos
  have hK : 0 < 2 * (|K| + 1) := by positivity
  refine ⟨⟨s.mass, s.momentum, s.momentum ^ 2 / (s.mass * (2 * (|K| + 1))), s.hadronic,
    by positivity, ?_, s.momentum_lt_mass⟩, rfl, rfl, rfl, fun h ↦ ?_⟩
  · rw [div_lt_iff₀ (by positivity), sq]
    refine mul_lt_mul_of_pos_left ?_ hp
    calc s.momentum < s.mass := s.momentum_lt_mass
      _ ≤ s.mass * (2 * (|K| + 1)) := le_mul_of_one_le_right hm.le (by linarith [abs_nonneg K])
  · have h2 := h.1
    simp only [coulombRatio_def] at h2
    have hratio : s.momentum ^ 2 / (s.mass * (2 * (|K| + 1))) * s.mass / s.momentum ^ 2 =
        (2 * (|K| + 1))⁻¹ := by
      field_simp
    rw [hratio, inv_le_inv₀ (zero_lt_one.trans_le h.one_le) hK] at h2
    linarith [le_abs_self K]

/-! ### The weakly and strongly coupled regimes -/

variable (s) in
/-- The weakly coupled regime: the hadronic scale lies below the binding energy, `Λ < E`. -/
def WeaklyCoupled : Prop := s.hadronic < s.binding

variable (s) in
/-- The strongly coupled regime: the hadronic scale lies between the binding energy and the
relative momentum, `E < Λ < p`. -/
def StronglyCoupled : Prop := s.binding < s.hadronic ∧ s.hadronic < s.momentum

theorem weaklyCoupled_iff : s.WeaklyCoupled ↔ s.hadronic < s.binding := Iff.rfl

theorem stronglyCoupled_iff :
    s.StronglyCoupled ↔ s.binding < s.hadronic ∧ s.hadronic < s.momentum := Iff.rfl

/-- In the weakly coupled regime the hadronic scale lies below the relative momentum, as it does
by definition in the strongly coupled one. -/
theorem WeaklyCoupled.hadronic_lt_momentum (h : s.WeaklyCoupled) : s.hadronic < s.momentum :=
  h.trans s.binding_lt_momentum

/-- The weakly coupled regime excludes the strongly coupled one. -/
theorem WeaklyCoupled.not_stronglyCoupled (h : s.WeaklyCoupled) : ¬ s.StronglyCoupled :=
  fun h' ↦ lt_asymm h h'.1

/-- The strongly coupled regime excludes the weakly coupled one. -/
theorem StronglyCoupled.not_weaklyCoupled (h : s.StronglyCoupled) : ¬ s.WeaklyCoupled :=
  fun h' ↦ h'.not_stronglyCoupled h

/-- When the hadronic scale lies below the relative momentum and differs from the binding
energy, the pair is in one of the two regimes, and by `WeaklyCoupled.not_stronglyCoupled` in
only one. -/
theorem weaklyCoupled_or_stronglyCoupled (hE : s.hadronic ≠ s.binding)
    (hp : s.hadronic < s.momentum) : s.WeaklyCoupled ∨ s.StronglyCoupled :=
  hE.lt_or_gt.imp id (⟨·, hp⟩)

/-- The weakly coupled regime is compatible with every mass, relative momentum and binding
energy. -/
theorem exists_weaklyCoupled (s : HeavyQuarkScales) :
    ∃ s' : HeavyQuarkScales, s'.mass = s.mass ∧ s'.momentum = s.momentum ∧
      s'.binding = s.binding ∧ s'.WeaklyCoupled :=
  ⟨{ s with hadronic := s.binding / 2 }, rfl, rfl, rfl,
    weaklyCoupled_iff.2 (half_lt_self s.binding_pos)⟩

/-- The strongly coupled regime is compatible with every mass, relative momentum and binding
energy. -/
theorem exists_stronglyCoupled (s : HeavyQuarkScales) :
    ∃ s' : HeavyQuarkScales, s'.mass = s.mass ∧ s'.momentum = s.momentum ∧
      s'.binding = s.binding ∧ s'.StronglyCoupled :=
  ⟨{ s with hadronic := (s.binding + s.momentum) / 2 }, rfl, rfl, rfl,
    stronglyCoupled_iff.2 <| by constructor <;> linarith [s.binding_lt_momentum]⟩

end HeavyQuarkScales

end EpsilonEridani.QFT.Quarkonium
