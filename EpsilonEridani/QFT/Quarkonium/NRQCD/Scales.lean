/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Interval.Set.Basic
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

This module records the scales as data, `HeavyQuarkScales`, with the ordering `0 < E < p < m` and
the positivity of the hadronic scale as hypothesis fields, and derives the velocity `v = p / m`,
which satisfies `0 < v < 1`.

The familiar estimate `E ~ m v²` does *not* follow from the ordering. Writing
`κ = E m / p²` (`HeavyQuarkScales.coulombRatio`), one has the identity `E = m v² κ`, so the
estimate is the statement that `κ` is of order one. That is the additional assumption
`HeavyQuarkScales.CoulombicScaling`, which fixes a constant `K` and asks `κ ∈ [K⁻¹, K]`. It is
consistent with every choice of `0 < p < m` and `0 < Λ` (`exists_coulombicScaling_one`), and
implied by none (`exists_not_coulombicScaling`), so a statement that needs it must carry it as a
hypothesis.

The position of `Λ` relative to the binding energy separates two regimes: the weakly coupled
regime `Λ < E` (`HeavyQuarkScales.WeaklyCoupled`), in which the potential is perturbatively
computable, and the strongly coupled regime `E < Λ < p` (`HeavyQuarkScales.StronglyCoupled`), in
which it is a non-perturbative matching coefficient. They are mutually exclusive, and between them
they exhaust the configurations with `Λ < p` and `Λ ≠ E`. Which regime a given quarkonium occupies
is an empirical input, not a consequence of the ordering of `m`, `p` and `E`
(`exists_weaklyCoupled`, `exists_stronglyCoupled`).

## Main definitions

* `HeavyQuarkScales`: the scales `m`, `p`, `E`, `Λ` with `0 < E < p < m` and `0 < Λ`.
* `HeavyQuarkScales.velocity`: the relative velocity `v = p / m`.
* `HeavyQuarkScales.coulombRatio`: the ratio `κ = E / (m v²) = E m / p²`.
* `HeavyQuarkScales.CoulombicScaling`: the assumption `E ~ m v²`, with an explicit constant.
* `HeavyQuarkScales.ofCoulombRatio`: the scales with prescribed `m`, `p`, `Λ` and ratio `κ`.
* `HeavyQuarkScales.WeaklyCoupled`, `HeavyQuarkScales.StronglyCoupled`: the two regimes.

## Main results

* `HeavyQuarkScales.velocity_pos` and `HeavyQuarkScales.velocity_lt_one`: `0 < v < 1`.
* `HeavyQuarkScales.binding_div_mass_eq_velocity_sq_mul_coulombRatio`: `E / m = v² * κ`.
* `HeavyQuarkScales.binding_div_mass_eq`: `E / m = v² · (E / p²) · m`.
* `HeavyQuarkScales.mass_mul_velocity_sq_lt_momentum`: `m v² < m v = p`.
* `HeavyQuarkScales.coulombicScaling_one_iff`: `κ` lies in `[1, 1]` exactly when `E = m v²`.
* `HeavyQuarkScales.exists_not_coulombicScaling`: the ordering never forces Coulombic scaling.
* `HeavyQuarkScales.WeaklyCoupled.not_stronglyCoupled`,
  `HeavyQuarkScales.StronglyCoupled.not_weaklyCoupled` and
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
`0 < E < p < m`, and the positivity of the hadronic scale, are part of the data. -/
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
  /-- The hadronic scale is positive. -/
  hadronic_pos : 0 < hadronic

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

/-- The relative velocity is positive. -/
theorem velocity_pos : 0 < s.velocity := div_pos s.momentum_pos s.mass_pos

/-- The relative velocity is less than one: the relative momentum lies below the heavy-quark
mass. -/
theorem velocity_lt_one : s.velocity < 1 := (div_lt_one s.mass_pos).2 s.momentum_lt_mass



/-- The scale `m v²` lies strictly below the relative momentum `m v = p`. -/
theorem mass_mul_velocity_sq_lt_momentum : s.mass * s.velocity ^ 2 < s.momentum := by
  calc s.mass * s.velocity ^ 2 = s.momentum * s.velocity := by
        rw [← s.mass_mul_velocity]; ring
    _ < s.momentum := mul_lt_of_lt_one_right s.momentum_pos s.velocity_lt_one

/-! ### The Coulombic ratio -/

/-- The ratio `κ = E / (m v²) = E m / p²` of the binding energy to the Coulombic estimate
`m v²`. The estimate `E ~ m v²` is the statement that `κ` is of order one. -/
noncomputable def coulombRatio : ℝ := s.binding * s.mass / s.momentum ^ 2

theorem coulombRatio_def : s.coulombRatio = s.binding * s.mass / s.momentum ^ 2 := (rfl)

theorem coulombRatio_pos : 0 < s.coulombRatio :=
  div_pos (mul_pos s.binding_pos s.mass_pos) (pow_pos s.momentum_pos 2)

/-- The binding energy is the Coulombic estimate `m v²` times the ratio `κ`. -/
@[simp]
theorem mass_mul_velocity_sq_mul_coulombRatio :
    s.mass * s.velocity ^ 2 * s.coulombRatio = s.binding := by
  rw [coulombRatio_def, velocity_def]
  field_simp [s.mass_pos.ne', s.momentum_pos.ne']

/-- `E / m = v² κ`: the ratio of the binding energy to the mass is `v²` times `κ`. -/
theorem binding_div_mass_eq_velocity_sq_mul_coulombRatio :
    s.binding / s.mass = s.velocity ^ 2 * s.coulombRatio := by
  rw [coulombRatio_def, velocity_def]
  field_simp [s.mass_pos.ne', s.momentum_pos.ne']

/-- `κ = E / (m v²)`: the Coulombic ratio is the binding energy over the Coulombic estimate. -/
theorem coulombRatio_eq_div : s.coulombRatio = s.binding / (s.mass * s.velocity ^ 2) := by
  rw [coulombRatio_def, velocity_def]
  field_simp [s.mass_pos.ne', s.momentum_pos.ne']

/-- `E / m = v² · (E / p²) · m`: the ratio of the binding energy to the mass is `v²` times the
dimensionless factor `E m / p²`. -/
theorem binding_div_mass_eq :
    s.binding / s.mass = s.velocity ^ 2 * (s.binding / s.momentum ^ 2) * s.mass := by
  rw [binding_div_mass_eq_velocity_sq_mul_coulombRatio, coulombRatio_def]
  ring

/-- Coulombic scaling `E ~ m v²` with constant `K`: the ratio `κ = E / (m v²)` lies in
`[K⁻¹, K]`. This is an assumption about the scales, not a consequence of their ordering
(`exists_not_coulombicScaling`). -/
def CoulombicScaling (K : ℝ) : Prop :=
  s.coulombRatio ∈ Set.Icc K⁻¹ K

variable {s}

@[simp]
theorem coulombicScaling_iff {K : ℝ} :
    s.CoulombicScaling K ↔ s.coulombRatio ∈ Set.Icc K⁻¹ K := Iff.rfl

/-- Coulombic scaling with constant `K` bounds the binding energy between `K⁻¹ m v²` and
`K m v²`. -/
theorem coulombicScaling_iff_binding {K : ℝ} :
    s.CoulombicScaling K ↔
      K⁻¹ * (s.mass * s.velocity ^ 2) ≤ s.binding ∧ s.binding ≤ K * (s.mass * s.velocity ^ 2) := by
  have h : 0 < s.mass * s.velocity ^ 2 := mul_pos s.mass_pos (pow_pos s.velocity_pos 2)
  rw [coulombicScaling_iff, Set.mem_Icc, s.coulombRatio_eq_div, le_div_iff₀ h, div_le_iff₀ h]

/-- The constant in a Coulombic-scaling bound is at least one. -/
theorem CoulombicScaling.one_le {K : ℝ} (h : s.CoulombicScaling K) : 1 ≤ K := by
  obtain ⟨h₁, h₂⟩ := Set.mem_Icc.1 (coulombicScaling_iff.1 h)
  have hK : 0 < K := s.coulombRatio_pos.trans_le h₂
  refine le_of_not_gt fun hK₁ ↦ ?_
  linarith [(one_lt_inv₀ hK).2 hK₁]

/-- Coulombic scaling is preserved by enlarging the constant. -/
theorem CoulombicScaling.mono {K K' : ℝ} (h : s.CoulombicScaling K) (hKK' : K ≤ K') :
    s.CoulombicScaling K' :=
  coulombicScaling_iff.2 <| Set.Icc_subset_Icc (inv_anti₀ (zero_lt_one.trans_le h.one_le) hKK')
    hKK' (coulombicScaling_iff.1 h)

/-- Coulombic scaling with constant one is the exact relation `E = m v²`. -/
theorem coulombicScaling_one_iff : s.CoulombicScaling 1 ↔ s.binding = s.mass * s.velocity ^ 2 := by
  simp only [coulombicScaling_iff_binding, inv_one, one_mul]
  exact ⟨fun h ↦ le_antisymm h.2 h.1, fun h ↦ ⟨h.ge, h.le⟩⟩

/-- The scales with mass `m`, relative momentum `p`, positive hadronic scale `Λ`, and binding
energy `κ p² / m`, whose Coulombic ratio is therefore `κ`. The conditions `0 < κ` and `κ p < m`
are exactly those that place this binding energy in `(0, p)`. -/
noncomputable def ofCoulombRatio {m p : ℝ} (hp : 0 < p) (hpm : p < m) (Λ : ℝ) (hΛ : 0 < Λ)
    {κ : ℝ} (hκ : 0 < κ) (hκ₁ : κ * p < m) : HeavyQuarkScales where
  mass := m
  momentum := p
  binding := κ * p ^ 2 / m
  hadronic := Λ
  binding_pos := by have := hp.trans hpm; positivity
  binding_lt_momentum := by
    rw [div_lt_iff₀ (hp.trans hpm)]
    nlinarith
  momentum_lt_mass := hpm
  hadronic_pos := hΛ

section ofCoulombRatio

variable {m p : ℝ} (hp : 0 < p) (hpm : p < m) (Λ : ℝ) (hΛ : 0 < Λ) {κ : ℝ} (hκ : 0 < κ)
    (hκ₁ : κ * p < m)

@[simp]
theorem mass_ofCoulombRatio : (ofCoulombRatio hp hpm Λ hΛ hκ hκ₁).mass = m := (rfl)

@[simp]
theorem momentum_ofCoulombRatio : (ofCoulombRatio hp hpm Λ hΛ hκ hκ₁).momentum = p := (rfl)

@[simp]
theorem velocity_ofCoulombRatio : (ofCoulombRatio hp hpm Λ hΛ hκ hκ₁).velocity = p / m := by
  rw [velocity_def, mass_ofCoulombRatio, momentum_ofCoulombRatio]

@[simp]
theorem binding_ofCoulombRatio :
    (ofCoulombRatio hp hpm Λ hΛ hκ hκ₁).binding = κ * p ^ 2 / m := (rfl)

@[simp]
theorem hadronic_ofCoulombRatio : (ofCoulombRatio hp hpm Λ hΛ hκ hκ₁).hadronic = Λ := (rfl)

@[simp]
theorem coulombRatio_ofCoulombRatio : (ofCoulombRatio hp hpm Λ hΛ hκ hκ₁).coulombRatio = κ := by
  have := (hp.trans hpm).ne'
  rw [coulombRatio_def, binding_ofCoulombRatio, mass_ofCoulombRatio, momentum_ofCoulombRatio]
  field_simp

end ofCoulombRatio

instance : Nonempty HeavyQuarkScales :=
  ⟨ofCoulombRatio one_pos one_lt_two 1 one_pos one_pos (by rw [one_mul]; exact one_lt_two)⟩

/-- Coulombic scaling is consistent with every mass, relative momentum and positive hadronic
scale. -/
theorem exists_coulombicScaling_one {m p : ℝ} (hp : 0 < p) (hpm : p < m) (Λ : ℝ) (hΛ : 0 < Λ) :
    ∃ s : HeavyQuarkScales, s.mass = m ∧ s.momentum = p ∧ s.hadronic = Λ ∧
      s.CoulombicScaling 1 :=
  ⟨ofCoulombRatio hp hpm Λ hΛ one_pos (by rwa [one_mul]), mass_ofCoulombRatio ..,
    momentum_ofCoulombRatio .., hadronic_ofCoulombRatio .., coulombicScaling_iff.2 <| by
      rw [coulombRatio_ofCoulombRatio, inv_one]; exact Set.left_mem_Icc.2 le_rfl⟩

/-- Coulombic scaling is not a consequence of the ordering `0 < E < p < m`: for every mass,
relative momentum and positive hadronic scale, and every constant `K`, some binding energy
violates it. -/
theorem exists_not_coulombicScaling {m p : ℝ} (hp : 0 < p) (hpm : p < m) (Λ K : ℝ)
    (hΛ : 0 < Λ) :
    ∃ s : HeavyQuarkScales, s.mass = m ∧ s.momentum = p ∧ s.hadronic = Λ ∧
      ¬ s.CoulombicScaling K := by
  have hc : 0 < 2 * (|K| + 1) := by positivity
  have hc₁ : (2 * (|K| + 1))⁻¹ * p < m := by
    have : (2 * (|K| + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [abs_nonneg K])
    nlinarith
  refine ⟨ofCoulombRatio hp hpm Λ hΛ (inv_pos.2 hc) hc₁, mass_ofCoulombRatio ..,
    momentum_ofCoulombRatio .., hadronic_ofCoulombRatio .., fun h ↦ ?_⟩
  have h₁ := (Set.mem_Icc.1 (coulombicScaling_iff.1 h)).1
  rw [coulombRatio_ofCoulombRatio, inv_le_inv₀ (zero_lt_one.trans_le h.one_le) hc] at h₁
  linarith [le_abs_self K]

/-! ### The weakly and strongly coupled regimes -/

variable (s) in
/-- The weakly coupled regime: the hadronic scale lies below the binding energy, `Λ < E`. -/
def WeaklyCoupled : Prop := s.hadronic < s.binding

variable (s) in
/-- The strongly coupled regime: the hadronic scale lies between the binding energy and the
relative momentum, `E < Λ < p`. -/
def StronglyCoupled : Prop := s.binding < s.hadronic ∧ s.hadronic < s.momentum

@[simp]
theorem weaklyCoupled_iff : s.WeaklyCoupled ↔ s.hadronic < s.binding := Iff.rfl

@[simp]
theorem stronglyCoupled_iff :
    s.StronglyCoupled ↔ s.binding < s.hadronic ∧ s.hadronic < s.momentum := Iff.rfl

/-- In the strongly coupled regime the binding energy lies below the hadronic scale. -/
theorem StronglyCoupled.binding_lt_hadronic (h : s.StronglyCoupled) : s.binding < s.hadronic :=
  (stronglyCoupled_iff.1 h).1

/-- In the strongly coupled regime the hadronic scale lies below the relative momentum. -/
theorem StronglyCoupled.hadronic_lt_momentum (h : s.StronglyCoupled) : s.hadronic < s.momentum :=
  (stronglyCoupled_iff.1 h).2

/-- In the weakly coupled regime the hadronic scale lies below the relative momentum, as it does
by definition in the strongly coupled one. -/
theorem WeaklyCoupled.hadronic_lt_momentum (h : s.WeaklyCoupled) : s.hadronic < s.momentum :=
  (weaklyCoupled_iff.1 h).trans s.binding_lt_momentum

/-- The weakly coupled regime excludes the strongly coupled one. -/
theorem WeaklyCoupled.not_stronglyCoupled (h : s.WeaklyCoupled) : ¬ s.StronglyCoupled :=
  fun h' ↦ lt_asymm (weaklyCoupled_iff.1 h) h'.binding_lt_hadronic

/-- The strongly coupled regime excludes the weakly coupled one. -/
theorem StronglyCoupled.not_weaklyCoupled (h : s.StronglyCoupled) : ¬ s.WeaklyCoupled :=
  fun h' ↦ h'.not_stronglyCoupled h

/-- When the hadronic scale lies below the relative momentum and differs from the binding
energy, the pair is in one of the two regimes. -/
theorem weaklyCoupled_or_stronglyCoupled (hE : s.hadronic ≠ s.binding)
    (hp : s.hadronic < s.momentum) : s.WeaklyCoupled ∨ s.StronglyCoupled :=
  hE.lt_or_gt.imp weaklyCoupled_iff.2 fun h ↦ stronglyCoupled_iff.2 ⟨h, hp⟩

/-- The weakly coupled regime is compatible with every mass, relative momentum and binding
energy. -/
theorem exists_weaklyCoupled (s : HeavyQuarkScales) :
    ∃ s' : HeavyQuarkScales, s'.mass = s.mass ∧ s'.momentum = s.momentum ∧
      s'.binding = s.binding ∧ s'.WeaklyCoupled :=
  ⟨{ s with hadronic := s.binding / 2, hadronic_pos := half_pos s.binding_pos }, rfl, rfl, rfl,
    weaklyCoupled_iff.2 (half_lt_self s.binding_pos)⟩

/-- The strongly coupled regime is compatible with every mass, relative momentum and binding
energy. -/
theorem exists_stronglyCoupled (s : HeavyQuarkScales) :
    ∃ s' : HeavyQuarkScales, s'.mass = s.mass ∧ s'.momentum = s.momentum ∧
      s'.binding = s.binding ∧ s'.StronglyCoupled :=
  ⟨{ s with
      hadronic := (s.binding + s.momentum) / 2,
      hadronic_pos := half_pos (add_pos s.binding_pos s.momentum_pos) }, rfl, rfl, rfl,
    stronglyCoupled_iff.2 <| by constructor <;> linarith [s.binding_lt_momentum]⟩

end HeavyQuarkScales

end EpsilonEridani.QFT.Quarkonium
