/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Apply
public import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic
public import PhyslibAlpha.Relativity.Poincare.Causality
public import EpsilonEridani.Relativity.LorentzGroup.Boosts.BasicExtensions
public import EpsilonEridani.Relativity.LorentzGroup.RotationsExtensions
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions

/-!
# The mass shell and the Lorentz map on it

A particle of mass `m` in `d` spatial dimensions has four-momenta on the mass shell
`p⁰ = E(p) = √(m² + |p|²)`. The shell is parametrised by the spatial momentum `p ∈ ℝᵈ`, and a
Lorentz transformation `Λ` moves the point `(E(p), p)` to another point of the shell.

* `onShellEnergy m p` is `E(p)`, and `onShellMomentum m p : Lorentz.Vector d` is the on-shell
  four-momentum `(E(p), p)`, built with `Lorentz.Vector.ofTimeAndSpatial`. Every four-vector with
  Minkowski square `m²` and non-negative energy is of this form
  (`onShellMomentum_spatialPart_of_timeComponent_nonneg`). At `m = 1` it is Physlib's unit
  four-velocity `Lorentz.Velocity.ofSpatialPart` (`onShellMomentum_one_eq_ofSpatialPart`); the
  general mass, `m = 0` included, is what phase space needs.
* `massShellMap Λ m p` is the spatial momentum of `Λ • onShellMomentum m p`: the map `Λ`
  induces on the shell, read in the chart `p`. It is not called an action: for a time-reversing
  `Λ` it does not compose. Whenever `Λ` keeps the energy non-negative, it acts on the shell
  through the map (`onShellMomentum_massShellMap_of_timeComponent_nonneg`), the maps compose
  (`massShellMap_mul_of_timeComponent_nonneg`) and `Λ⁻¹` undoes `Λ`
  (`massShellMap_inv_massShellMap_of_timeComponent_nonneg`). Every orthochronous `Λ` — every
  element of the restricted group in particular — keeps the energy non-negative
  (`timeComponent_smul_onShellMomentum_nonneg`), so for it these hold without side condition
  (`onShellMomentum_massShellMap_of_isOrthochronous`, `massShellMap_mul_of_isOrthochronous`,
  `massShellMap_inv_massShellMap_of_isOrthochronous`).
* A boost along the coordinate axis `i` with velocity `β` sends `pᵢ` to `γ (pᵢ - β E)`, fixes the
  other components, and sends the energy to `E' = γ (E - β pᵢ)`
  (`onShellEnergy_massShellMap_boost`), which is non-negative
  (`timeComponent_boost_smul_onShellMomentum_nonneg`, the boost case of the orthochronous
  lemma). The boost with velocity `-β` undoes it (`massShellMap_boost_neg_boost`).
* A Lorentz transformation `Λ` with time-time entry `1` — a rotation or a spatial reflection —
  is orthochronous (`isOrthochronous_of_timeComponent_eq_one`). It acts on spatial momenta,
  independently of the mass, as the linear isometry equivalence
  `LorentzGroup.spatialLinearIsometryEquiv hΛ` (`massShellMap_eq_spatialLinearIsometryEquiv`),
  and leaves the energy unchanged (`onShellEnergy_massShellMap_of_timeComponent_eq_one`).

The invariant measure on the shell is in
`EpsilonEridani.QFT.Scattering.Kinematics.PhaseSpace`.
-/

public section

noncomputable section

namespace EpsilonEridani

open LorentzGroup
open scoped Lorentz.Vector

variable {d : ℕ}

/-! ### The mass shell -/

/-- The energy `E(p) = √(m² + |p|²)` of a particle of mass `m` and spatial momentum `p`. -/
def onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : ℝ := √(m ^ 2 + ‖p‖ ^ 2)

/-- Defining expression for `onShellEnergy`. -/
theorem onShellEnergy_def (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m p = √(m ^ 2 + ‖p‖ ^ 2) := (rfl)

/-- The energy is non-negative. -/
theorem onShellEnergy_nonneg (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : 0 ≤ onShellEnergy m p :=
  Real.sqrt_nonneg _

/-- The energy of a massive particle is strictly positive. -/
theorem onShellEnergy_pos_of_mass_ne_zero {m : ℝ} (hm : m ≠ 0) (p : EuclideanSpace ℝ (Fin d)) :
    0 < onShellEnergy m p :=
  Real.sqrt_pos.2 (by positivity)

/-- The energy of a particle with non-zero momentum is strictly positive, whatever its mass. -/
theorem onShellEnergy_pos_of_momentum_ne_zero (m : ℝ) {p : EuclideanSpace ℝ (Fin d)}
    (hp : p ≠ 0) : 0 < onShellEnergy m p :=
  Real.sqrt_pos.2 (by have := norm_pos_iff.2 hp; positivity)

/-- A massless particle has energy `|p|`. -/
@[simp]
theorem onShellEnergy_zero_left (p : EuclideanSpace ℝ (Fin d)) : onShellEnergy 0 p = ‖p‖ := by
  simp [onShellEnergy_def, Real.sqrt_sq (norm_nonneg p)]

/-- A particle at rest has energy `|m|`. -/
@[simp]
theorem onShellEnergy_zero_right (m : ℝ) :
    onShellEnergy m (0 : EuclideanSpace ℝ (Fin d)) = |m| := by
  simp [onShellEnergy_def, Real.sqrt_sq_eq_abs]

/-- The square of the energy is `m² + |p|²`. -/
theorem sq_onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m p ^ 2 = m ^ 2 + ‖p‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The energy dominates the size of the spatial momentum. -/
theorem norm_le_onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    ‖p‖ ≤ onShellEnergy m p :=
  Real.le_sqrt_of_sq_le (by nlinarith)

/-- The momentum scaled by a subluminal factor is strictly dominated by a positive energy, in
particular by the energy of a massive particle at rest. -/
theorem abs_mul_norm_lt_onShellEnergy {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    {p : EuclideanSpace ℝ (Fin d)} (hE : 0 < onShellEnergy m p) :
    |β| * ‖p‖ < onShellEnergy m p :=
  (mul_le_mul_of_nonneg_left (norm_le_onShellEnergy m p) (abs_nonneg _)).trans_lt
    (mul_lt_of_lt_one_left hE hβ)

/-- A momentum component scaled by a subluminal factor is strictly dominated by a positive
energy. -/
theorem abs_mul_apply_lt_onShellEnergy {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    {p : EuclideanSpace ℝ (Fin d)} (hE : 0 < onShellEnergy m p) (i : Fin d) :
    |β * p i| < onShellEnergy m p := by
  have hpi : |p i| ≤ ‖p‖ := by simpa using PiLp.norm_apply_le p i
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left hpi (abs_nonneg _)).trans_lt
    (abs_mul_norm_lt_onShellEnergy hβ m hE)

/-- The energy depends continuously on the spatial momentum. -/
@[fun_prop]
theorem continuous_onShellEnergy (m : ℝ) : Continuous (onShellEnergy (d := d) m) := by
  unfold onShellEnergy
  fun_prop

/-- The on-shell four-momentum `(E(p), p)` of a particle of mass `m` and spatial momentum
`p`. -/
def onShellMomentum (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : Lorentz.Vector d :=
  Lorentz.Vector.ofTimeAndSpatial (onShellEnergy m p) p

/-- Defining expression for `onShellMomentum`. -/
theorem onShellMomentum_def (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellMomentum m p = Lorentz.Vector.ofTimeAndSpatial (onShellEnergy m p) p := (rfl)

/-- The time component of the on-shell four-momentum is the energy. -/
@[simp]
theorem timeComponent_onShellMomentum (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    (onShellMomentum m p).timeComponent = onShellEnergy m p := by
  rw [onShellMomentum_def, Lorentz.Vector.timeComponent_ofTimeAndSpatial_eq]

/-- The spatial part of the on-shell four-momentum is the spatial momentum. -/
@[simp]
theorem spatialPart_onShellMomentum (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    (onShellMomentum m p).spatialPart = p := by
  rw [onShellMomentum_def, Lorentz.Vector.spatialPart_ofTimeAndSpatial_eq]

/-- The spatial component `i` of the on-shell four-momentum is `pᵢ`: `spatialPart_onShellMomentum`
in components, through Physlib's `Lorentz.Vector.spatialPart_apply_eq_toCoord`, which is `rfl`. -/
private theorem onShellMomentum_apply_inr (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    onShellMomentum m p (Sum.inr i) = p i := by
  rw [← Lorentz.Vector.spatialPart_apply_eq_toCoord (onShellMomentum m p),
    spatialPart_onShellMomentum]

/-- The on-shell four-momentum depends continuously on the spatial momentum. -/
@[fun_prop]
theorem continuous_onShellMomentum (m : ℝ) : Continuous (onShellMomentum (d := d) m) := by
  unfold onShellMomentum
  simp only [Lorentz.Vector.ofTimeAndSpatial_def]
  exact (Lorentz.Vector.ofTemporalComponent.continuous.comp (continuous_onShellEnergy m)).add
    Lorentz.Vector.ofSpatialComponent.continuous

/-- At unit mass, the on-shell four-momentum is Physlib's unit four-velocity with spatial
part `p`. -/
theorem onShellMomentum_one_eq_ofSpatialPart (p : EuclideanSpace ℝ (Fin d)) :
    onShellMomentum 1 p = (Lorentz.Velocity.ofSpatialPart p).1 := by
  rw [← Lorentz.Vector.ofTimeAndSpatial_timeComponent_spatialPart_eq
      (Lorentz.Velocity.ofSpatialPart p).1, Lorentz.Velocity.timeComponent_ofSpatialPart,
    Lorentz.Velocity.spatialPart_ofSpatialPart, onShellMomentum_def, onShellEnergy_def, one_pow]

/-- The on-shell four-momentum has Minkowski square `m²`. -/
@[simp]
theorem minkowskiProduct_onShellMomentum_self (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    ⟪onShellMomentum m p, onShellMomentum m p⟫ₘ = m ^ 2 := by
  rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub, spatialPart_onShellMomentum,
    timeComponent_onShellMomentum, sq_onShellEnergy, add_sub_cancel_right]

/-- A four-vector with Minkowski square `m²` and non-negative energy is the on-shell
four-momentum of its own spatial part. -/
theorem onShellMomentum_spatialPart_of_timeComponent_nonneg {m : ℝ} {v : Lorentz.Vector d}
    (hv : ⟪v, v⟫ₘ = m ^ 2)
    (h0 : 0 ≤ v.timeComponent) : onShellMomentum m v.spatialPart = v := by
  rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub] at hv
  rw [onShellMomentum_def, onShellEnergy, ← hv, sub_add_cancel, Real.sqrt_sq h0,
    Lorentz.Vector.ofTimeAndSpatial_timeComponent_spatialPart_eq]

/-! ### The map a Lorentz transformation induces on the shell -/

/-- The map a Lorentz transformation induces on the mass shell, read on spatial momenta: the
spatial part of `Λ • (E(p), p)`. -/
def massShellMap (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (Λ • onShellMomentum m p).spatialPart

/-- Defining expression for `massShellMap`. -/
theorem massShellMap_def (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShellMap Λ m p = (Λ • onShellMomentum m p).spatialPart := (rfl)

/-- Component `j` of the map on the shell: `Λʲ₀ E(p) + ∑ₖ Λʲₖ pₖ`. -/
theorem massShellMap_apply (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (j : Fin d) :
    massShellMap Λ m p j =
      Λ.1 (Sum.inr j) (Sum.inl 0) * onShellEnergy m p +
        ∑ k, Λ.1 (Sum.inr j) (Sum.inr k) * p k := by
  simp [massShellMap, Lorentz.Vector.smul_eq_sum, Fintype.sum_sum_type,
    onShellMomentum_apply_inr m p]

/-- An orthochronous Lorentz transformation keeps the energy of an on-shell momentum
non-negative. -/
theorem timeComponent_smul_onShellMomentum_nonneg {Λ : LorentzGroup d} (hΛ : IsOrthochronous Λ)
    (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (Λ • onShellMomentum m p).timeComponent := by
  -- `Λ` preserves the closed future light cone, which contains `(E(p), p)`
  exact (Lorentz.Vector.causallyFollows_zero_iff.1 (PoincareGroup.causallyFollows_zero_smul hΛ
    (Lorentz.Vector.causallyFollows_zero_iff.2
      ⟨by simp [sq_nonneg], by simp [onShellEnergy_nonneg]⟩))).2

/-- When `Λ` keeps the energy of `(E(p), p)` non-negative, `massShellMap` is the Lorentz
action on the shell: `Λ` sends `(E(p), p)` to the on-shell four-momentum of
`massShellMap Λ m p`. -/
theorem onShellMomentum_massShellMap_of_timeComponent_nonneg {Λ : LorentzGroup d} {m : ℝ}
    {p : EuclideanSpace ℝ (Fin d)} (h : 0 ≤ (Λ • onShellMomentum m p).timeComponent) :
    onShellMomentum m (massShellMap Λ m p) = Λ • onShellMomentum m p :=
  onShellMomentum_spatialPart_of_timeComponent_nonneg (by simp) h

/-- An orthochronous Lorentz transformation acts on the shell through `massShellMap`. -/
theorem onShellMomentum_massShellMap_of_isOrthochronous {Λ : LorentzGroup d}
    (hΛ : IsOrthochronous Λ) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellMomentum m (massShellMap Λ m p) = Λ • onShellMomentum m p :=
  onShellMomentum_massShellMap_of_timeComponent_nonneg
    (timeComponent_smul_onShellMomentum_nonneg hΛ m p)

/-- The identity acts trivially on the shell. -/
@[simp]
theorem massShellMap_one (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShellMap 1 m p = p := by
  rw [massShellMap_def, one_smul, spatialPart_onShellMomentum]

/-- The map on the shell composes, as long as `Λ₂`, which acts first, keeps the energy
non-negative — every orthochronous `Λ₂` does. -/
theorem massShellMap_mul_of_timeComponent_nonneg {Λ₁ Λ₂ : LorentzGroup d} {m : ℝ}
    {p : EuclideanSpace ℝ (Fin d)}
    (h : 0 ≤ (Λ₂ • onShellMomentum m p).timeComponent) :
    massShellMap (Λ₁ * Λ₂) m p = massShellMap Λ₁ m (massShellMap Λ₂ m p) := by
  rw [massShellMap_def, massShellMap_def, onShellMomentum_massShellMap_of_timeComponent_nonneg h,
    mul_smul]

/-- The map on the shell of a product whose first factor `Λ₂` is orthochronous is the
composite of the maps. -/
theorem massShellMap_mul_of_isOrthochronous (Λ₁ : LorentzGroup d) {Λ₂ : LorentzGroup d}
    (hΛ₂ : IsOrthochronous Λ₂) (m : ℝ) :
    massShellMap (Λ₁ * Λ₂) m = massShellMap Λ₁ m ∘ massShellMap Λ₂ m :=
  funext fun p =>
    massShellMap_mul_of_timeComponent_nonneg (timeComponent_smul_onShellMomentum_nonneg hΛ₂ m p)

/-- A Lorentz transformation is undone, on the shell, by its own inverse at every momentum
whose energy it keeps non-negative. -/
theorem massShellMap_inv_massShellMap_of_timeComponent_nonneg {Λ : LorentzGroup d} {m : ℝ}
    {p : EuclideanSpace ℝ (Fin d)} (h : 0 ≤ (Λ • onShellMomentum m p).timeComponent) :
    massShellMap Λ⁻¹ m (massShellMap Λ m p) = p := by
  rw [← massShellMap_mul_of_timeComponent_nonneg h, inv_mul_cancel, massShellMap_one]

/-- An orthochronous Lorentz transformation is undone, on the shell, by its own inverse. -/
theorem massShellMap_inv_massShellMap_of_isOrthochronous {Λ : LorentzGroup d}
    (hΛ : IsOrthochronous Λ) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShellMap Λ⁻¹ m (massShellMap Λ m p) = p :=
  massShellMap_inv_massShellMap_of_timeComponent_nonneg
    (timeComponent_smul_onShellMomentum_nonneg hΛ m p)

/-- The map on the shell is continuous in the spatial momentum. -/
@[fun_prop]
theorem continuous_massShellMap (Λ : LorentzGroup d) (m : ℝ) :
    Continuous (massShellMap Λ m) := by
  -- it is the composite of Physlib's continuous linear maps `spatialCLM` and `actionCLM Λ`
  have h : massShellMap Λ m =
      Lorentz.Vector.spatialCLM d ∘ Lorentz.Vector.actionCLM Λ ∘ onShellMomentum m := by
    funext p
    rw [massShellMap_def, Function.comp_apply, Function.comp_apply,
      Lorentz.Vector.spatialCLM_apply, Lorentz.Vector.actionCLM_apply]
  rw [h]
  exact (Lorentz.Vector.spatialCLM d).continuous.comp
    ((Lorentz.Vector.actionCLM Λ).continuous.comp (continuous_onShellMomentum m))

/-! ### Boosts along a coordinate axis -/

/-- A boost along axis `i` sends the component `pᵢ` to `γ (pᵢ - β E)`. -/
theorem massShellMap_boost_apply_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShellMap (boost i β hβ) m p i = γ β * (p i - β * onShellEnergy m p) := by
  simp [massShellMap, Lorentz.Vector.boost_inr_self_eq, onShellMomentum_apply_inr m p]

/-- A boost along axis `i` fixes the components transverse to it. -/
theorem massShellMap_boost_apply_of_ne {i j : Fin d} (hji : j ≠ i) {β : ℝ} (hβ : |β| < 1)
    (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : massShellMap (boost i β hβ) m p j = p j := by
  simp [massShellMap, Lorentz.Vector.boost_inr_other_eq _ _ hji, onShellMomentum_apply_inr m p]

/-- The energy after a boost along axis `i`: `E' = γ (E - β pᵢ)`. -/
theorem timeComponent_boost_smul_onShellMomentum (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    (boost i β hβ • onShellMomentum m p).timeComponent =
      γ β * (onShellEnergy m p - β * p i) := by
  simp [Lorentz.Vector.timeComponent, Lorentz.Vector.boost_time_eq,
    onShellMomentum_apply_inr m p]

/-- A boost along a coordinate axis keeps the energy of an on-shell momentum non-negative. -/
theorem timeComponent_boost_smul_onShellMomentum_nonneg (i : Fin d) {β : ℝ} (hβ : |β| < 1)
    (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (boost i β hβ • onShellMomentum m p).timeComponent :=
  timeComponent_smul_onShellMomentum_nonneg (isOrthochronous_boost i hβ) m p

/-- A boost along axis `i` keeps the energy non-negative, so it acts on the shell through
`massShellMap`. -/
theorem onShellMomentum_massShellMap_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellMomentum m (massShellMap (boost i β hβ) m p) =
      boost i β hβ • onShellMomentum m p :=
  onShellMomentum_massShellMap_of_timeComponent_nonneg
    (timeComponent_boost_smul_onShellMomentum_nonneg i hβ m p)

/-- The energy after a boost along axis `i`, read in the chart: `E' = γ (E - β pᵢ)`. -/
theorem onShellEnergy_massShellMap_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m (massShellMap (boost i β hβ) m p) =
      γ β * (onShellEnergy m p - β * p i) := by
  have h := congrArg Lorentz.Vector.timeComponent (onShellMomentum_massShellMap_boost i hβ m p)
  rwa [timeComponent_onShellMomentum, timeComponent_boost_smul_onShellMomentum] at h

/-- The boost with velocity `-β` along axis `i` undoes the boost with velocity `β` on the
shell: the boost case of `massShellMap_inv_massShellMap_of_timeComponent_nonneg`. -/
theorem massShellMap_boost_neg_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShellMap (boost i (-β) (by rwa [abs_neg])) m (massShellMap (boost i β hβ) m p) =
      p := by
  rw [← boost_inverse i hβ]
  exact massShellMap_inv_massShellMap_of_timeComponent_nonneg
    (timeComponent_boost_smul_onShellMomentum_nonneg i hβ m p)

/-! ### Rotations and spatial reflections -/

/-- For every mass, a Lorentz transformation with time-time entry `1` acts on the shell as its
linear isometry equivalence of spatial momenta. -/
theorem massShellMap_eq_spatialLinearIsometryEquiv {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (m : ℝ) :
    massShellMap Λ m = spatialLinearIsometryEquiv hΛ := by
  funext p
  rw [massShellMap_def, spatialPart_smul_of_timeComponent_eq_one hΛ, spatialPart_onShellMomentum]

/-- A Lorentz transformation with time-time entry `1` — a rotation or a spatial reflection —
preserves the size of the spatial momentum. -/
@[simp]
theorem norm_massShellMap_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    ‖massShellMap Λ m p‖ = ‖p‖ := by
  rw [massShellMap_def, norm_spatialPart_smul_of_timeComponent_eq_one hΛ,
    spatialPart_onShellMomentum]

/-- A Lorentz transformation with time-time entry `1` — a rotation or a spatial reflection —
does not change the energy. -/
@[simp]
theorem onShellEnergy_massShellMap_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m (massShellMap Λ m p) = onShellEnergy m p := by
  rw [onShellEnergy_def, onShellEnergy_def, norm_massShellMap_of_timeComponent_eq_one hΛ]

end EpsilonEridani
