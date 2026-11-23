/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Physlib.Relativity.LorentzGroup.Boosts.Apply
public import EpsilonEridani.Relativity.LorentzGroup.Boosts.BasicExtensions
public import EpsilonEridani.Relativity.LorentzGroup.RotationsExtensions
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions

/-!
# The mass shell and the Lorentz action on it

A particle of mass `m` in `d` spatial dimensions has four-momenta on the mass shell
`p⁰ = E(p) = √(m² + |p|²)`. The shell is parametrised by the spatial momentum `p ∈ ℝᵈ`, and a
Lorentz transformation `Λ` moves the point `(E(p), p)` to another point of the shell.

* `onShellEnergy m p` is `E(p)`, and `massShell m p : Lorentz.Vector d` is the on-shell
  four-momentum `(E(p), p)`, built with `Lorentz.Vector.ofTimeAndSpatial`.
  `massShell_spatialPart` says that every four-vector with Minkowski square `m²` and non-negative
  energy is of this form.
* `massShellAction Λ m p` is the spatial momentum of `Λ • massShell m p`: the action of `Λ` on
  the shell, read in the chart `p`. `massShell_massShellAction` identifies it with the Lorentz
  action when `Λ` keeps the energy non-negative, and `massShellAction_mul` shows that it composes.
* A boost along the coordinate axis `i` with velocity `β` sends `pᵢ` to `γ (pᵢ - β E)`, fixes the
  other components, and sends the energy to `E' = γ (E - β pᵢ)`
  (`onShellEnergy_massShellAction_boost`), which is non-negative.
* A rotation `Λ` acts on spatial momenta through its spatial block, independently of the mass,
  as the linear isometry `massShellActionₗᵢ Λ` (`coe_massShellActionₗᵢ`), and leaves the energy
  unchanged (`onShellEnergy_massShellAction_rotation`).

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

theorem onShellEnergy_nonneg (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : 0 ≤ onShellEnergy m p :=
  Real.sqrt_nonneg _

/-- The energy of a massive particle is strictly positive. -/
theorem onShellEnergy_pos {m : ℝ} (hm : m ≠ 0) (p : EuclideanSpace ℝ (Fin d)) :
    0 < onShellEnergy m p :=
  Real.sqrt_pos.2 (by positivity)

/-- The energy of a particle with non-zero momentum is strictly positive, whatever its mass. -/
theorem onShellEnergy_pos_of_ne_zero (m : ℝ) {p : EuclideanSpace ℝ (Fin d)} (hp : p ≠ 0) :
    0 < onShellEnergy m p :=
  Real.sqrt_pos.2 (by have := norm_pos_iff.2 hp; positivity)

theorem sq_onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m p ^ 2 = m ^ 2 + ‖p‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The energy dominates the size of the spatial momentum. -/
theorem norm_le_onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    ‖p‖ ≤ onShellEnergy m p :=
  Real.le_sqrt_of_sq_le (by nlinarith)

@[fun_prop]
theorem continuous_onShellEnergy (m : ℝ) : Continuous (onShellEnergy (d := d) m) := by
  unfold onShellEnergy
  fun_prop

/-- The on-shell four-momentum `(E(p), p)` of a particle of mass `m` and spatial momentum
`p`. -/
def massShell (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : Lorentz.Vector d :=
  Lorentz.Vector.ofTimeAndSpatial (onShellEnergy m p) p

theorem massShell_def (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShell m p = Lorentz.Vector.ofTimeAndSpatial (onShellEnergy m p) p := (rfl)

@[simp]
theorem timeComponent_massShell (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    (massShell m p).timeComponent = onShellEnergy m p := by
  rw [massShell_def, Lorentz.Vector.timeComponent_ofTimeAndSpatial_eq]

@[simp]
theorem spatialPart_massShell (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    (massShell m p).spatialPart = p := by
  rw [massShell_def, Lorentz.Vector.spatialPart_ofTimeAndSpatial_eq]

@[simp]
theorem massShell_inr (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    massShell m p (Sum.inr i) = p i := by
  rw [← Lorentz.Vector.spatialPart_apply_eq_toCoord (massShell m p), spatialPart_massShell]

@[fun_prop]
theorem continuous_massShell (m : ℝ) : Continuous (massShell (d := d) m) := by
  rw [funext (massShell_def (d := d) m)]
  simp only [Lorentz.Vector.ofTimeAndSpatial_def]
  exact (Lorentz.Vector.ofTemporalComponent.continuous.comp (continuous_onShellEnergy m)).add
    Lorentz.Vector.ofSpatialComponent.continuous

/-- The on-shell four-momentum has Minkowski square `m²`. -/
@[simp]
theorem minkowskiProduct_massShell_self (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    ⟪massShell m p, massShell m p⟫ₘ = m ^ 2 := by
  rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub, spatialPart_massShell,
    timeComponent_massShell, sq_onShellEnergy, add_sub_cancel_right]

/-- A four-vector with Minkowski square `m²` and non-negative energy is the on-shell
four-momentum of its own spatial part. -/
theorem massShell_spatialPart {m : ℝ} {v : Lorentz.Vector d} (hv : ⟪v, v⟫ₘ = m ^ 2)
    (h0 : 0 ≤ v.timeComponent) : massShell m v.spatialPart = v := by
  rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub] at hv
  rw [massShell_def, onShellEnergy, ← hv, sub_add_cancel, Real.sqrt_sq h0,
    Lorentz.Vector.ofTimeAndSpatial_timeComponent_spatialPart_eq]

/-! ### The action of the Lorentz group on the shell -/

/-- The action of a Lorentz transformation on the mass shell, read on spatial momenta: the
spatial part of `Λ • (E(p), p)`. -/
def massShellAction (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (Λ • massShell m p).spatialPart

theorem massShellAction_def (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShellAction Λ m p = (Λ • massShell m p).spatialPart := (rfl)

theorem massShellAction_apply (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (j : Fin d) :
    massShellAction Λ m p j =
      Λ.1 (Sum.inr j) (Sum.inl 0) * onShellEnergy m p +
        ∑ k, Λ.1 (Sum.inr j) (Sum.inr k) * p k := by
  simp [massShellAction, Lorentz.Vector.smul_eq_sum, Fintype.sum_sum_type]

/-- When `Λ` keeps the energy of `(E(p), p)` non-negative, `massShellAction` is the Lorentz
action on the shell: `Λ` sends `(E(p), p)` to the on-shell four-momentum of
`massShellAction Λ m p`. -/
theorem massShell_massShellAction {Λ : LorentzGroup d} {m : ℝ} {p : EuclideanSpace ℝ (Fin d)}
    (h : 0 ≤ (Λ • massShell m p).timeComponent) :
    massShell m (massShellAction Λ m p) = Λ • massShell m p :=
  massShell_spatialPart (by simp) h

@[simp]
theorem massShellAction_one (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShellAction 1 m p = p := by
  rw [massShellAction_def, one_smul, spatialPart_massShell]

/-- The action on the shell composes, as long as `Λ₂`, which acts first, keeps the energy
non-negative. -/
theorem massShellAction_mul {Λ₁ Λ₂ : LorentzGroup d} {m : ℝ} {p : EuclideanSpace ℝ (Fin d)}
    (h : 0 ≤ (Λ₂ • massShell m p).timeComponent) :
    massShellAction (Λ₁ * Λ₂) m p = massShellAction Λ₁ m (massShellAction Λ₂ m p) := by
  rw [massShellAction_def, massShellAction_def, massShell_massShellAction h, mul_smul]

@[fun_prop]
theorem continuous_massShellAction (Λ : LorentzGroup d) (m : ℝ) :
    Continuous (massShellAction Λ m) := by
  have h : massShellAction Λ m =
      Lorentz.Vector.spatialCLM d ∘ Lorentz.Vector.actionCLM Λ ∘ massShell m := by
    funext p
    ext j
    rw [massShellAction_def, Function.comp_apply, Function.comp_apply,
      Lorentz.Vector.spatialCLM_apply_eq_spatialPart, Lorentz.Vector.actionCLM_apply]
  rw [h]
  exact (Lorentz.Vector.spatialCLM d).continuous.comp
    ((Lorentz.Vector.actionCLM Λ).continuous.comp (continuous_massShell m))

/-! ### Boosts along a coordinate axis -/

theorem massShellAction_boost_apply_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShellAction (boost i β hβ) m p i = γ β * (p i - β * onShellEnergy m p) := by
  simp [massShellAction, Lorentz.Vector.boost_inr_self_eq]

theorem massShellAction_boost_apply_of_ne {i j : Fin d} (hji : j ≠ i) {β : ℝ} (hβ : |β| < 1)
    (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : massShellAction (boost i β hβ) m p j = p j := by
  simp [massShellAction, Lorentz.Vector.boost_inr_other_eq _ _ hji]

/-- The energy after a boost along axis `i`: `E' = γ (E - β pᵢ)`. -/
theorem timeComponent_boost_smul_massShell (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    (boost i β hβ • massShell m p).timeComponent = γ β * (onShellEnergy m p - β * p i) := by
  simp [Lorentz.Vector.timeComponent, Lorentz.Vector.boost_time_eq]

theorem massShell_massShellAction_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShell m (massShellAction (boost i β hβ) m p) = boost i β hβ • massShell m p := by
  refine massShell_massShellAction ?_
  rw [timeComponent_boost_smul_massShell]
  have hpi : |p i| ≤ ‖p‖ := by simpa using PiLp.norm_apply_le p i
  have hp : |p i| ≤ onShellEnergy m p := hpi.trans (norm_le_onShellEnergy m p)
  refine mul_nonneg (γ_pos hβ).le (sub_nonneg.2 ((le_abs_self _).trans ?_))
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hβ.le).trans hp

/-- The energy after a boost along axis `i`, read in the chart: `E' = γ (E - β pᵢ)`. -/
theorem onShellEnergy_massShellAction_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m (massShellAction (boost i β hβ) m p) =
      γ β * (onShellEnergy m p - β * p i) := by
  have h := congrArg Lorentz.Vector.timeComponent (massShell_massShellAction_boost i hβ m p)
  rwa [timeComponent_massShell, timeComponent_boost_smul_massShell] at h

/-! ### Rotations -/

/-- A rotation acts on spatial momenta through its spatial block, whatever the mass. -/
theorem massShellAction_rotation_apply (Λ : Rotations d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (j : Fin d) :
    massShellAction Λ m p j = ∑ k, (Λ : LorentzGroup d).1 (Sum.inr j) (Sum.inr k) * p k := by
  rw [massShellAction_def, spatialPart_rotation_smul_apply, spatialPart_massShell]

/-- A rotation preserves the size of the spatial momentum. -/
theorem norm_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) : ‖massShellAction Λ m p‖ = ‖p‖ := by
  rw [massShellAction_def, norm_spatialPart_rotation_smul, spatialPart_massShell]

/-- The action of a rotation `Λ` on spatial momenta as a linear isometry: the spatial part of
`Λ • (0, p)`. By `coe_massShellActionₗᵢ` it is `massShellAction Λ m` for every mass `m`. -/
def massShellActionₗᵢ (Λ : Rotations d) :
    EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) where
  toLinearMap := ((Lorentz.Vector.spatialCLM d).comp ((Lorentz.Vector.actionCLM Λ).comp
    Lorentz.Vector.ofSpatialComponent)).toLinearMap
  norm_map' p := by
    change ‖((Λ : LorentzGroup d) • Lorentz.Vector.ofSpatialComponent p).spatialPart‖ = ‖p‖
    rw [norm_spatialPart_rotation_smul, Lorentz.Vector.spatialPart_ofSpatialComponent]

/-- The linear isometry of a rotation is its action on the mass shell, for every mass. -/
theorem coe_massShellActionₗᵢ (Λ : Rotations d) (m : ℝ) :
    ⇑(massShellActionₗᵢ Λ) = massShellAction Λ m := by
  funext p
  ext j
  change ((Λ : LorentzGroup d) • Lorentz.Vector.ofSpatialComponent p).spatialPart j = _
  rw [spatialPart_rotation_smul_apply, Lorentz.Vector.spatialPart_ofSpatialComponent,
    massShellAction_rotation_apply]

theorem massShell_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShell m (massShellAction Λ m p) = (Λ : LorentzGroup d) • massShell m p :=
  massShell_massShellAction <| by
    rw [timeComponent_rotation_smul, timeComponent_massShell]
    exact onShellEnergy_nonneg m p

/-- A rotation does not change the energy. -/
theorem onShellEnergy_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m (massShellAction Λ m p) = onShellEnergy m p := by
  rw [onShellEnergy_def, onShellEnergy_def, norm_massShellAction_rotation]

end EpsilonEridani
