/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.LorentzGroup.Boosts.Apply
public import Physlib.Relativity.Tensors.RealTensor.Velocity.Basic
public import EpsilonEridani.Relativity.LorentzGroup.Boosts.BasicExtensions
public import EpsilonEridani.Relativity.LorentzGroup.RotationsExtensions
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions

/-!
# The mass shell and the Lorentz action on it

A particle of mass `m` in `d` spatial dimensions has four-momenta on the mass shell
`p⁰ = E(p) = √(m² + |p|²)`. The shell is parametrised by the spatial momentum `p ∈ ℝᵈ`, and a
Lorentz transformation `Λ` moves the point `(E(p), p)` to another point of the shell.

* `onShellEnergy m p` is `E(p)`, and `onShellMomentum m p : Lorentz.Vector d` is the on-shell
  four-momentum `(E(p), p)`, built with `Lorentz.Vector.ofTimeAndSpatial`.
  `onShellMomentum_spatialPart` says that every four-vector with Minkowski square `m²` and
  non-negative energy is of this form. At `m = 1` it is Physlib's unit four-velocity
  `Lorentz.Velocity.ofSpatialPart` (`onShellMomentum_one`); the general mass, `m = 0` included,
  is what phase space needs.
* `massShellAction Λ m p` is the spatial momentum of `Λ • onShellMomentum m p`: the action of `Λ`
  on the shell, read in the chart `p`. `onShellMomentum_massShellAction` identifies it with the
  Lorentz action when `Λ` keeps the energy non-negative, and `massShellAction_mul` shows that it
  composes.
* A boost along the coordinate axis `i` with velocity `β` sends `pᵢ` to `γ (pᵢ - β E)`, fixes the
  other components, and sends the energy to `E' = γ (E - β pᵢ)`
  (`onShellEnergy_massShellAction_boost`), which is non-negative
  (`timeComponent_boost_smul_onShellMomentum_nonneg`). The boost with velocity `-β` undoes it
  (`massShellAction_boost_neg_boost`).
* A rotation `Λ` keeps the energy non-negative
  (`timeComponent_rotation_smul_onShellMomentum_nonneg`), acts on spatial momenta through its
  spatial block, independently of the mass, as the linear isometry equivalence
  `LorentzGroup.Rotations.toLinearIsometryEquiv Λ` (`massShellAction_rotation`), and leaves the
  energy unchanged (`onShellEnergy_massShellAction_rotation`).

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

/-- The square of the energy is `m² + |p|²`. -/
theorem sq_onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m p ^ 2 = m ^ 2 + ‖p‖ ^ 2 :=
  Real.sq_sqrt (by positivity)

/-- The energy dominates the size of the spatial momentum. -/
theorem norm_le_onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    ‖p‖ ≤ onShellEnergy m p :=
  Real.le_sqrt_of_sq_le (by nlinarith)

/-- A momentum component scaled by a factor of size at most one is dominated by the energy. -/
theorem abs_mul_apply_le_onShellEnergy {β : ℝ} (hβ : |β| ≤ 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |β * p i| ≤ onShellEnergy m p := by
  have hpi : |p i| ≤ ‖p‖ := by simpa using PiLp.norm_apply_le p i
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hβ).trans (hpi.trans (norm_le_onShellEnergy m p))

/-- For a non-zero momentum, a component scaled by a subluminal factor is strictly dominated by
the energy. -/
theorem abs_mul_apply_lt_onShellEnergy {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    {p : EuclideanSpace ℝ (Fin d)} (hp : p ≠ 0) (i : Fin d) : |β * p i| < onShellEnergy m p := by
  have hpi : |p i| ≤ ‖p‖ := by simpa using PiLp.norm_apply_le p i
  rw [abs_mul]
  calc |β| * |p i| ≤ |β| * ‖p‖ := mul_le_mul_of_nonneg_left hpi (abs_nonneg _)
    _ < ‖p‖ := mul_lt_of_lt_one_left (norm_pos_iff.2 hp) hβ
    _ ≤ onShellEnergy m p := norm_le_onShellEnergy m p

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

/-- The spatial component `i` of the on-shell four-momentum is `pᵢ`. -/
@[simp]
theorem onShellMomentum_inr (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    onShellMomentum m p (Sum.inr i) = p i := by
  rw [← Lorentz.Vector.spatialPart_apply_eq_toCoord (onShellMomentum m p),
    spatialPart_onShellMomentum]

/-- The on-shell four-momentum depends continuously on the spatial momentum. -/
@[fun_prop]
theorem continuous_onShellMomentum (m : ℝ) : Continuous (onShellMomentum (d := d) m) := by
  rw [funext (onShellMomentum_def (d := d) m)]
  simp only [Lorentz.Vector.ofTimeAndSpatial_def]
  exact (Lorentz.Vector.ofTemporalComponent.continuous.comp (continuous_onShellEnergy m)).add
    Lorentz.Vector.ofSpatialComponent.continuous

/-- At unit mass, the on-shell four-momentum is Physlib's unit four-velocity with spatial
part `p`. -/
theorem onShellMomentum_one (p : EuclideanSpace ℝ (Fin d)) :
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
theorem onShellMomentum_spatialPart {m : ℝ} {v : Lorentz.Vector d} (hv : ⟪v, v⟫ₘ = m ^ 2)
    (h0 : 0 ≤ v.timeComponent) : onShellMomentum m v.spatialPart = v := by
  rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub] at hv
  rw [onShellMomentum_def, onShellEnergy, ← hv, sub_add_cancel, Real.sqrt_sq h0,
    Lorentz.Vector.ofTimeAndSpatial_timeComponent_spatialPart_eq]

/-! ### The action of the Lorentz group on the shell -/

/-- The action of a Lorentz transformation on the mass shell, read on spatial momenta: the
spatial part of `Λ • (E(p), p)`. -/
def massShellAction (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  (Λ • onShellMomentum m p).spatialPart

/-- Defining expression for `massShellAction`. -/
theorem massShellAction_def (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShellAction Λ m p = (Λ • onShellMomentum m p).spatialPart := (rfl)

/-- Component `j` of the action on the shell: `Λʲ₀ E(p) + ∑ₖ Λʲₖ pₖ`. -/
theorem massShellAction_apply (Λ : LorentzGroup d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (j : Fin d) :
    massShellAction Λ m p j =
      Λ.1 (Sum.inr j) (Sum.inl 0) * onShellEnergy m p +
        ∑ k, Λ.1 (Sum.inr j) (Sum.inr k) * p k := by
  simp [massShellAction, Lorentz.Vector.smul_eq_sum, Fintype.sum_sum_type]

/-- When `Λ` keeps the energy of `(E(p), p)` non-negative, `massShellAction` is the Lorentz
action on the shell: `Λ` sends `(E(p), p)` to the on-shell four-momentum of
`massShellAction Λ m p`. -/
theorem onShellMomentum_massShellAction {Λ : LorentzGroup d} {m : ℝ}
    {p : EuclideanSpace ℝ (Fin d)} (h : 0 ≤ (Λ • onShellMomentum m p).timeComponent) :
    onShellMomentum m (massShellAction Λ m p) = Λ • onShellMomentum m p :=
  onShellMomentum_spatialPart (by simp) h

/-- The identity acts trivially on the shell. -/
@[simp]
theorem massShellAction_one (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    massShellAction 1 m p = p := by
  rw [massShellAction_def, one_smul, spatialPart_onShellMomentum]

/-- The action on the shell composes, as long as `Λ₂`, which acts first, keeps the energy
non-negative. -/
theorem massShellAction_mul {Λ₁ Λ₂ : LorentzGroup d} {m : ℝ} {p : EuclideanSpace ℝ (Fin d)}
    (h : 0 ≤ (Λ₂ • onShellMomentum m p).timeComponent) :
    massShellAction (Λ₁ * Λ₂) m p = massShellAction Λ₁ m (massShellAction Λ₂ m p) := by
  rw [massShellAction_def, massShellAction_def, onShellMomentum_massShellAction h, mul_smul]

/-- The action on the shell is continuous in the spatial momentum. -/
@[fun_prop]
theorem continuous_massShellAction (Λ : LorentzGroup d) (m : ℝ) :
    Continuous (massShellAction Λ m) := by
  -- it is the composite of Physlib's continuous linear maps `spatialCLM` and `actionCLM Λ`
  have h : massShellAction Λ m =
      Lorentz.Vector.spatialCLM d ∘ Lorentz.Vector.actionCLM Λ ∘ onShellMomentum m := by
    funext p
    rw [massShellAction_def, Function.comp_apply, Function.comp_apply,
      Lorentz.Vector.spatialCLM_apply, Lorentz.Vector.actionCLM_apply]
  rw [h]
  exact (Lorentz.Vector.spatialCLM d).continuous.comp
    ((Lorentz.Vector.actionCLM Λ).continuous.comp (continuous_onShellMomentum m))

/-! ### Boosts along a coordinate axis -/

/-- A boost along axis `i` sends the component `pᵢ` to `γ (pᵢ - β E)`. -/
theorem massShellAction_boost_apply_self (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShellAction (boost i β hβ) m p i = γ β * (p i - β * onShellEnergy m p) := by
  simp [massShellAction, Lorentz.Vector.boost_inr_self_eq]

/-- A boost along axis `i` fixes the components transverse to it. -/
theorem massShellAction_boost_apply_of_ne {i j : Fin d} (hji : j ≠ i) {β : ℝ} (hβ : |β| < 1)
    (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : massShellAction (boost i β hβ) m p j = p j := by
  simp [massShellAction, Lorentz.Vector.boost_inr_other_eq _ _ hji]

/-- The energy after a boost along axis `i`: `E' = γ (E - β pᵢ)`. -/
theorem timeComponent_boost_smul_onShellMomentum (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    (boost i β hβ • onShellMomentum m p).timeComponent =
      γ β * (onShellEnergy m p - β * p i) := by
  simp [Lorentz.Vector.timeComponent, Lorentz.Vector.boost_time_eq]

/-- A boost along a coordinate axis keeps the energy of an on-shell momentum non-negative. -/
theorem timeComponent_boost_smul_onShellMomentum_nonneg (i : Fin d) {β : ℝ} (hβ : |β| < 1)
    (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    0 ≤ (boost i β hβ • onShellMomentum m p).timeComponent := by
  rw [timeComponent_boost_smul_onShellMomentum]
  exact mul_nonneg (γ_pos hβ).le
    (sub_nonneg.2 ((le_abs_self _).trans (abs_mul_apply_le_onShellEnergy hβ.le m p i)))

/-- A boost along axis `i` keeps the energy non-negative, so it acts on the shell through
`massShellAction`. -/
theorem onShellMomentum_massShellAction_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellMomentum m (massShellAction (boost i β hβ) m p) =
      boost i β hβ • onShellMomentum m p :=
  onShellMomentum_massShellAction (timeComponent_boost_smul_onShellMomentum_nonneg i hβ m p)

/-- The energy after a boost along axis `i`, read in the chart: `E' = γ (E - β pᵢ)`. -/
theorem onShellEnergy_massShellAction_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m (massShellAction (boost i β hβ) m p) =
      γ β * (onShellEnergy m p - β * p i) := by
  have h := congrArg Lorentz.Vector.timeComponent (onShellMomentum_massShellAction_boost i hβ m p)
  rwa [timeComponent_onShellMomentum, timeComponent_boost_smul_onShellMomentum] at h

/-- The boost with velocity `-β` along axis `i` undoes the boost with velocity `β` on the
shell. -/
theorem massShellAction_boost_neg_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShellAction (boost i (-β) (by rwa [abs_neg])) m (massShellAction (boost i β hβ) m p) =
      p := by
  rw [← massShellAction_mul (timeComponent_boost_smul_onShellMomentum_nonneg i hβ m p),
    ← boost_inverse i hβ, inv_mul_cancel, massShellAction_one]

/-! ### Rotations -/

/-- A rotation keeps the energy of an on-shell momentum non-negative. -/
theorem timeComponent_rotation_smul_onShellMomentum_nonneg (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    0 ≤ ((Λ : LorentzGroup d) • onShellMomentum m p).timeComponent := by
  rw [timeComponent_rotation_smul, timeComponent_onShellMomentum]
  exact onShellEnergy_nonneg m p

/-- A rotation keeps the energy non-negative, so it acts on the shell through
`massShellAction`. -/
theorem onShellMomentum_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellMomentum m (massShellAction Λ m p) = (Λ : LorentzGroup d) • onShellMomentum m p :=
  onShellMomentum_massShellAction (timeComponent_rotation_smul_onShellMomentum_nonneg Λ m p)

/-- A rotation acts on spatial momenta through its spatial block, whatever the mass. -/
theorem massShellAction_rotation_apply (Λ : Rotations d) (m : ℝ) (p : EuclideanSpace ℝ (Fin d))
    (j : Fin d) :
    massShellAction Λ m p j = ∑ k, (Λ : LorentzGroup d).1 (Sum.inr j) (Sum.inr k) * p k := by
  rw [massShellAction_apply, rotation_inr_inl_eq_zero, zero_mul, zero_add]

/-- For every mass, a rotation acts on the shell as its linear isometry equivalence of spatial
momenta. -/
theorem massShellAction_rotation (Λ : Rotations d) (m : ℝ) :
    massShellAction Λ m = Rotations.toLinearIsometryEquiv Λ := by
  funext p
  rw [massShellAction_def, spatialPart_rotation_smul, spatialPart_onShellMomentum]

/-- A rotation preserves the size of the spatial momentum. -/
@[simp]
theorem norm_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) : ‖massShellAction Λ m p‖ = ‖p‖ := by
  rw [massShellAction_def, norm_spatialPart_rotation_smul, spatialPart_onShellMomentum]

/-- A rotation does not change the energy. -/
@[simp]
theorem onShellEnergy_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m (massShellAction Λ m p) = onShellEnergy m p := by
  rw [onShellEnergy_def, onShellEnergy_def, norm_massShellAction_rotation]

end EpsilonEridani
