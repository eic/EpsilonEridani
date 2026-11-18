/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Physlib.Relativity.LorentzGroup.Boosts.Apply
public import EpsilonEridani.Relativity.LorentzGroup.Boosts.BasicExtensions
public import EpsilonEridani.Relativity.LorentzGroup.RotationsExtensions
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.BasicExtensions

/-!
# The Lorentz-invariant one-body phase-space measure

A particle of mass `m` in `d` spatial dimensions has four-momenta on the mass shell
`p⁰ = E(p) = √(m² + |p|²)`. The shell is parametrised by the spatial momentum `p ∈ ℝᵈ`, and the
invariant one-body measure is

  `d^d p / (2 E(p))`,

Lebesgue measure on the spatial momenta with density `1 / (2E)`. Its invariance under Lorentz
transformations is the reason phase space is written this way: a Lorentz transformation `Λ` moves
the point `(E(p), p)` to another point of the shell. The induced map on spatial momenta does not
preserve `d^d p`, but its Jacobian `E(Λp) / E(p)` is cancelled exactly by the density.

* `onShellEnergy m p` is `E(p)`, and `massShell m p : Lorentz.Vector d` is the on-shell
  four-momentum `(E(p), p)`, built with `Lorentz.Vector.ofTimeAndSpatial`.
  `massShell_spatialPart` says that every four-vector with Minkowski square `m²` and non-negative
  energy is of this form.
* `massShellAction Λ m p` is the spatial momentum of `Λ • massShell m p`: the action of `Λ` on
  the shell, read in the chart `p`. `massShell_massShellAction` identifies it with the Lorentz
  action when `Λ` keeps the energy non-negative, and `massShellAction_mul` shows that it composes.
* `oneBodyMeasure m` is `d^d p / (2E)`, a σ-finite measure on `EuclideanSpace ℝ (Fin d)`. The
  massless case `m = 0` is included. There the density is singular at `p = 0`, a null set.
* `measurePreserving_massShellAction_boost`: a boost along any coordinate axis preserves
  `oneBodyMeasure m`. Along the boost axis, at fixed transverse momentum `p_⊥`, the energy is
  `√(m² + |p_⊥|² + q²)` and the boost acts as `q ↦ γ (q - β E)`, a bijection of the line with
  derivative `E' / E`, where `E' = γ (E - β q)` is the boosted energy.
* `measurePreserving_massShellAction_rotation`: a spatial rotation preserves it, since it acts on
  `p` as a linear isometry and leaves `E` unchanged.

Rotations and axis boosts both keep the energy non-negative, so by `massShellAction_mul` the
action of any finite product of them is the composite of their actions, and preserves
`oneBodyMeasure m` as well.

## References

* E. Byckling and K. Kajantie, *Particle Kinematics*, Wiley (1973), for the invariant
  one-particle phase space and its Lorentz invariance.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace Kinematics
namespace PhaseSpace

open MeasureTheory LorentzGroup
open scoped ENNReal Lorentz.Vector

variable {d : ℕ}

/-! ### The mass shell -/

/-- The energy `E(p) = √(m² + |p|²)` of a particle of mass `m` and spatial momentum `p`. -/
def onShellEnergy (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : ℝ := √(m ^ 2 + ‖p‖ ^ 2)

/-- Defining expression for `onShellEnergy`. -/
theorem onShellEnergy_def (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m p = √(m ^ 2 + ‖p‖ ^ 2) := (rfl)

theorem onShellEnergy_nonneg (m : ℝ) (p : EuclideanSpace ℝ (Fin d)) : 0 ≤ onShellEnergy m p :=
  Real.sqrt_nonneg _

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
  simp [massShellAction, Lorentz.Vector.smul_eq_mulVec, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type]

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
  have h : massShellAction Λ m = fun p => WithLp.toLp 2 fun j =>
      Λ.1 (Sum.inr j) (Sum.inl 0) * onShellEnergy m p +
        ∑ k, Λ.1 (Sum.inr j) (Sum.inr k) * p k := by
    funext p
    ext j
    exact massShellAction_apply Λ m p j
  rw [h]
  fun_prop

/-! ### The one-body measure -/

/-- The Lorentz-invariant one-body phase-space measure `d^d p / (2 E(p))` on the spatial
momenta of a particle of mass `m`. -/
def oneBodyMeasure (m : ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  volume.withDensity fun p => ENNReal.ofReal (2 * onShellEnergy m p)⁻¹

theorem oneBodyMeasure_def (m : ℝ) :
    oneBodyMeasure (d := d) m =
      volume.withDensity fun p => ENNReal.ofReal (2 * onShellEnergy m p)⁻¹ :=
  (rfl)

instance (m : ℝ) : SigmaFinite (oneBodyMeasure (d := d) m) := by
  rw [oneBodyMeasure_def]
  exact SigmaFinite.withDensity_ofReal _

private theorem measurable_density (m : ℝ) :
    Measurable fun p : EuclideanSpace ℝ (Fin d) => ENNReal.ofReal (2 * onShellEnergy m p)⁻¹ :=
  ENNReal.measurable_ofReal.comp ((continuous_onShellEnergy m).measurable.const_mul 2).inv

/-- Integrating against `oneBodyMeasure m` is integrating against Lebesgue measure with the
weight `1 / (2E)`. -/
theorem lintegral_oneBodyMeasure (m : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ p, f p ∂oneBodyMeasure m = ∫⁻ p, ENNReal.ofReal (2 * onShellEnergy m p)⁻¹ * f p :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_density m)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f

/-! ### Boosts along a coordinate axis -/

private theorem mul_le_sqrt_add_sq {a β q : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) :
    β * q ≤ √(a + q ^ 2) := by
  have hq : |q| ≤ √(a + q ^ 2) := Real.abs_le_sqrt (by linarith)
  calc β * q ≤ |β| * |q| := (le_abs_self _).trans (abs_mul _ _).le
    _ ≤ 1 * |q| := by gcongr
    _ ≤ _ := by simpa using hq

private theorem mul_lt_sqrt_add_sq {a β q : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) (hq : q ≠ 0) :
    β * q < √(a + q ^ 2) := by
  have hq' : |q| ≤ √(a + q ^ 2) := Real.abs_le_sqrt (by linarith)
  have hqpos : 0 < |q| := abs_pos.2 hq
  calc β * q ≤ |β| * |q| := (le_abs_self _).trans (abs_mul _ _).le
    _ < 1 * |q| := by gcongr
    _ ≤ _ := by simpa using hq'

/-- In `1 + 1` dimensions with transverse mass `√a`, the boosted momentum
`q' = γ (q - β E)` has energy `E' = γ (E - β q)`. -/
private theorem sqrt_add_sq_boost {a β : ℝ} (q : ℝ) (ha : 0 ≤ a) (hβ : |β| < 1) :
    √(a + (γ β * (q - β * √(a + q ^ 2))) ^ 2) = γ β * (√(a + q ^ 2) - β * q) := by
  have h1 : γ β ^ 2 * (1 - β ^ 2) = 1 := by
    have : 1 - β ^ 2 ≠ 0 := (sub_pos.2 ((sq_lt_one_iff_abs_lt_one β).2 hβ)).ne'
    rw [γ_sq β hβ]
    field_simp
  have hE : √(a + q ^ 2) ^ 2 = a + q ^ 2 := Real.sq_sqrt (by positivity)
  rw [← Real.sqrt_sq (mul_nonneg (γ_pos hβ).le (sub_nonneg.2 (mul_le_sqrt_add_sq ha hβ)))]
  congr 1
  linear_combination (-a) * h1 + (-(γ β ^ 2 * (1 - β ^ 2))) * hE

/-- The boost with velocity `-β` undoes the boost with velocity `β` on the line of transverse
mass `√a`. -/
private theorem boost_neg_boost {a β : ℝ} (q : ℝ) (ha : 0 ≤ a) (hβ : |β| < 1) :
    γ (-β) * (γ β * (q - β * √(a + q ^ 2)) - -β * √(a + (γ β * (q - β * √(a + q ^ 2))) ^ 2))
      = q := by
  have h1 : γ β ^ 2 * (1 - β ^ 2) = 1 := by
    have : 1 - β ^ 2 ≠ 0 := (sub_pos.2 ((sq_lt_one_iff_abs_lt_one β).2 hβ)).ne'
    rw [γ_sq β hβ]
    field_simp
  rw [sqrt_add_sq_boost q ha hβ, γ_neg]
  linear_combination q * h1

/-- The one-dimensional core of boost invariance: on the line of transverse mass `√a`, the
measure `dq / (2 √(a + q²))` is invariant under the boost `q ↦ γ (q - β √(a + q²))`. -/
private theorem lintegral_comp_boost {a β : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) (h : ℝ → ℝ≥0∞) :
    ∫⁻ q, ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ * h (γ β * (q - β * √(a + q ^ 2))) =
      ∫⁻ q, ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ * h q := by
  set g : ℝ → ℝ := fun q => γ β * (q - β * √(a + q ^ 2)) with hg
  have hβ' : |-β| < 1 := by rwa [abs_neg]
  -- `g` is a bijection of `ℝ`, with inverse the boost with velocity `-β`
  have hinv : Function.LeftInverse (fun y => γ (-β) * (y - -β * √(a + y ^ 2))) g :=
    fun q => boost_neg_boost q ha hβ
  have hinv' : Function.RightInverse (fun y => γ (-β) * (y - -β * √(a + y ^ 2))) g := by
    intro y
    simpa only [neg_neg, hg] using boost_neg_boost y ha hβ'
  have hbij : Function.Bijective g := ⟨hinv.injective, hinv'.surjective⟩
  -- away from `q = 0`, where `√(a + q²)` may fail to be differentiable when `a = 0`
  have hderiv : ∀ q ∈ ({0}ᶜ : Set ℝ),
      HasDerivWithinAt g (γ β * (1 - β * (q / √(a + q ^ 2)))) {0}ᶜ q := by
    intro q hq
    have hpos : a + q ^ 2 ≠ 0 := by
      have : q ≠ 0 := hq
      positivity
    have hs : HasDerivAt (fun q => √(a + q ^ 2)) (q / √(a + q ^ 2)) q := by
      convert ((hasDerivAt_pow 2 q).const_add a).sqrt hpos using 1
      field_simp
      ring
    exact (((hasDerivAt_id' q).sub (hs.const_mul β)).const_mul (γ β)).hasDerivWithinAt
  have key := lintegral_image_eq_lintegral_abs_deriv_mul (measurableSet_singleton 0).compl
    hderiv hbij.injective.injOn (fun y => h y * ENNReal.ofReal (2 * √(a + y ^ 2))⁻¹)
  rw [Set.image_compl_eq hbij, Set.image_singleton, restrict_compl_singleton] at key
  have hL : ∫⁻ q, h (g q) * ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ =
      ∫⁻ q in {0}ᶜ, h (g q) * ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ := by
    rw [restrict_compl_singleton]
  simp_rw [mul_comm (ENNReal.ofReal _)]
  rw [key, hL]
  refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun q hq => ?_
  have hq : q ≠ 0 := hq
  -- the Jacobian `E' / E` cancels against the density `1 / (2 E')` at the image point
  have hE : 0 < √(a + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hE' : 0 < √(a + q ^ 2) - β * q := sub_pos.2 (mul_lt_sqrt_add_sq ha hβ hq)
  have hγ := γ_pos hβ
  have hd : γ β * (1 - β * (q / √(a + q ^ 2))) =
      γ β * (√(a + q ^ 2) - β * q) / √(a + q ^ 2) := by
    field_simp
  simp only [hg]
  rw [sqrt_add_sq_boost q ha hβ, mul_left_comm, ← ENNReal.ofReal_mul (abs_nonneg _), hd,
    abs_of_pos (by positivity)]
  congr 2
  field_simp
  rw [mul_comm q β, div_self hE'.ne']

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
  refine mul_nonneg (γ_pos hβ).le (sub_nonneg.2 ?_)
  calc β * p i ≤ |β| * |p i| := (le_abs_self _).trans (abs_mul _ _).le
    _ ≤ 1 * ‖p‖ :=
      mul_le_mul hβ.le (by simpa using PiLp.norm_apply_le p i) (abs_nonneg _) zero_le_one
    _ ≤ _ := by simpa using norm_le_onShellEnergy m p

private theorem lintegral_comp_massShellAction_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f (massShellAction (boost i β hβ) m p) ∂oneBodyMeasure m =
      ∫⁻ p, f p ∂oneBodyMeasure m := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := Nat.exists_eq_succ_of_ne_zero (Fin.pos i).ne'
  -- split `p` into its component `q` along the boost axis and the transverse rest `r`
  set e := (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) i)
  have he : MeasurePreserving e volume (volume.prod volume) :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp _).trans
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) i)
  have hsymm : ∀ q r, e.symm (q, r) = WithLp.toLp 2 (Fin.insertNth i q r) := fun _ _ => rfl
  have hE : ∀ q r, onShellEnergy m (e.symm (q, r)) = √((m ^ 2 + ∑ k, r k ^ 2) + q ^ 2) := by
    intro q r
    rw [hsymm, onShellEnergy, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succAbove _ i]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, Real.norm_eq_abs,
      sq_abs]
    congr 1
    ring
  have hT : ∀ q r, massShellAction (boost i β hβ) m (e.symm (q, r)) =
      e.symm (γ β * (q - β * √((m ^ 2 + ∑ k, r k ^ 2) + q ^ 2)), r) := by
    intro q r
    ext j
    rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩
    · rw [massShellAction_boost_apply_self, hE, hsymm, hsymm]
      simp
    · rw [massShellAction_boost_apply_of_ne (Fin.succAbove_ne i k), hsymm, hsymm]
      simp
  have hmeas : ∀ g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)),
      Measurable g → Measurable fun x : ℝ × (Fin n → ℝ) =>
        ENNReal.ofReal (2 * onShellEnergy m (e.symm x))⁻¹ * f (g (e.symm x)) := fun g hg =>
    ((measurable_density m).comp e.symm.measurable).mul (hf.comp (hg.comp e.symm.measurable))
  have hm₂ : Measurable fun x : ℝ × (Fin n → ℝ) =>
      ENNReal.ofReal (2 * onShellEnergy m (e.symm x))⁻¹ * f (e.symm x) :=
    hmeas id measurable_id
  rw [lintegral_oneBodyMeasure, lintegral_oneBodyMeasure,
    ← he.symm.lintegral_comp_emb e.symm.measurableEmbedding,
    ← he.symm.lintegral_comp_emb e.symm.measurableEmbedding,
    lintegral_prod_symm _ (hmeas _ (continuous_massShellAction _ m).measurable).aemeasurable,
    lintegral_prod_symm _ hm₂.aemeasurable]
  -- at fixed transverse momentum this is the one-dimensional statement
  refine lintegral_congr fun r => ?_
  simp only [hT, hE]
  exact lintegral_comp_boost (by positivity) hβ fun y => f (e.symm (y, r))

/-- **Boost invariance.** A boost along a coordinate axis preserves the one-body measure
`d^d p / (2E)`, for every mass `m`, the massless case included. -/
theorem measurePreserving_massShellAction_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ) :
    MeasurePreserving (massShellAction (boost i β hβ) m) (oneBodyMeasure m)
      (oneBodyMeasure m) :=
  ⟨(continuous_massShellAction _ m).measurable, Measure.ext_of_lintegral _ fun f hf => by
    rw [lintegral_map hf (continuous_massShellAction _ m).measurable]
    exact lintegral_comp_massShellAction_boost i hβ m hf⟩

/-! ### Rotations -/

theorem massShell_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    massShell m (massShellAction Λ m p) = (Λ : LorentzGroup d) • massShell m p :=
  massShell_massShellAction <| by
    rw [timeComponent_rotations_smul, timeComponent_massShell]
    exact onShellEnergy_nonneg m p

/-- A rotation does not change the energy. -/
theorem onShellEnergy_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) :
    onShellEnergy m (massShellAction Λ m p) = onShellEnergy m p := by
  have h := congrArg Lorentz.Vector.timeComponent (massShell_massShellAction_rotation Λ m p)
  rwa [timeComponent_massShell, timeComponent_rotations_smul, timeComponent_massShell] at h

theorem norm_massShellAction_rotation (Λ : Rotations d) (m : ℝ)
    (p : EuclideanSpace ℝ (Fin d)) : ‖massShellAction Λ m p‖ = ‖p‖ := by
  have h := congrArg (· ^ 2) (onShellEnergy_massShellAction_rotation Λ m p)
  simp only [sq_onShellEnergy, add_right_inj] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- **Rotation invariance.** A spatial rotation preserves the one-body measure. -/
theorem measurePreserving_massShellAction_rotation (Λ : Rotations d) (m : ℝ) :
    MeasurePreserving (massShellAction (Λ : LorentzGroup d) m) (oneBodyMeasure m)
      (oneBodyMeasure m) := by
  -- on spatial momenta the rotation is a linear isometry, so it preserves Lebesgue measure
  have hrot : ∀ p j, massShellAction (Λ : LorentzGroup d) m p j =
      ∑ k, (Λ : LorentzGroup d).1 (Sum.inr j) (Sum.inr k) * p k := fun p j => by
    rw [massShellAction_def, spatialPart_rotations_smul_apply, spatialPart_massShell]
  let L : EuclideanSpace ℝ (Fin d) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d) :=
    { toFun := massShellAction (Λ : LorentzGroup d) m
      map_add' := fun p q => by
        ext j
        simp [hrot, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c p => by
        ext j
        simp [hrot, Finset.mul_sum, mul_left_comm]
      norm_map' := norm_massShellAction_rotation Λ m }
  have hL : MeasurePreserving (massShellAction (Λ : LorentzGroup d) m) volume volume :=
    (L.toLinearIsometryEquiv rfl).measurePreserving
  refine ⟨hL.measurable, Measure.ext_of_lintegral _ fun f hf => ?_⟩
  rw [lintegral_map hf hL.measurable, lintegral_oneBodyMeasure, lintegral_oneBodyMeasure]
  -- and it leaves the energy, hence the density, unchanged
  calc _ = ∫⁻ p, ENNReal.ofReal (2 * onShellEnergy m (massShellAction Λ m p))⁻¹ *
        f (massShellAction (Λ : LorentzGroup d) m p) := by
        simp only [onShellEnergy_massShellAction_rotation]
    _ = _ := hL.lintegral_comp (f := fun q => ENNReal.ofReal (2 * onShellEnergy m q)⁻¹ * f q)
        ((measurable_density m).mul hf)

end PhaseSpace
end Kinematics
end Scattering
end QFT
end EpsilonEridani
