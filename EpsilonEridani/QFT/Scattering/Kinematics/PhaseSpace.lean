/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MassShell

/-!
# The Lorentz-invariant one-body phase-space measure

A particle of mass `m` in `d` spatial dimensions has four-momenta on the mass shell
`p⁰ = E(p) = √(m² + |p|²)`, parametrised by the spatial momentum `p ∈ ℝᵈ` (see
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MassShell` for the shell and the Lorentz
action `massShellAction` on it). The invariant one-body measure is

  `d^d p / (2 E(p))`,

Lebesgue measure on the spatial momenta with density `1 / (2E)`. Its invariance under Lorentz
transformations is the reason phase space is written this way: a Lorentz transformation `Λ` moves
the point `(E(p), p)` to another point of the shell. The induced map on spatial momenta does not
preserve `d^d p`, but its Jacobian `E(Λp) / E(p)` is cancelled exactly by the density.

* `oneBodyMeasure m` is `d^d p / (2E)`, a σ-finite measure on `EuclideanSpace ℝ (Fin d)`. The
  massless case `m = 0` is included. There the density is singular at `p = 0`, a null set.
* `measurePreserving_massShellAction_boost`: a boost along any coordinate axis preserves
  `oneBodyMeasure m`. Along the boost axis, at fixed transverse momentum `p_⊥`, the energy is
  `√(m² + |p_⊥|² + q²)` and the boost acts as `q ↦ γ (q - β E)`, a bijection of the line with
  derivative `E' / E`, where `E' = γ (E - β q)` is the boosted energy.
* `measurePreserving_massShellAction_rotation`: a spatial rotation preserves it, since it acts on
  `p` as the linear isometry `massShellActionₗᵢ` and leaves `E` unchanged.

This file proves invariance only for these two generating cases. Both keep the energy
non-negative, so for a finite product of them `massShellAction_mul` writes the action as the
composite of their actions, and `MeasurePreserving.comp` then gives invariance of the product;
that consequence is not stated here.

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
open scoped ENNReal

variable {d : ℕ}

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

private theorem mul_lt_sqrt_add_sq {a β q : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) (hq : q ≠ 0) :
    β * q < √(a + q ^ 2) := by
  refine ((le_abs_self _).trans_lt ?_).trans_le (Real.abs_le_sqrt (by linarith))
  rw [abs_mul]
  exact mul_lt_of_lt_one_left (abs_pos.2 hq) hβ

private theorem mul_le_sqrt_add_sq {a β q : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) :
    β * q ≤ √(a + q ^ 2) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · exact (mul_lt_sqrt_add_sq ha hβ hq).le

/-- In `1 + 1` dimensions with transverse mass `√a`, the boosted momentum
`q' = γ (q - β E)` has energy `E' = γ (E - β q)`. -/
private theorem sqrt_add_sq_boost {a β : ℝ} (q : ℝ) (ha : 0 ≤ a) (hβ : |β| < 1) :
    √(a + (γ β * (q - β * √(a + q ^ 2))) ^ 2) = γ β * (√(a + q ^ 2) - β * q) := by
  have h1 := γ_sq_mul_one_sub_sq hβ
  have hE : √(a + q ^ 2) ^ 2 = a + q ^ 2 := Real.sq_sqrt (by positivity)
  rw [← Real.sqrt_sq (mul_nonneg (γ_pos hβ).le (sub_nonneg.2 (mul_le_sqrt_add_sq ha hβ)))]
  congr 1
  linear_combination (-a) * h1 + (-(γ β ^ 2 * (1 - β ^ 2))) * hE

/-- The boost with velocity `-β` undoes the boost with velocity `β` on the line of transverse
mass `√a`. -/
private theorem boost_neg_boost {a β : ℝ} (q : ℝ) (ha : 0 ≤ a) (hβ : |β| < 1) :
    γ (-β) * (γ β * (q - β * √(a + q ^ 2)) - -β * √(a + (γ β * (q - β * √(a + q ^ 2))) ^ 2))
      = q := by
  have h1 := γ_sq_mul_one_sub_sq hβ
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
      have : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
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
  have hq : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
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
  have hsymm : ∀ q r, e.symm (q, r) = WithLp.toLp 2 (Fin.insertNth i q r) := fun q r => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
  have hE : ∀ q r, onShellEnergy m (e.symm (q, r)) = √((m ^ 2 + ∑ k, r k ^ 2) + q ^ 2) := by
    intro q r
    rw [hsymm, onShellEnergy_def, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succAbove _ i]
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

/-- **Rotation invariance.** A spatial rotation preserves the one-body measure. -/
theorem measurePreserving_massShellAction_rotation (Λ : Rotations d) (m : ℝ) :
    MeasurePreserving (massShellAction (Λ : LorentzGroup d) m) (oneBodyMeasure m)
      (oneBodyMeasure m) := by
  -- on spatial momenta the rotation is a linear isometry, so it preserves Lebesgue measure
  have hL : MeasurePreserving (massShellAction (Λ : LorentzGroup d) m) volume volume := by
    rw [← coe_massShellActionₗᵢ Λ m]
    exact ((massShellActionₗᵢ Λ).toLinearIsometryEquiv rfl).measurePreserving
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
