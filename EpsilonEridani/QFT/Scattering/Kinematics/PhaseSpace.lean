/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.MeasureTheory.Measure.WithDensity
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MassShell

/-!
# The Lorentz-invariant one-body phase-space measure

A particle of mass `m` in `d` spatial dimensions has four-momenta on the mass shell
`p⁰ = E(p) = √(m² + |p|²)`, parametrised by the spatial momentum `p ∈ ℝᵈ` (see
`EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MassShell` for the shell and the map
`massShellMap` a Lorentz transformation induces on it). The invariant one-body measure is

  `d^d p / (2 E(p))`,

Lebesgue measure on the spatial momenta with density `1 / (2E)`. Its invariance under Lorentz
transformations is the reason phase space is written this way: a Lorentz transformation `Λ` moves
the point `(E(p), p)` to another point of the shell. The induced map on spatial momenta does not
preserve `d^d p`, but its Jacobian `E(Λp) / E(p)` is cancelled exactly by the density.

* `oneBodyMeasure m` is `d^d p / (2E)`, a σ-finite measure on `EuclideanSpace ℝ (Fin d)`. The
  massless case `m = 0` is included: `1 / (2E)` blows up as `p → 0`, but the density is
  evaluated as `0` at `p = 0` itself (the real inverse of `0` is `0`), and for `d ≥ 1` the
  point `{0}` is Lebesgue-null anyway.
* `measurePreserving_massShellMap_boost`: a boost along any coordinate axis preserves
  `oneBodyMeasure m`. Along the boost axis, at fixed transverse momentum `p_⊥`, the energy is
  `√(m² + |p_⊥|² + q²)` and the boost acts as `q ↦ γ (q - β E)`, a bijection of the line with
  derivative `E' / E`, where `E' = γ (E - β q)` is the boosted energy.
* `measurePreserving_linearIsometryEquiv`: every linear isometry of the spatial momenta, a
  rotation or reflection, preserves it, since it preserves `d^d p` and `|p|`, hence `E`. A Lorentz
  transformation with time-time entry `1` acts on `p` as such an isometry,
  `LorentzGroup.spatialLinearIsometryEquiv`, so it preserves the measure as well
  (`measurePreserving_massShellMap_of_timeComponent_eq_one`).

This file proves invariance only for these two generating cases. Both keep the energy
non-negative, so for a finite product of them `massShellMap_mul` writes the map as the
composite of their maps, and `MeasurePreserving.comp` then gives invariance of the product;
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

/-- Defining expression for `oneBodyMeasure`. -/
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

/-- The `oneBodyMeasure m` of a set is the integral of the weight `1 / (2E)` over it. -/
theorem oneBodyMeasure_apply (m : ℝ) (s : Set (EuclideanSpace ℝ (Fin d))) :
    oneBodyMeasure m s = ∫⁻ p in s, ENNReal.ofReal (2 * onShellEnergy m p)⁻¹ := by
  rw [oneBodyMeasure_def, withDensity_apply' _ s]

/-- Integrating against `oneBodyMeasure m` is integrating against Lebesgue measure with the
weight `1 / (2E)`. -/
theorem lintegral_oneBodyMeasure (m : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    ∫⁻ p, f p ∂oneBodyMeasure m = ∫⁻ p, ENNReal.ofReal (2 * onShellEnergy m p)⁻¹ * f p :=
  lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_density m)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f

/-! ### Boosts along a coordinate axis -/

/-- On the line `d = 1`, the energy at mass `√a` of the momentum `q` is `√(a + q²)`. -/
private theorem onShellEnergy_sqrt_single {a : ℝ} (ha : 0 ≤ a) (q : ℝ) :
    onShellEnergy √a (WithLp.toLp 2 ![q] : EuclideanSpace ℝ (Fin 1)) = √(a + q ^ 2) := by
  rw [onShellEnergy_def, Real.sq_sqrt ha, EuclideanSpace.norm_sq_eq]
  simp

/-- On the line `d = 1` at mass `√a`, the boost acts as `q ↦ γ (q - β √(a + q²))`. -/
private theorem massShellMap_boost_single {a β : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) (q : ℝ) :
    massShellMap (boost 0 β hβ) √a (WithLp.toLp 2 ![q] : EuclideanSpace ℝ (Fin 1)) =
      WithLp.toLp 2 ![γ β * (q - β * √(a + q ^ 2))] := by
  ext j
  obtain rfl := Subsingleton.elim j 0
  rw [massShellMap_boost_apply_self, onShellEnergy_sqrt_single ha]
  simp

/-- In `1 + 1` dimensions with transverse mass `√a`, the boosted momentum
`q' = γ (q - β E)` has energy `E' = γ (E - β q)`: the case `d = 1`, `m = √a` of
`onShellEnergy_massShellMap_boost`. -/
private theorem sqrt_add_sq_boost {a β : ℝ} (q : ℝ) (ha : 0 ≤ a) (hβ : |β| < 1) :
    √(a + (γ β * (q - β * √(a + q ^ 2))) ^ 2) = γ β * (√(a + q ^ 2) - β * q) := by
  have h := onShellEnergy_massShellMap_boost 0 hβ √a
    (WithLp.toLp 2 ![q] : EuclideanSpace ℝ (Fin 1))
  rw [massShellMap_boost_single ha, onShellEnergy_sqrt_single ha,
    onShellEnergy_sqrt_single ha] at h
  simpa using h

/-- The boost with velocity `-β` undoes the boost with velocity `β` on the line of transverse
mass `√a`: the case `d = 1`, `m = √a` of `massShellMap_boost_neg_boost`. -/
private theorem boost_neg_boost {a β : ℝ} (q : ℝ) (ha : 0 ≤ a) (hβ : |β| < 1) :
    γ (-β) * (γ β * (q - β * √(a + q ^ 2)) - -β * √(a + (γ β * (q - β * √(a + q ^ 2))) ^ 2))
      = q := by
  have h := congrArg (· 0) (massShellMap_boost_neg_boost 0 hβ √a
    (WithLp.toLp 2 ![q] : EuclideanSpace ℝ (Fin 1)))
  simp only [massShellMap_boost_single ha] at h
  simpa using h

/-- The one-dimensional core of boost invariance: on the line of transverse mass `√a`, the
measure `dq / (2 √(a + q²))` is invariant under the boost `q ↦ γ (q - β √(a + q²))`. -/
private theorem map_withDensity_boost {a β : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) :
    (volume.withDensity fun q => ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹).map
        (fun q => γ β * (q - β * √(a + q ^ 2))) =
      volume.withDensity fun q => ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ := by
  set g : ℝ → ℝ := fun q => γ β * (q - β * √(a + q ^ 2)) with hg
  set w : ℝ → ℝ≥0∞ := fun q => ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ with hw
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
  have key := TauCeti.MeasureTheory.map_withDensity_abs_deriv_mul (f := w)
    (measurableSet_singleton 0).compl (by fun_prop) hderiv hbij.injective.injOn
  rw [Set.image_compl_eq hbij, Set.image_singleton, restrict_compl_singleton,
    restrict_compl_singleton] at key
  refine (congrArg (Measure.map g) ?_).trans key
  -- off `q = 0`, the Jacobian `E' / E` cancels against the density `1 / (2 E')` at the image
  refine withDensity_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : ℝ))] with q hq
  have hq : q ≠ 0 := Set.mem_compl_singleton_iff.mp hq
  have hE : 0 < √(a + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hE' : 0 < √(a + q ^ 2) - β * q := by
    have h := abs_mul_apply_lt_onShellEnergy hβ √a
      (p := (WithLp.toLp 2 ![q] : EuclideanSpace ℝ (Fin 1)))
      (by rw [onShellEnergy_sqrt_single ha]; exact hE) 0
    rw [onShellEnergy_sqrt_single ha] at h
    exact sub_pos.2 ((le_abs_self _).trans_lt (by simpa using h))
  have hγ := γ_pos hβ
  have hd : γ β * (1 - β * (q / √(a + q ^ 2))) =
      γ β * (√(a + q ^ 2) - β * q) / √(a + q ^ 2) := by
    field_simp [hE.ne']
  -- with `E = √(a + q²)` and `E' = γ (E - β q)`: `(E' / E) / (2 E') = 1 / (2 E)`
  have hJ : γ β * (√(a + q ^ 2) - β * q) / √(a + q ^ 2) *
      (2 * (γ β * (√(a + q ^ 2) - β * q)))⁻¹ = (2 * √(a + q ^ 2))⁻¹ := by
    have key : ∀ {E y g : ℝ}, E ≠ 0 → y ≠ 0 → g ≠ 0 → g * y / E * (2 * (g * y))⁻¹ = (2 * E)⁻¹ :=
      fun hE hy hg => by field_simp
    exact key hE.ne' hE'.ne' hγ.ne'
  simp only [hg, hw]
  rw [sqrt_add_sq_boost q ha hβ, ← ENNReal.ofReal_mul (abs_nonneg _), hd,
    abs_of_pos (by positivity), hJ]

/-- The one-dimensional boost invariance, integrated against a measurable function. -/
private theorem lintegral_comp_boost {a β : ℝ} (ha : 0 ≤ a) (hβ : |β| < 1) {h : ℝ → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ q, ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ * h (γ β * (q - β * √(a + q ^ 2))) =
      ∫⁻ q, ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ * h q := by
  have hw : Measurable fun q : ℝ => ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ := by fun_prop
  have hfin : ∀ᵐ q : ℝ, ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹ < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hmp : MeasurePreserving (fun q => γ β * (q - β * √(a + q ^ 2)))
      (volume.withDensity fun q => ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹)
      (volume.withDensity fun q => ENNReal.ofReal (2 * √(a + q ^ 2))⁻¹) :=
    ⟨by fun_prop, map_withDensity_boost ha hβ⟩
  exact ((lintegral_withDensity_eq_lintegral_mul_non_measurable _ hw hfin _).symm.trans
    (hmp.lintegral_comp hh)).trans
      (lintegral_withDensity_eq_lintegral_mul_non_measurable _ hw hfin h)

private theorem lintegral_comp_massShellMap_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ)
    {f : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ p, f (massShellMap (boost i β hβ) m p) ∂oneBodyMeasure m =
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
  have hT : ∀ q r, massShellMap (boost i β hβ) m (e.symm (q, r)) =
      e.symm (γ β * (q - β * √((m ^ 2 + ∑ k, r k ^ 2) + q ^ 2)), r) := by
    intro q r
    ext j
    rcases i.eq_self_or_eq_succAbove j with rfl | ⟨k, rfl⟩
    · rw [massShellMap_boost_apply_self, hE, hsymm, hsymm]
      simp
    · rw [massShellMap_boost_apply_of_ne (Fin.succAbove_ne i k), hsymm, hsymm]
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
    lintegral_prod_symm _ (hmeas _ (continuous_massShellMap _ m).measurable).aemeasurable,
    lintegral_prod_symm _ hm₂.aemeasurable]
  -- at fixed transverse momentum this is the one-dimensional statement
  refine lintegral_congr fun r => ?_
  simp only [hT, hE]
  exact lintegral_comp_boost (by positivity) hβ
    (hf.comp (e.symm.measurable.comp measurable_prodMk_right))

/-- **Boost invariance.** A boost along a coordinate axis preserves the one-body measure
`d^d p / (2E)`, for every mass `m`, the massless case included. -/
theorem measurePreserving_massShellMap_boost (i : Fin d) {β : ℝ} (hβ : |β| < 1) (m : ℝ) :
    MeasurePreserving (massShellMap (boost i β hβ) m) (oneBodyMeasure m)
      (oneBodyMeasure m) :=
  ⟨(continuous_massShellMap _ m).measurable, Measure.ext_of_lintegral _ fun f hf => by
    rw [lintegral_map hf (continuous_massShellMap _ m).measurable]
    exact lintegral_comp_massShellMap_boost i hβ m hf⟩

/-! ### Rotations and spatial reflections -/

/-- **Rotation invariance.** A linear isometry of the spatial momenta — a rotation or
reflection — preserves the one-body measure, since it preserves Lebesgue measure and `|p|`, hence
the energy. -/
theorem measurePreserving_linearIsometryEquiv
    (L : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) (m : ℝ) :
    MeasurePreserving L (oneBodyMeasure m) (oneBodyMeasure m) := by
  refine ⟨L.continuous.measurable, ?_⟩
  rw [oneBodyMeasure_def, ← L.coe_toMeasurableEquiv, MeasurableEquiv.map_withDensity,
    L.coe_toMeasurableEquiv, L.measurePreserving.map_eq]
  congr 1
  funext q
  rw [L.coe_symm_toMeasurableEquiv, onShellEnergy_def, onShellEnergy_def, L.symm.norm_map]

/-- A Lorentz transformation with time-time entry `1` — a spatial rotation or reflection —
preserves the one-body measure. -/
theorem measurePreserving_massShellMap_of_timeComponent_eq_one {Λ : LorentzGroup d}
    (hΛ : Λ.1 (Sum.inl 0) (Sum.inl 0) = 1) (m : ℝ) :
    MeasurePreserving (massShellMap Λ m) (oneBodyMeasure m) (oneBodyMeasure m) := by
  rw [massShellMap_of_timeComponent_eq_one hΛ m]
  exact measurePreserving_linearIsometryEquiv _ m

end PhaseSpace
end Kinematics
end Scattering
end QFT
end EpsilonEridani
