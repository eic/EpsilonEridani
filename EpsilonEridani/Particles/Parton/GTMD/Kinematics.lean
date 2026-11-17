/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.GPD.Kinematics
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.LightFront

/-!
# Kinematics of generalized transverse-momentum-dependent distributions

A generalized transverse-momentum-dependent parton distribution (GTMD) describes a parton of
average momentum `k` in the off-forward hadron transition `h(p) → h(p')`. In the light-front frame
it is a function of four variables, in this order:

* the momentum fraction `x = k⁺ / P⁺`,
* the skewness `ξ = -Δ⁺ / (2 P⁺) = (p⁺ - p'⁺) / (p⁺ + p'⁺)`,
* the transverse parton momentum `kT`,
* the transverse momentum transfer `ΔT`,

where `P = (p + p') / 2` and `Δ = p' - p`, and the transverse momenta are taken relative to `P`,
that is, in the frame `P_T = 0`. The two transverse variables are genuine vectors of the plane
`EuclideanSpace ℝ (Fin 2)`. This module bundles the four variables as `GTMD.Kinematics` and
derives the invariant momentum transfer `t = Δ²` from them.

The invariant `t` is not an independent variable: for a hadron of mass `M`,

  `t = -(4 ξ² M² + ΔT²) / (1 - ξ²)`,

which is the definition of `Kinematics.tMom`. That this is `Δ²` is a theorem about four-momenta,
`Kinematics.tMom_ofMomenta_eq_minkowskiProduct_sub_self`: for on-shell hadron momenta with positive
plus components, the kinematics `Kinematics.ofMomenta p p' k` read off from the momenta has
`tMom M = ⟪p' - p, p' - p⟫ₘ`. Such momenta form off-forward kinematics in the sense of
`EpsilonEridani.Particles.Parton.GPD.Kinematics` (`lightFrontOffForwardKinematics`), with the
light-like direction `ofLightFront 0 1 0` that defines the light-front plus component. For any
`OffForwardKinematics` whose light-like direction is a non-zero multiple of that one, the skewness,
the transverse momentum transfer and the momentum transfer are those of the GTMD kinematics
(`Kinematics.skewness_ofMomenta_eq_skewness`,
`Kinematics.deltaT_ofMomenta_eq_transversePart_deltaOrthN` and `Kinematics.tMom_ofMomenta_eq_tMom`);
the GPD conventions for `ξ` and `t` are adopted unchanged.

The variables are invariant under the light-front transverse boosts, provided `P⁺ ≠ 0`
(`Kinematics.ofMomenta_transverseBoost`). Exchanging the two hadrons reverses the skewness and the
transverse momentum transfer (`Kinematics.ofMomenta_swap`), the operation `Kinematics.swap` against
which hermiticity of an off-forward correlator is stated; it preserves the physical domain
(`Kinematics.isPhysical_swap`).

Consequences of the formula for `t`:

* `Kinematics.tMom_le_tZero`: `t ≤ t₀(ξ)` for `|ξ| < 1`, with equality exactly when `ΔT = 0`
  (`Kinematics.tMom_eq_tZero_iff`), where `t₀` is `GPD.tZero`.
* `Kinematics.tMom_eq_neg_norm_deltaT_sq_of_mem_zeroSkewness`: at zero skewness `t = -ΔT²`, which
  is what makes `ΔT` Fourier conjugate to a transverse position there.
* `Kinematics.tMom_eq_zero_iff`: for a massive hadron and `|ξ| < 1`, `t = 0` exactly at `ξ = 0`
  and `ΔT = 0`.
* `Kinematics.exists_ofMomenta_eq_iff`: a value of `Kinematics` is realised by on-shell hadron
  momenta with positive plus components exactly when `|ξ| < 1`.

The two distinguished subsets `Kinematics.zeroSkewness` (`ξ = 0`) and
`Kinematics.zeroTransverseTransfer` (`ΔT = 0`) are named, since the reductions of a GTMD are
restrictions to them. The physical domain, `|x| ≤ 1` and `|ξ| < 1`, is the predicate
`Kinematics.IsPhysical`; `Kinematics.isPhysical_iff` shows it is equivalent to `|x| ≤ 1` together
with membership of `(ξ, t)` in `GPD.physicalRegion M`, so the bound `t ≤ t₀(ξ)` is a consequence,
not an assumption.

## References

* S. Meissner, A. Metz and M. Schlegel, *Generalized parton correlation functions for a spin-1/2
  hadron*, JHEP **08** (2009) 056 (arXiv:0906.5323), §2.
* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41
  (arXiv:hep-ph/0307382), §3.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

open Lorentz Lorentz.Vector EpsilonEridani.LightFront
open GPD (tZero physicalRegion OffForwardKinematics)

/-- The transverse plane. -/
local notation "E²" => EuclideanSpace ℝ (Fin 2)

/-- The light-front kinematic variables of a generalized transverse-momentum-dependent
distribution, in the order `(x, ξ, kT, ΔT)`: the momentum fraction, the skewness, the transverse
parton momentum and the transverse momentum transfer. The invariant momentum transfer is
derived from them, see `Kinematics.tMom`. -/
@[ext]
structure Kinematics where
  /-- The momentum fraction `x = k⁺ / P⁺` of the parton. -/
  x : ℝ
  /-- The skewness `ξ = -Δ⁺ / (2 P⁺)`. -/
  skewness : ℝ
  /-- The transverse parton momentum, relative to the average hadron momentum. -/
  kT : E²
  /-- The transverse momentum transfer, relative to the average hadron momentum. -/
  deltaT : E²

namespace Kinematics

variable (K : Kinematics) (M : ℝ)

/-! ### The invariant momentum transfer -/

/-- The invariant momentum transfer `t = -(4 ξ² M² + ΔT²) / (1 - ξ²)` of the kinematics `K` for a
hadron of mass `M`. It equals `Δ²` for every realisation by on-shell four-momenta with positive
plus components (`tMom_ofMomenta_eq_minkowskiProduct_sub_self`). -/
def tMom : ℝ :=
  -(4 * K.skewness ^ 2 * M ^ 2 + ‖K.deltaT‖ ^ 2) / (1 - K.skewness ^ 2)

lemma tMom_def :
    K.tMom M = -(4 * K.skewness ^ 2 * M ^ 2 + ‖K.deltaT‖ ^ 2) / (1 - K.skewness ^ 2) := (rfl)

/-- The momentum transfer in terms of the minimal momentum transfer,
`t = t₀(ξ) - ΔT² / (1 - ξ²)`; for `|ξ| < 1` it is `t₀(ξ)` lowered by `ΔT² / (1 - ξ²)`. -/
lemma tMom_eq_tZero_sub :
    K.tMom M = tZero M K.skewness - ‖K.deltaT‖ ^ 2 / (1 - K.skewness ^ 2) := by
  rw [tMom_def, GPD.tZero_def]
  ring

/-- Away from `|ξ| = 1`, the value of the momentum transfer is characterised by the covariant
relation `(1 - ξ²) t + 4 ξ² M² = -ΔT²`. -/
lemma tMom_eq_iff (hξ : |K.skewness| ≠ 1) (t : ℝ) :
    K.tMom M = t ↔
      ‖K.deltaT‖ ^ 2 = -((1 - K.skewness ^ 2) * t + 4 * K.skewness ^ 2 * M ^ 2) := by
  have h : 1 - K.skewness ^ 2 ≠ 0 := fun h0 => hξ (by
    rcases sq_eq_one_iff.mp (by linarith : K.skewness ^ 2 = 1) with h1 | h1 <;> simp [h1])
  rw [tMom_def, div_eq_iff h]
  constructor <;> intro h <;> linarith

/-- The covariant form of the momentum transfer: `ΔT² = -((1 - ξ²) t + 4 ξ² M²)`. -/
lemma norm_deltaT_sq_eq (hξ : |K.skewness| ≠ 1) :
    ‖K.deltaT‖ ^ 2 = -((1 - K.skewness ^ 2) * K.tMom M + 4 * K.skewness ^ 2 * M ^ 2) :=
  (K.tMom_eq_iff M hξ _).mp rfl

/-- In the physical range `|ξ| < 1` the momentum transfer is bounded by the minimal momentum
transfer, `t ≤ t₀(ξ)`. -/
theorem tMom_le_tZero (hξ : |K.skewness| < 1) : K.tMom M ≤ tZero M K.skewness := by
  have h : 0 < 1 - K.skewness ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr hξ)
  rw [tMom_eq_tZero_sub, sub_le_self_iff]
  positivity

/-- In the physical range `|ξ| < 1`, the bound `t ≤ t₀(ξ)` is attained exactly when `ΔT = 0`. -/
theorem tMom_eq_tZero_iff (hξ : |K.skewness| < 1) :
    K.tMom M = tZero M K.skewness ↔ K.deltaT = 0 := by
  have h : 0 < 1 - K.skewness ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr hξ)
  rw [tMom_eq_tZero_sub, sub_eq_self, div_eq_zero_iff, or_iff_left h.ne']
  simp

/-- In the physical range `|ξ| < 1` the momentum transfer is non-positive, `t ≤ 0`. -/
lemma tMom_nonpos (hξ : |K.skewness| < 1) : K.tMom M ≤ 0 :=
  (K.tMom_le_tZero M hξ).trans (GPD.tZero_nonpos M hξ)

/-- In the physical range `|ξ| < 1` the pair `(ξ, t)` lies in the physical region of the
off-forward variables of a generalized parton distribution. -/
lemma skewness_tMom_mem_physicalRegion (hξ : |K.skewness| < 1) :
    (K.skewness, K.tMom M) ∈ physicalRegion M :=
  (GPD.mem_physicalRegion_iff M _).mpr ⟨hξ, K.tMom_le_tZero M hξ⟩

/-! ### The subsets of zero skewness and of zero transverse momentum transfer -/

/-- The kinematics at zero skewness, `ξ = 0`. -/
def zeroSkewness : Set Kinematics := {K | K.skewness = 0}

@[simp]
lemma mem_zeroSkewness_iff : K ∈ zeroSkewness ↔ K.skewness = 0 := Iff.rfl

/-- The kinematics at zero transverse momentum transfer, `ΔT = 0`. -/
def zeroTransverseTransfer : Set Kinematics := {K | K.deltaT = 0}

@[simp]
lemma mem_zeroTransverseTransfer_iff : K ∈ zeroTransverseTransfer ↔ K.deltaT = 0 := Iff.rfl

/-- At zero skewness the momentum transfer is purely transverse, `t = -ΔT²`. -/
lemma tMom_eq_neg_norm_deltaT_sq_of_mem_zeroSkewness {K : Kinematics} (hK : K ∈ zeroSkewness) :
    K.tMom M = -‖K.deltaT‖ ^ 2 := by
  rw [mem_zeroSkewness_iff] at hK
  simp [tMom_def, hK]

/-- At zero transverse momentum transfer the momentum transfer is the minimal one,
`t = t₀(ξ)`. -/
lemma tMom_eq_tZero_of_mem_zeroTransverseTransfer {K : Kinematics}
    (hK : K ∈ zeroTransverseTransfer) :
    K.tMom M = tZero M K.skewness := by
  rw [mem_zeroTransverseTransfer_iff] at hK
  simp [tMom_eq_tZero_sub, hK]

/-- For a hadron of non-zero mass and `|ξ| < 1`, the momentum transfer vanishes exactly at zero
skewness and zero transverse momentum transfer. -/
theorem tMom_eq_zero_iff (hM : M ≠ 0) (hξ : |K.skewness| < 1) :
    K.tMom M = 0 ↔ K ∈ zeroSkewness ∩ zeroTransverseTransfer := by
  have h : 0 < 1 - K.skewness ^ 2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one _).mpr hξ)
  have h₁ : 0 ≤ 4 * K.skewness ^ 2 * M ^ 2 := by positivity
  have h₂ : 0 ≤ ‖K.deltaT‖ ^ 2 := by positivity
  rw [tMom_def, div_eq_zero_iff, or_iff_left h.ne', neg_eq_zero,
    add_eq_zero_iff_of_nonneg h₁ h₂]
  simp [hM]

/-! ### The physical domain -/

/-- The physical domain of the GTMD variables: `|x| ≤ 1` and `|ξ| < 1`. The bound `t ≤ t₀(ξ)` on
the momentum transfer is a consequence, see `isPhysical_iff`. -/
structure IsPhysical : Prop where
  /-- The momentum fraction lies in `[-1, 1]`. -/
  abs_x_le_one : |K.x| ≤ 1
  /-- The skewness lies in `(-1, 1)`. -/
  abs_skewness_lt_one : |K.skewness| < 1

/-- The physical domain is `|x| ≤ 1` together with `(ξ, t)` in the physical region
`|ξ| < 1`, `t ≤ t₀(ξ)` of the off-forward variables, for a hadron of any mass `M`. -/
theorem isPhysical_iff :
    K.IsPhysical ↔ |K.x| ≤ 1 ∧ (K.skewness, K.tMom M) ∈ physicalRegion M :=
  ⟨fun h => ⟨h.abs_x_le_one, K.skewness_tMom_mem_physicalRegion M h.abs_skewness_lt_one⟩,
    fun h => ⟨h.1, ((GPD.mem_physicalRegion_iff M _).mp h.2).1⟩⟩

/-! ### Exchange of the two hadrons -/

/-- The kinematics with the two hadrons exchanged: the skewness and the transverse momentum
transfer change sign, `(x, ξ, kT, ΔT) ↦ (x, -ξ, kT, -ΔT)` (`ofMomenta_swap`). -/
def swap : Kinematics := ⟨K.x, -K.skewness, K.kT, -K.deltaT⟩

@[simp]
lemma x_swap : K.swap.x = K.x := (rfl)

@[simp]
lemma skewness_swap : K.swap.skewness = -K.skewness := (rfl)

@[simp]
lemma kT_swap : K.swap.kT = K.kT := (rfl)

@[simp]
lemma deltaT_swap : K.swap.deltaT = -K.deltaT := (rfl)

@[simp]
lemma swap_swap : K.swap.swap = K := by
  ext <;> simp

@[simp]
lemma tMom_swap : K.swap.tMom M = K.tMom M := by
  simp [tMom_def]

/-- Exchanging the two hadrons preserves the physical domain. -/
@[simp]
lemma isPhysical_swap : K.swap.IsPhysical ↔ K.IsPhysical :=
  ⟨fun h => ⟨by simpa using h.abs_x_le_one, by simpa using h.abs_skewness_lt_one⟩,
    fun h => ⟨by simpa using h.abs_x_le_one, by simpa using h.abs_skewness_lt_one⟩⟩

/-! ### Realisation by four-momenta -/

/-- The GTMD kinematics of a parton of average momentum `k` in the transition from a hadron of
momentum `p` to one of momentum `p'`: with `P = (p + p') / 2`, the momentum fraction `k⁺ / P⁺`,
the skewness `(p⁺ - p'⁺) / (p⁺ + p'⁺)`, and the transverse momenta of `k` and of `p' - p`
relative to `P`. -/
def ofMomenta (p p' k : Lorentz.Vector 3) : Kinematics where
  x := plusComponent k / plusComponent ((2⁻¹ : ℝ) • (p + p'))
  skewness := (plusComponent p - plusComponent p') / (plusComponent p + plusComponent p')
  kT := relativeTransverse k ((2⁻¹ : ℝ) • (p + p'))
  deltaT := relativeTransverse (p' - p) ((2⁻¹ : ℝ) • (p + p'))

variable (p p' k : Lorentz.Vector 3)

@[simp]
lemma x_ofMomenta :
    (ofMomenta p p' k).x = plusComponent k / plusComponent ((2⁻¹ : ℝ) • (p + p')) := (rfl)

@[simp]
lemma skewness_ofMomenta : (ofMomenta p p' k).skewness =
    (plusComponent p - plusComponent p') / (plusComponent p + plusComponent p') := (rfl)

@[simp]
lemma kT_ofMomenta : (ofMomenta p p' k).kT = relativeTransverse k ((2⁻¹ : ℝ) • (p + p')) := (rfl)

@[simp]
lemma deltaT_ofMomenta :
    (ofMomenta p p' k).deltaT = relativeTransverse (p' - p) ((2⁻¹ : ℝ) • (p + p')) := (rfl)

/-- Exchanging the two hadrons reverses the skewness and the transverse momentum transfer. -/
theorem ofMomenta_swap : ofMomenta p' p k = (ofMomenta p p' k).swap := by
  apply Kinematics.ext
  · simp [add_comm p']
  · simp only [skewness_ofMomenta, skewness_swap, add_comm (plusComponent p'), ← neg_div,
      neg_sub]
  · simp [add_comm p']
  · simp [add_comm p']

/-- The kinematics read off from four-momenta is invariant under light-front transverse boosts,
provided the average hadron momentum has non-zero plus component. -/
theorem ofMomenta_transverseBoost (v : E²) (hP : plusComponent p + plusComponent p' ≠ 0) :
    ofMomenta (transverseBoost v p) (transverseBoost v p') (transverseBoost v k) =
      ofMomenta p p' k := by
  have hP' : plusComponent ((2⁻¹ : ℝ) • (p + p')) ≠ 0 := by
    rw [plusComponent_smul, plusComponent_add]
    exact mul_ne_zero (by norm_num) hP
  apply Kinematics.ext
  · simp
  · simp
  · simp only [kT_ofMomenta, ← map_add, ← map_smul]
    exact relativeTransverse_transverseBoost v k hP'
  · simp only [deltaT_ofMomenta, ← map_add, ← map_smul, ← map_sub]
    exact relativeTransverse_transverseBoost v (p' - p) hP'

/-- If the plus components of both hadrons are positive, the skewness lies in `(-1, 1)`. -/
lemma abs_skewness_ofMomenta_lt_one {p p' : Lorentz.Vector 3} (hp : 0 < plusComponent p)
    (hp' : 0 < plusComponent p') : |(ofMomenta p p' k).skewness| < 1 := by
  have h : 0 < plusComponent p + plusComponent p' := add_pos hp hp'
  rw [skewness_ofMomenta, abs_lt, lt_div_iff₀ h, div_lt_one h]
  constructor <;> linarith

/-- For off-forward kinematics whose light-like direction `n` defines the light-front plus
component up to a scale `c`, `⟪n, q⟫ₘ = c q⁺`, the GTMD skewness is the skewness of the off-forward
kinematics. -/
lemma skewness_ofMomenta_eq_skewness (F : OffForwardKinematics 3 M) {c : ℝ}
    (hn : ∀ q, ⟪F.n, q⟫ₘ = c * plusComponent q) :
    (ofMomenta F.p F.pPrime k).skewness = F.skewness := by
  have hc : c ≠ 0 :=
    left_ne_zero_of_mul (hn F.avgMomentum ▸ F.minkowskiProduct_n_avgMomentum_pos).ne'
  rw [F.skewness_eq_div, skewness_ofMomenta, hn, hn, ← mul_sub, ← mul_add, mul_div_mul_left _ _ hc]

/-- For off-forward kinematics whose light-like direction `n` defines the light-front plus
component up to a scale `c`, `⟪n, q⟫ₘ = c q⁺`, the GTMD transverse momentum transfer is the
transverse part of `Δ + 2 ξ P`. -/
lemma deltaT_ofMomenta_eq_transversePart_deltaOrthN (F : OffForwardKinematics 3 M) {c : ℝ}
    (hn : ∀ q, ⟪F.n, q⟫ₘ = c * plusComponent q) :
    (ofMomenta F.p F.pPrime k).deltaT = transversePart F.deltaOrthN := by
  have hpos := hn F.avgMomentum ▸ F.minkowskiProduct_n_avgMomentum_pos
  have hw : plusComponent F.deltaOrthN = 0 := by
    simpa [hn, left_ne_zero_of_mul hpos.ne'] using F.minkowskiProduct_n_deltaOrthN_eq_zero
  rw [deltaT_ofMomenta, ← F.delta_def, ← F.avgMomentum_def,
    ← relativeTransverse_of_plusComponent_eq_zero hw F.avgMomentum, F.deltaOrthN_def]
  simp [right_ne_zero_of_mul hpos.ne']

/-- For off-forward kinematics whose light-like direction `n` defines the light-front plus
component up to a scale `c`, `⟪n, q⟫ₘ = c q⁺`, the GTMD momentum transfer is the invariant
`t = Δ²` of the off-forward kinematics. -/
theorem tMom_ofMomenta_eq_tMom (F : OffForwardKinematics 3 M) {c : ℝ}
    (hn : ∀ q, ⟪F.n, q⟫ₘ = c * plusComponent q) :
    (ofMomenta F.p F.pPrime k).tMom M = F.tMom := by
  have hc : c ≠ 0 :=
    left_ne_zero_of_mul (hn F.avgMomentum ▸ F.minkowskiProduct_n_avgMomentum_pos).ne'
  have hw : plusComponent F.deltaOrthN = 0 := by
    simpa [hn, hc] using F.minkowskiProduct_n_deltaOrthN_eq_zero
  have hξ := skewness_ofMomenta_eq_skewness M k F hn
  have h := F.minkowskiProduct_deltaOrthN_self_eq
  rw [minkowskiProduct_self_eq_lightFront, hw,
    ← deltaT_ofMomenta_eq_transversePart_deltaOrthN M k F hn] at h
  rw [tMom_eq_iff _ _ (hξ ▸ F.abs_skewness_lt_one.ne), hξ]
  linarith

end Kinematics

/-- The off-forward kinematics of two on-shell hadron momenta `p`, `p'` of mass `M` with positive
plus components, with the light-like direction `ofLightFront 0 1 0` that defines the light-front
plus component (`minkowskiProduct_ofLightFront_zero_one_zero`). -/
def lightFrontOffForwardKinematics {M : ℝ} {p p' : Lorentz.Vector 3} (hp : ⟪p, p⟫ₘ = M ^ 2)
    (hp' : ⟪p', p'⟫ₘ = M ^ 2) (hpos : 0 < plusComponent p) (hpos' : 0 < plusComponent p') :
    OffForwardKinematics 3 M where
  p := p
  pPrime := p'
  n := ofLightFront 0 1 0
  minkowskiProduct_p_self := hp
  minkowskiProduct_pPrime_self := hp'
  minkowskiProduct_n_self := by simp [minkowskiProduct_ofLightFront_zero_one_zero]
  minkowskiProduct_n_p_pos := by rwa [minkowskiProduct_ofLightFront_zero_one_zero]
  minkowskiProduct_n_pPrime_pos := by rwa [minkowskiProduct_ofLightFront_zero_one_zero]

section

variable {M : ℝ} {p p' : Lorentz.Vector 3} (hp : ⟪p, p⟫ₘ = M ^ 2) (hp' : ⟪p', p'⟫ₘ = M ^ 2)
  (hpos : 0 < plusComponent p) (hpos' : 0 < plusComponent p')

@[simp]
lemma lightFrontOffForwardKinematics_p :
    (lightFrontOffForwardKinematics hp hp' hpos hpos').p = p := (rfl)

@[simp]
lemma lightFrontOffForwardKinematics_pPrime :
    (lightFrontOffForwardKinematics hp hp' hpos hpos').pPrime = p' := (rfl)

@[simp]
lemma lightFrontOffForwardKinematics_n :
    (lightFrontOffForwardKinematics hp hp' hpos hpos').n = ofLightFront 0 1 0 := (rfl)

end

namespace Kinematics

variable (K : Kinematics) (M : ℝ) (k : Lorentz.Vector 3)

/-- **The momentum transfer of on-shell momenta.** For hadron momenta `p`, `p'` on the mass
shell `M²` with positive plus components, the momentum transfer of the GTMD kinematics is the
invariant `t = (p' - p)²`. -/
theorem tMom_ofMomenta_eq_minkowskiProduct_sub_self {p p' : Lorentz.Vector 3}
    (hp : ⟪p, p⟫ₘ = M ^ 2) (hp' : ⟪p', p'⟫ₘ = M ^ 2) (hpos : 0 < plusComponent p)
    (hpos' : 0 < plusComponent p') :
    (ofMomenta p p' k).tMom M = ⟪p' - p, p' - p⟫ₘ := by
  simpa [OffForwardKinematics.tMom_def, OffForwardKinematics.delta_def] using
    tMom_ofMomenta_eq_tMom M k (lightFrontOffForwardKinematics hp hp' hpos hpos') (c := 1)
      (by simp [minkowskiProduct_ofLightFront_zero_one_zero])

/-- **Realisability.** A value of the GTMD kinematics is realised by a parton momentum and two
on-shell hadron momenta of mass `M` with positive plus components exactly when `|ξ| < 1`. -/
theorem exists_ofMomenta_eq_iff :
    (∃ p p' k : Lorentz.Vector 3, ⟪p, p⟫ₘ = M ^ 2 ∧ ⟪p', p'⟫ₘ = M ^ 2 ∧
      0 < plusComponent p ∧ 0 < plusComponent p' ∧ ofMomenta p p' k = K) ↔
      |K.skewness| < 1 := by
  constructor
  · rintro ⟨p, p', k, -, -, hp, hp', rfl⟩
    exact abs_skewness_ofMomenta_lt_one k hp hp'
  · intro hξ
    obtain ⟨hξ₁, hξ₂⟩ := abs_lt.mp hξ
    -- In the frame `P⁺ = 1`, `P_T = 0`: `p⁺ = 1 + ξ`, `p'⁺ = 1 - ξ`, `p_T = -ΔT / 2`,
    -- `p'_T = ΔT / 2`, and the minus components put both hadrons on the mass shell.
    set m : ℝ := M ^ 2 + ‖K.deltaT‖ ^ 2 / 4 with hm
    have hshell (a : ℝ) (ha : 0 < a) (w : E²) (hw : ‖w‖ ^ 2 = ‖K.deltaT‖ ^ 2 / 4) :
        ⟪ofLightFront a (m / (2 * a)) w, ofLightFront a (m / (2 * a)) w⟫ₘ = M ^ 2 := by
      rw [minkowskiProduct_ofLightFront_self, hw, mul_div_cancel₀ _ (by positivity), hm]
      ring
    have hhalf : ‖(2⁻¹ : ℝ) • K.deltaT‖ ^ 2 = ‖K.deltaT‖ ^ 2 / 4 := by
      rw [norm_smul]
      norm_num
      ring
    set p₀ := ofLightFront (1 + K.skewness) (m / (2 * (1 + K.skewness)))
      (-((2⁻¹ : ℝ) • K.deltaT)) with hp₀
    set p₀' := ofLightFront (1 - K.skewness) (m / (2 * (1 - K.skewness)))
      ((2⁻¹ : ℝ) • K.deltaT) with hp₀'
    have hT : transversePart ((2⁻¹ : ℝ) • (p₀ + p₀')) = 0 := by
      simp [hp₀, hp₀']
    have hplus : plusComponent ((2⁻¹ : ℝ) • (p₀ + p₀')) = 1 := by
      simp only [hp₀, hp₀', plusComponent_smul, plusComponent_add, plusComponent_ofLightFront]
      ring
    refine ⟨p₀, p₀', ofLightFront K.x 0 K.kT, hshell _ (by linarith) _ (by rw [norm_neg, hhalf]),
      hshell _ (by linarith) _ hhalf, by simp [hp₀]; linarith, by simp [hp₀']; linarith, ?_⟩
    apply Kinematics.ext
    · rw [x_ofMomenta, hplus, div_one, plusComponent_ofLightFront]
    · simp only [skewness_ofMomenta, hp₀, hp₀', plusComponent_ofLightFront]
      ring
    · rw [kT_ofMomenta, relativeTransverse_of_transversePart_eq_zero _ hT,
        transversePart_ofLightFront]
    · rw [deltaT_ofMomenta, relativeTransverse_of_transversePart_eq_zero _ hT]
      simp only [hp₀, hp₀', transversePart_sub, transversePart_ofLightFront, sub_neg_eq_add]
      rw [← add_smul]
      norm_num

end Kinematics

end GTMD
end Parton
end Particles
end EpsilonEridani
