/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.Kinematics.Emission

/-!
# The emitting source and the virtuality of an equivalent photon

A charged source of mass `m` and energy `E` that emits a photon and leaves with energy `E'` at
scattering angle `θ` hands the photon the virtuality `emissionVirtuality m E E' θ`, developed in
`EpsilonEridani.QFT.Scattering.Kinematics.Emission`. This module applies it to equivalent photons.

The explicit data of the subject are a `ChargedSource` (charge, mass, charge radius and Lorentz
factor in the collider frame), the photon variables `PhotonKinematics` (energy in the collider
frame and virtuality, with the real-photon point `PhotonKinematics.IsReal`), and the photon energy
fraction `PhotonKinematics.energyFraction`. The kinematic minimum of the virtuality is strictly
positive for a massive source (`ChargedSource.photonVirtualityMin_pos`) and strictly exceeds the
familiar `m² x² / (1 - x)` in terms of the energy fraction `x` carried by the photon
(`ChargedSource.sq_mul_sq_div_one_sub_lt_photonVirtualityMin`). The set
`ChargedSource.photonRegion s θmax` of photon variables allowed by the bounds is exactly the set of
photons emitted by `s` with scattering angle at most `θmax`
(`ChargedSource.mem_photonRegion_iff_exists`). Since the kinematic minimum is positive, every photon
a massive source emits has strictly positive virtuality
(`ChargedSource.virtuality_pos_of_mem_photonRegion`), so a massive source never emits a real photon
(`ChargedSource.not_isReal_of_mem_photonRegion`): the virtuality integral of the equivalent-photon
spectrum has a strictly positive lower limit, and the real-photon point `Q² = 0` lies outside the
physical region of every massive source. Rewritten through the photon energy `k = γ m x`, the
same minimum bounds the photon energy by the virtuality, `k² < γ² (1 - x) Q²`, as the
`PhotonKinematics` lemma
`energy_sq_lt_gamma_sq_mul_one_sub_energyFraction_mul_virtuality_of_mem_photonRegion`
states for a photon in the photon region, from the region-level bound `m² x² / (1 - x) < Q²`
(`ChargedSource.sq_mul_sq_div_one_sub_lt_virtuality_of_mem_photonRegion`). Under the coherence
condition `Q² R² ≤ 1` for a radius `R` of the source, any real number taken as a hypothesis on
the photon variables, this bounds the photon energy by the Lorentz factor over the radius,
`|k R| < γ`, the `PhotonKinematics` lemma
`abs_energy_mul_lt_gamma_of_mem_photonRegion_of_virtuality_mul_sq_le_one`.

## References

* V. M. Budnev, I. F. Ginzburg, G. V. Meledin and V. G. Serbo, *The two-photon particle
  production mechanism. Physical problems. Applications. Equivalent photon approximation*,
  Phys. Rep. **15** (1975) 181, section 2, where the minimum is quoted in its high-energy form
  `m² ω² / (E (E - ω))`.
* J. D. Jackson, *Classical Electrodynamics*, 3rd ed., Wiley (1999), section 15.4,
  *Weizsäcker–Williams method of virtual quanta*, for the bound `ω ≲ γ / R` on the photon energy
  under the coherence condition.
* G. Baur, K. Hencken, D. Trautmann, S. Sadovsky and Y. Kharlov, *Coherent γγ and γA interactions
  in very peripheral collisions at relativistic ion colliders*, Phys. Rep. **364** (2002) 359,
  section 2, for the same bound `ω ≲ γ / R` and the coherence condition `Q² ≲ 1 / R²`.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace Photoproduction
namespace Kinematics

open Real InnerProductGeometry Set EpsilonEridani.QFT.Scattering.Kinematics
open scoped InnerProductSpace Lorentz.Vector

/-! ### The charged source and the photon variables -/

/-- A charged source of equivalent photons, as explicit data: its charge in units of the positron
charge, its mass, its charge radius, and its Lorentz factor in the collider frame. -/
@[ext]
structure ChargedSource where
  /-- Electric charge in units of the positron charge. -/
  charge : ℝ
  /-- Mass of the source. -/
  mass : ℝ
  /-- Charge radius of the source. -/
  radius : ℝ
  /-- Lorentz factor of the source in the collider frame. -/
  gamma : ℝ

/-- The kinematics of a photon: its energy in the collider frame and its virtuality `Q²`, carried
explicitly so that a photoproduction statement is a statement about `Q² → 0` rather than about
an implicit `Q² = 0`. -/
@[ext]
structure PhotonKinematics where
  /-- Energy of the photon in the collider frame. -/
  energy : ℝ
  /-- Virtuality `Q² = -q²` of the photon. -/
  virtuality : ℝ

namespace ChargedSource

/-- The energy `γ m` of the source in the collider frame. -/
def energy (s : ChargedSource) : ℝ := s.gamma * s.mass

/-- Defining expression for `ChargedSource.energy`. -/
theorem energy_def (s : ChargedSource) : s.energy = s.gamma * s.mass := (rfl)

end ChargedSource

namespace PhotonKinematics

/-- The real-photon point `Q² = 0`. -/
def IsReal (k : PhotonKinematics) : Prop := k.virtuality = 0

/-- A photon is real exactly at zero virtuality. -/
@[simp]
theorem isReal_iff (k : PhotonKinematics) : k.IsReal ↔ k.virtuality = 0 := (Iff.rfl)

/-- The fraction `x = k / E` of the source energy carried by the photon. -/
def energyFraction (k : PhotonKinematics) (s : ChargedSource) : ℝ := k.energy / s.energy

/-- Defining expression for `PhotonKinematics.energyFraction`. -/
theorem energyFraction_def (k : PhotonKinematics) (s : ChargedSource) :
    k.energyFraction s = k.energy / s.energy :=
  (rfl)

/-- The source keeps the fraction `1 - x` of its energy. -/
theorem one_sub_energyFraction_mul_energy (k : PhotonKinematics) {s : ChargedSource}
    (hs : s.energy ≠ 0) : (1 - k.energyFraction s) * s.energy = s.energy - k.energy := by
  simp only [energyFraction, sub_mul, div_mul_cancel₀ _ hs, one_mul]

/-- The photon energy is the fraction `x` of the source energy `γ m`: `k = γ m x`. -/
theorem energy_eq_gamma_mul_mass_mul_energyFraction (k : PhotonKinematics) {s : ChargedSource}
    (hs : s.energy ≠ 0) : k.energy = s.gamma * s.mass * k.energyFraction s := by
  rw [energyFraction_def, ← ChargedSource.energy_def, mul_div_cancel₀ _ hs]

/-- The photon `q = p - p'` emitted by a source going from four-momentum `p` to `p'`: its energy
is the energy lost by the source, and its virtuality is `-q²`. -/
def ofEmission {d : ℕ} (p p' : Lorentz.Vector d) : PhotonKinematics where
  energy := p.timeComponent - p'.timeComponent
  virtuality := -⟪p - p', p - p'⟫ₘ

/-- The energy of the emitted photon is the energy lost by the source. -/
@[simp]
theorem ofEmission_energy {d : ℕ} (p p' : Lorentz.Vector d) :
    (ofEmission p p').energy = p.timeComponent - p'.timeComponent :=
  (rfl)

/-- The virtuality of the emitted photon is `-(p - p')²`. -/
@[simp]
theorem ofEmission_virtuality {d : ℕ} (p p' : Lorentz.Vector d) :
    (ofEmission p p').virtuality = -⟪p - p', p - p'⟫ₘ :=
  (rfl)

end PhotonKinematics

namespace ChargedSource

variable (s : ChargedSource)

/-- The virtuality of a photon carrying the energy fraction `x`, emitted by the source `s` at
scattering angle `θ`. -/
def photonVirtuality (x θ : ℝ) : ℝ :=
  emissionVirtuality s.mass s.energy ((1 - x) * s.energy) θ

/-- Defining expression for `ChargedSource.photonVirtuality`. -/
theorem photonVirtuality_def (x θ : ℝ) :
    s.photonVirtuality x θ = emissionVirtuality s.mass s.energy ((1 - x) * s.energy) θ :=
  (rfl)

/-- The kinematic minimum of the virtuality of a photon carrying the energy fraction `x`, reached
at zero scattering angle. -/
def photonVirtualityMin (x : ℝ) : ℝ := s.photonVirtuality x 0

/-- Defining expression for `ChargedSource.photonVirtualityMin`. -/
theorem photonVirtualityMin_def (x : ℝ) : s.photonVirtualityMin x = s.photonVirtuality x 0 :=
  (rfl)

variable {s}

/-- A source of non-zero energy that emits the fraction `x ≠ 0` of it changes its energy. -/
private theorem energy_ne_one_sub_mul_energy (hs : s.energy ≠ 0) {x : ℝ} (hx : x ≠ 0) :
    s.energy ≠ (1 - x) * s.energy := by
  intro h
  have : x * s.energy = 0 := by linarith
  exact hx ((mul_eq_zero.1 this).resolve_right hs)

/-- **The kinematic minimum strictly exceeds `m² x² / (1 - x)`**, the form in which it is usually
quoted for a high-energy source. -/
theorem sq_mul_sq_div_one_sub_lt_photonVirtualityMin (hm : 0 < s.mass) (hE : s.mass ≤ s.energy)
    {x : ℝ} (hx : x ≠ 0) (hE' : s.mass ≤ (1 - x) * s.energy) :
    s.mass ^ 2 * x ^ 2 / (1 - x) < s.photonVirtualityMin x := by
  have hEpos : s.energy ≠ 0 := (hm.trans_le hE).ne'
  have hlt := sq_mul_sub_sq_div_mul_lt_emissionVirtuality_zero hm.ne'
    ((abs_of_pos hm).trans_le hE) ((abs_of_pos hm).trans_le hE')
    (energy_ne_one_sub_mul_energy hEpos hx)
  have h1x : 1 - x ≠ 0 := by
    intro h
    rw [h, zero_mul] at hE'
    linarith
  rw [photonVirtualityMin, photonVirtuality]
  convert hlt using 1
  field_simp
  ring

/-- **The kinematic minimum of the virtuality is strictly positive for a massive source** whose
energy before and after emitting the fraction `x ≠ 0` lies above its mass. -/
theorem photonVirtualityMin_pos (hm : 0 < s.mass) (hE : s.mass ≤ s.energy) {x : ℝ} (hx : x ≠ 0)
    (hE' : s.mass ≤ (1 - x) * s.energy) : 0 < s.photonVirtualityMin x := by
  -- the source keeps a positive share of its positive energy, so `0 < 1 - x`
  have h1x : 0 < 1 - x := by nlinarith
  exact (div_pos (by positivity) h1x).trans
    (sq_mul_sq_div_one_sub_lt_photonVirtualityMin hm hE hx hE')

/-- The photon variables a source `s` can emit at scattering angle at most `θmax`: the photon
carries energy, the source keeps more energy than its mass (so that it leaves with a non-zero
momentum and the scattering angle is defined), and the virtuality lies between the kinematic
minimum and its value at `θmax`. -/
def photonRegion (s : ChargedSource) (θmax : ℝ) : Set PhotonKinematics :=
  {k | 0 < k.energy ∧ k.energy < s.energy - s.mass ∧
    s.photonVirtualityMin (k.energyFraction s) ≤ k.virtuality ∧
    k.virtuality ≤ s.photonVirtuality (k.energyFraction s) θmax}

/-- Defining expression for `ChargedSource.photonRegion`. -/
theorem photonRegion_def (s : ChargedSource) (θmax : ℝ) :
    s.photonRegion θmax = {k | 0 < k.energy ∧ k.energy < s.energy - s.mass ∧
      s.photonVirtualityMin (k.energyFraction s) ≤ k.virtuality ∧
      k.virtuality ≤ s.photonVirtuality (k.energyFraction s) θmax} :=
  (rfl)

/-- Membership in the photon region, unfolded. -/
theorem mem_photonRegion_iff {θmax : ℝ} {k : PhotonKinematics} :
    k ∈ s.photonRegion θmax ↔ 0 < k.energy ∧ k.energy < s.energy - s.mass ∧
      s.photonVirtualityMin (k.energyFraction s) ≤ k.virtuality ∧
      k.virtuality ≤ s.photonVirtuality (k.energyFraction s) θmax :=
  (Iff.rfl)

/-- In terms of the photon energy `k`, the source energy after the emission is `E - k`. -/
theorem photonVirtuality_energyFraction (k : PhotonKinematics) (hs : s.energy ≠ 0) (θ : ℝ) :
    s.photonVirtuality (k.energyFraction s) θ =
      emissionVirtuality s.mass s.energy (s.energy - k.energy) θ := by
  rw [photonVirtuality, k.one_sub_energyFraction_mul_energy hs]

/-- **Every photon emitted at scattering angle at most `θmax` lies in the photon region.** -/
theorem ofEmission_mem_photonRegion {d : ℕ} {p p' : Lorentz.Vector d}
    (hp : ⟪p, p⟫ₘ = s.mass ^ 2) (hp' : ⟪p', p'⟫ₘ = s.mass ^ 2)
    (hE : p.timeComponent = s.energy) (hE' : s.mass < p'.timeComponent)
    (hk : p'.timeComponent < p.timeComponent) {θmax : ℝ}
    (hθ : angle p.spatialPart p'.spatialPart ≤ θmax) (hπ : θmax ≤ π) :
    PhotonKinematics.ofEmission p p' ∈ s.photonRegion θmax := by
  have hk0 : 0 < (PhotonKinematics.ofEmission p p').energy := by
    rw [PhotonKinematics.ofEmission_energy]; linarith
  have hk1 : (PhotonKinematics.ofEmission p p').energy < s.energy - s.mass := by
    rw [PhotonKinematics.ofEmission_energy]; linarith
  -- on the mass shell, `E'² ≥ m²`, so `E' > m` forces `E' > 0` and the source energy is non-zero
  have hE'sq : s.mass ^ 2 ≤ p'.timeComponent ^ 2 := by
    rw [Lorentz.Vector.minkowskiProduct_self_eq_sq_sub] at hp'
    nlinarith [sq_nonneg ‖p'.spatialPart‖]
  have hs : s.energy ≠ 0 := by
    rw [← hE]
    have : 0 < p'.timeComponent := by
      by_contra h
      nlinarith
    linarith
  -- the source keeps the energy `p'⁰`, and the photon virtuality is the emission virtuality
  have hE'k : s.energy - (PhotonKinematics.ofEmission p p').energy = p'.timeComponent := by
    simp [← hE]
  have hv := neg_minkowskiProduct_sub_self_eq_emissionVirtuality hp hp'
  rw [hE] at hv
  have hmono := monotoneOn_emissionVirtuality s.mass s.energy p'.timeComponent
  have hang : angle p.spatialPart p'.spatialPart ∈ Icc 0 π := ⟨angle_nonneg _ _, angle_le_pi _ _⟩
  refine mem_photonRegion_iff.2 ⟨hk0, hk1, ?_, ?_⟩ <;>
    simp only [photonVirtualityMin, photonVirtuality_energyFraction _ hs, hE'k,
      PhotonKinematics.ofEmission_virtuality, hv]
  · exact hmono ⟨le_rfl, pi_pos.le⟩ hang (angle_nonneg _ _)
  · exact hmono hang ⟨(angle_nonneg _ _).trans hθ, hπ⟩ hθ

/-- **The photon region is exactly the set of photons emitted at scattering angle at most
`θmax`.** In at least two spatial dimensions, a photon lies in `s.photonRegion θmax` if and only
if it is the photon `p - p'` of an emission in which the source, on its mass shell, has energy
`s.energy` before and keeps more than its mass after, with scattering angle at most `θmax`. -/
theorem mem_photonRegion_iff_exists (hm : 0 ≤ s.mass) {d : ℕ} (hd : 2 ≤ d) {θmax : ℝ}
    (h0 : 0 ≤ θmax) (hπ : θmax ≤ π) {k : PhotonKinematics} :
    k ∈ s.photonRegion θmax ↔ ∃ p p' : Lorentz.Vector d, ⟪p, p⟫ₘ = s.mass ^ 2 ∧
      ⟪p', p'⟫ₘ = s.mass ^ 2 ∧ p.timeComponent = s.energy ∧ s.mass < p'.timeComponent ∧
      p'.timeComponent < p.timeComponent ∧ angle p.spatialPart p'.spatialPart ≤ θmax ∧
      PhotonKinematics.ofEmission p p' = k := by
  constructor
  · rintro ⟨hk0, hk1, hmin, hmax⟩
    set E := s.energy
    set E' := E - k.energy
    set m := s.mass
    have hs : s.energy ≠ 0 := by linarith
    rw [photonVirtualityMin, photonVirtuality_energyFraction _ hs] at hmin
    rw [photonVirtuality_energyFraction _ hs] at hmax
    have hmem : k.virtuality ∈ emissionVirtuality m E E' '' Icc 0 θmax := by
      rw [image_emissionVirtuality_Icc m E E' h0 hπ]
      exact ⟨hmin, hmax⟩
    obtain ⟨θ, ⟨hθ0, hθ⟩, hθk⟩ := hmem
    have hE'm : m < E' := by simp only [E']; linarith
    obtain ⟨p, p', hpm, hp'm, hpt, hp't, hang⟩ := exists_massShell_pair_angle_eq hd
      (m := m) (E := E) (E' := E') (by rw [abs_of_nonneg hm]; linarith)
      (by rw [abs_of_nonneg hm]; linarith) hθ0 (hθ.trans hπ)
    refine ⟨p, p', hpm, hp'm, hpt, hp't ▸ hE'm, by simp only [hpt, hp't, E']; linarith,
      hang.trans_le hθ, ?_⟩
    ext
    · simp [hpt, hp't, E']
    · rw [PhotonKinematics.ofEmission_virtuality, ← hθk, ← hang, ← hpt, ← hp't]
      exact neg_minkowskiProduct_sub_self_eq_emissionVirtuality hpm hp'm
  · rintro ⟨p, p', hp, hp', hE, hE', hk, hθ, rfl⟩
    exact ofEmission_mem_photonRegion hp hp' hE hE' hk hθ hπ

/-- A source that can emit a photon has energy above its mass. -/
theorem mass_lt_energy_of_mem_photonRegion {θmax : ℝ} {k : PhotonKinematics}
    (hk : k ∈ s.photonRegion θmax) : s.mass < s.energy := by
  obtain ⟨hk0, hk1, -⟩ := mem_photonRegion_iff.1 hk
  linarith

/-- A photon in the photon region of a source of non-negative mass carries a positive fraction of
the source energy. -/
theorem energyFraction_pos_of_mem_photonRegion (hm : 0 ≤ s.mass) {θmax : ℝ}
    {k : PhotonKinematics} (hk : k ∈ s.photonRegion θmax) : 0 < k.energyFraction s := by
  obtain ⟨hk0, hk1, -⟩ := mem_photonRegion_iff.1 hk
  rw [PhotonKinematics.energyFraction_def]
  exact div_pos hk0 (by linarith)

/-- A photon in the photon region of a source of non-negative mass carries less than the whole
source energy. -/
theorem energyFraction_lt_one_of_mem_photonRegion (hm : 0 ≤ s.mass) {θmax : ℝ}
    {k : PhotonKinematics} (hk : k ∈ s.photonRegion θmax) : k.energyFraction s < 1 := by
  obtain ⟨hk0, hk1, -⟩ := mem_photonRegion_iff.1 hk
  rw [PhotonKinematics.energyFraction_def, div_lt_one (by linarith)]
  linarith

/-- After emitting a photon of its photon region, the source keeps more energy than its mass. -/
theorem mass_lt_one_sub_energyFraction_mul_energy_of_mem_photonRegion {θmax : ℝ}
    {k : PhotonKinematics} (hk : k ∈ s.photonRegion θmax) :
    s.mass < (1 - k.energyFraction s) * s.energy := by
  obtain ⟨hk0, hk1, -⟩ := mem_photonRegion_iff.1 hk
  rcases eq_or_ne s.energy 0 with hs | hs
  · rw [hs, mul_zero]
    linarith
  · rw [k.one_sub_energyFraction_mul_energy hs]
    linarith

/-- A source of non-negative mass with energy above its mass moves with Lorentz factor above one. -/
theorem one_lt_gamma_of_mass_lt_energy (hm : 0 ≤ s.mass) (hE : s.mass < s.energy) :
    1 < s.gamma := by
  rw [energy_def] at hE
  -- if `γ ≤ 1` then `γ m ≤ m` for `0 ≤ m`, contradicting `m < γ m`
  nlinarith

/-- **The virtuality strictly exceeds `m² x² / (1 - x)`.** Every photon in the photon region of a
source of positive mass, carrying the fraction `x` of the energy of the source, has
`m² x² / (1 - x) < Q²`: the kinematic minimum in its high-energy form bounds the virtuality. -/
theorem sq_mul_sq_div_one_sub_lt_virtuality_of_mem_photonRegion (hm : 0 < s.mass) {θmax : ℝ}
    {k : PhotonKinematics} (hk : k ∈ s.photonRegion θmax) :
    s.mass ^ 2 * k.energyFraction s ^ 2 / (1 - k.energyFraction s) < k.virtuality :=
  (sq_mul_sq_div_one_sub_lt_photonVirtualityMin hm (mass_lt_energy_of_mem_photonRegion hk).le
    (energyFraction_pos_of_mem_photonRegion hm.le hk).ne'
    (mass_lt_one_sub_energyFraction_mul_energy_of_mem_photonRegion hk).le).trans_le
    (mem_photonRegion_iff.1 hk).2.2.1

/-- **A massive source emits only at strictly positive virtuality.** Every photon in the photon
region of a source of positive mass has strictly positive virtuality. -/
theorem virtuality_pos_of_mem_photonRegion (hm : 0 < s.mass) {θmax : ℝ} {k : PhotonKinematics}
    (hk : k ∈ s.photonRegion θmax) : 0 < k.virtuality :=
  (div_pos (mul_pos (pow_pos hm 2) (pow_pos (energyFraction_pos_of_mem_photonRegion hm.le hk) 2))
    (sub_pos.2 (energyFraction_lt_one_of_mem_photonRegion hm.le hk))).trans
    (sq_mul_sq_div_one_sub_lt_virtuality_of_mem_photonRegion hm hk)

/-- **A massive source never emits a real photon.** -/
theorem not_isReal_of_mem_photonRegion (hm : 0 < s.mass) {θmax : ℝ} {k : PhotonKinematics}
    (hk : k ∈ s.photonRegion θmax) : ¬ k.IsReal := by
  rw [PhotonKinematics.isReal_iff]
  exact (virtuality_pos_of_mem_photonRegion hm hk).ne'

end ChargedSource

/-! ### The photon energy in the collider frame -/

namespace PhotonKinematics

variable {s : ChargedSource}

/-- **The photon energy is bounded by the virtuality.** A photon in the photon region of a source
of positive mass, of energy `k` carrying the fraction `x` of the energy of the source with
Lorentz factor `γ`, has `k² < γ² (1 - x) Q²`: in the collider frame, `k / γ` is at most of the
order of `√(Q²)`. This is the bound `m² x² / (1 - x) < Q²`
(`ChargedSource.sq_mul_sq_div_one_sub_lt_virtuality_of_mem_photonRegion`) rewritten through
`k = γ m x`. -/
theorem energy_sq_lt_gamma_sq_mul_one_sub_energyFraction_mul_virtuality_of_mem_photonRegion
    (k : PhotonKinematics) (hm : 0 < s.mass) {θmax : ℝ} (hk : k ∈ s.photonRegion θmax) :
    k.energy ^ 2 < s.gamma ^ 2 * (1 - k.energyFraction s) * k.virtuality := by
  have hE := ChargedSource.mass_lt_energy_of_mem_photonRegion hk
  have hγ := zero_lt_one.trans (ChargedSource.one_lt_gamma_of_mass_lt_energy hm.le hE)
  have hx1 := ChargedSource.energyFraction_lt_one_of_mem_photonRegion hm.le hk
  have hQ := ChargedSource.sq_mul_sq_div_one_sub_lt_virtuality_of_mem_photonRegion hm hk
  rw [div_lt_iff₀ (sub_pos.2 hx1)] at hQ
  rw [k.energy_eq_gamma_mul_mass_mul_energyFraction (hm.trans hE).ne']
  nlinarith [mul_lt_mul_of_pos_left hQ (pow_pos hγ 2)]

/-- **The photon energy of coherent emission is bounded by the Lorentz factor over the radius.**
If a massive source of Lorentz factor `γ` emits a photon of its photon region within the coherence
bound `Q² R² ≤ 1` for a radius `R`, the photon energy in the collider frame satisfies
`|k R| < γ`. The radius `R` is any real number, of either sign: the charge radius `s.radius` of
the source, or a root-mean-square radius of its charge distribution. -/
theorem abs_energy_mul_lt_gamma_of_mem_photonRegion_of_virtuality_mul_sq_le_one
    (k : PhotonKinematics) (hm : 0 < s.mass) {θmax R : ℝ} (hk : k ∈ s.photonRegion θmax)
    (hcoh : k.virtuality * R ^ 2 ≤ 1) : |k.energy * R| < s.gamma := by
  have hE := ChargedSource.mass_lt_energy_of_mem_photonRegion hk
  have hγ := zero_lt_one.trans (ChargedSource.one_lt_gamma_of_mass_lt_energy hm.le hE)
  have hx0 := ChargedSource.energyFraction_pos_of_mem_photonRegion hm.le hk
  have hx1 := ChargedSource.energyFraction_lt_one_of_mem_photonRegion hm.le hk
  have hc : 0 ≤ s.gamma ^ 2 * (1 - k.energyFraction s) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  -- `(k R)² ≤ γ² (1 - x) Q² R² ≤ γ² (1 - x) < γ²`
  have hsq : (k.energy * R) ^ 2 < s.gamma ^ 2 :=
    calc (k.energy * R) ^ 2 = k.energy ^ 2 * R ^ 2 := mul_pow _ _ _
      _ ≤ s.gamma ^ 2 * (1 - k.energyFraction s) * (k.virtuality * R ^ 2) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (k.energy_sq_lt_gamma_sq_mul_one_sub_energyFraction_mul_virtuality_of_mem_photonRegion
            hm hk).le (sq_nonneg _)
      _ ≤ s.gamma ^ 2 * (1 - k.energyFraction s) := mul_le_of_le_one_right hc hcoh
      _ < s.gamma ^ 2 := by nlinarith [mul_pos (pow_pos hγ 2) hx0]
  exact abs_lt_of_sq_lt_sq hsq hγ.le

end PhotonKinematics

end Kinematics
end Photoproduction
end Scattering
end QFT
end EpsilonEridani
