/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Topology.Order.IntermediateValue
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions

/-!
# The emitting source and the virtuality of an equivalent photon

A charged source of mass `m` and energy `E` that emits a photon and leaves with energy `E'` at
scattering angle `θ` hands the photon the four-momentum `q = p - p'`, whose virtuality is

  `Q² = -q² = 2 (E E' - |p⃗| |p⃗'| cos θ - m²)`,  `|p⃗| = √(E² - m²)`,  `|p⃗'| = √(E'² - m²)`.

This module develops that formula and the region it carves out.

* `emissionVirtuality m E E' θ` is the right-hand side above, and
  `neg_minkowskiProduct_sub_self_eq_emissionVirtuality` proves that it *is* `-q²` for any pair of
  on-shell four-momenta of `Physlib`, with `θ` the angle between their spatial parts.
* It is monotone in the angle on `[0, π]`, so the virtualities reachable at scattering angle at most
  `θmax` form the interval between its value at `θ = 0` and its value at `θmax`
  (`image_emissionVirtuality_Icc`).
* The value at `θ = 0` is the kinematic minimum. It vanishes for a massless source, and is strictly
  positive as soon as the source is massive and the photon carries energy
  (`emissionVirtuality_zero_pos_iff`). It strictly exceeds the familiar
  `m² (E - E')² / (E E')`, i.e. `m² x² / (1 - x)` in terms of the energy fraction `x` carried by
  the photon (`div_lt_emissionVirtuality_zero`,
  `ChargedSource.sq_mass_mul_sq_div_lt_photonVirtualityMin`).

On top of this sits the explicit data of the subject: a `ChargedSource` (charge, mass, charge
radius and Lorentz factor in the collider frame), the photon variables `PhotonKin` (energy in the
collider frame and virtuality, with the real-photon point `PhotonKin.IsReal`), and the photon
energy fraction `PhotonKin.energyFraction`. The set `ChargedSource.photonRegion s θmax` of photon
variables allowed by the bounds is exactly the set of photons emitted by `s` with scattering angle
at most `θmax` (`ChargedSource.mem_photonRegion_iff_exists`). Since the kinematic minimum is
positive, a massive source never emits a real photon
(`ChargedSource.not_isReal_of_mem_photonRegion`): the virtuality integral of the equivalent-photon
spectrum has a strictly positive lower limit, and the real-photon point `Q² = 0` lies outside the
physical region of every massive source.

## References

* V. M. Budnev, I. F. Ginzburg, G. V. Meledin and V. G. Serbo, *The two-photon particle
  production mechanism. Physical problems. Applications. Equivalent photon approximation*,
  Phys. Rep. **15** (1975) 181, section 2, where the minimum is quoted in its high-energy form
  `m² ω² / (E (E - ω))`.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace Photoproduction

open Real InnerProductGeometry Set
open scoped InnerProductSpace Lorentz.Vector

/-! ### The emission virtuality as a function of the scattering angle -/

/-- The virtuality `Q² = 2 (E E' - |p⃗| |p⃗'| cos θ - m²)` of the photon emitted when a source of
mass `m` goes from energy `E` to energy `E'` and is scattered by the angle `θ`, with the
magnitudes of the three-momenta `|p⃗| = √(E² - m²)` and `|p⃗'| = √(E'² - m²)` fixed by the mass
shell. -/
def emissionVirtuality (m E E' θ : ℝ) : ℝ :=
  2 * (E * E' - √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) * cos θ - m ^ 2)

theorem emissionVirtuality_def (m E E' θ : ℝ) :
    emissionVirtuality m E E' θ =
      2 * (E * E' - √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) * cos θ - m ^ 2) :=
  (rfl)

/-- The emission virtuality is continuous in the scattering angle. -/
theorem continuous_emissionVirtuality (m E E' : ℝ) : Continuous (emissionVirtuality m E E') := by
  unfold emissionVirtuality
  fun_prop

/-- The emission virtuality grows with the scattering angle on `[0, π]`. -/
theorem monotoneOn_emissionVirtuality (m E E' : ℝ) :
    MonotoneOn (emissionVirtuality m E E') (Icc 0 π) := by
  intro θ hθ θ' hθ' hle
  have hcos : cos θ' ≤ cos θ := cos_le_cos_of_nonneg_of_le_pi hθ.1 hθ'.2 hle
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  unfold emissionVirtuality
  nlinarith [mul_le_mul_of_nonneg_left hcos hP]

/-- The virtualities reachable at scattering angles in `[0, θmax]` form the interval between the
kinematic minimum, at `θ = 0`, and the value at `θmax`. -/
theorem image_emissionVirtuality_Icc (m E E' : ℝ) {θmax : ℝ} (h0 : 0 ≤ θmax) (hπ : θmax ≤ π) :
    emissionVirtuality m E E' '' Icc 0 θmax =
      Icc (emissionVirtuality m E E' 0) (emissionVirtuality m E E' θmax) :=
  (continuous_emissionVirtuality m E E').continuousOn.image_Icc_of_monotoneOn h0
    ((monotoneOn_emissionVirtuality m E E').mono (Icc_subset_Icc_right hπ))

/-- A massless source emits at zero minimum virtuality. -/
theorem emissionVirtuality_zero_eq_zero_of_mass_eq_zero {m E E' : ℝ} (hm : m = 0) (hE : 0 ≤ E)
    (hE' : 0 ≤ E') : emissionVirtuality m E E' 0 = 0 := by
  subst hm
  simp [emissionVirtuality, Real.sqrt_sq hE, Real.sqrt_sq hE']

/-- The algebraic identity behind the kinematic minimum: with `A = E E' - m²` and the momenta
`P = √(E² - m²)`, `P' = √(E'² - m²)`, one has `A² - (P P')² = m² (E - E')²`. -/
private theorem sq_sub_sq_momenta {m E E' : ℝ} (hE : |m| ≤ E) (hE' : |m| ≤ E') :
    (E * E' - m ^ 2) ^ 2 - (√(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2)) ^ 2 =
      m ^ 2 * (E - E') ^ 2 := by
  have h1 : 0 ≤ E ^ 2 - m ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
  have h2 : 0 ≤ E' ^ 2 - m ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
  rw [mul_pow, Real.sq_sqrt h1, Real.sq_sqrt h2]
  ring

/-- For a massive source and a photon carrying energy, the momentum product `P P'` is strictly
below `E E' - m²`. -/
private theorem momenta_lt {m E E' : ℝ} (hm : m ≠ 0) (hE : |m| ≤ E) (hE' : |m| ≤ E')
    (hne : E ≠ E') :
    √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) < E * E' - m ^ 2 := by
  have hA : 0 ≤ E * E' - m ^ 2 := by
    nlinarith [sq_abs m, mul_le_mul hE hE' (abs_nonneg m) (le_trans (abs_nonneg m) hE)]
  have hB : 0 < m ^ 2 * (E - E') ^ 2 := by
    have := sub_ne_zero.2 hne
    positivity
  have hid := sq_sub_sq_momenta hE hE'
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  nlinarith

/-- The kinematic minimum of the virtuality is non-negative whenever both energies lie above the
mass. -/
theorem emissionVirtuality_zero_nonneg {m E E' : ℝ} (hE : |m| ≤ E) (hE' : |m| ≤ E') :
    0 ≤ emissionVirtuality m E E' 0 := by
  have hA : 0 ≤ E * E' - m ^ 2 := by
    nlinarith [sq_abs m, mul_le_mul hE hE' (abs_nonneg m) (le_trans (abs_nonneg m) hE)]
  have hid := sq_sub_sq_momenta hE hE'
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  have hle : √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) ≤ E * E' - m ^ 2 := by
    nlinarith [sq_nonneg m, sq_nonneg (E - E')]
  simp only [emissionVirtuality, cos_zero, mul_one]
  linarith

/-- **The kinematic minimum is strictly positive exactly for a massive source emitting a photon
of non-zero energy.** -/
theorem emissionVirtuality_zero_pos_iff {m E E' : ℝ} (hE : |m| ≤ E) (hE' : |m| ≤ E') :
    0 < emissionVirtuality m E E' 0 ↔ m ≠ 0 ∧ E ≠ E' := by
  constructor
  · intro h
    refine ⟨fun hm => ?_, fun hEE => ?_⟩
    · rw [emissionVirtuality_zero_eq_zero_of_mass_eq_zero hm (le_trans (abs_nonneg _) hE)
        (le_trans (abs_nonneg _) hE')] at h
      exact lt_irrefl _ h
    · subst hEE
      have h1 : 0 ≤ E ^ 2 - m ^ 2 := by nlinarith [sq_abs m, abs_nonneg m]
      have : emissionVirtuality m E E 0 = 0 := by
        simp only [emissionVirtuality, cos_zero, mul_one, Real.mul_self_sqrt h1]
        ring
      rw [this] at h
      exact lt_irrefl _ h
  · rintro ⟨hm, hne⟩
    have := momenta_lt hm hE hE' hne
    simp only [emissionVirtuality, cos_zero, mul_one]
    linarith

/-- **The kinematic minimum strictly exceeds `m² (E - E')² / (E E' - m²)`.** For a high-energy
source the bound approaches the minimum, and it is itself above the familiar high-energy form
`m² (E - E')² / (E E')`; see `div_lt_emissionVirtuality_zero`. -/
theorem div_sub_lt_emissionVirtuality_zero {m E E' : ℝ} (hm : m ≠ 0) (hE : |m| ≤ E)
    (hE' : |m| ≤ E') (hne : E ≠ E') :
    m ^ 2 * (E - E') ^ 2 / (E * E' - m ^ 2) < emissionVirtuality m E E' 0 := by
  have hlt := momenta_lt hm hE hE' hne
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  have hA : 0 < E * E' - m ^ 2 := hP.trans_lt hlt
  have hid := sq_sub_sq_momenta hE hE'
  rw [div_lt_iff₀ hA]
  simp only [emissionVirtuality, cos_zero, mul_one]
  nlinarith

/-- **The kinematic minimum strictly exceeds its high-energy form `m² (E - E')² / (E E')`.** -/
theorem div_lt_emissionVirtuality_zero {m E E' : ℝ} (hm : m ≠ 0) (hE : |m| ≤ E)
    (hE' : |m| ≤ E') (hne : E ≠ E') :
    m ^ 2 * (E - E') ^ 2 / (E * E') < emissionVirtuality m E E' 0 := by
  have hlt := momenta_lt hm hE hE' hne
  have hP : 0 ≤ √(E ^ 2 - m ^ 2) * √(E' ^ 2 - m ^ 2) := by positivity
  have hA : 0 < E * E' - m ^ 2 := hP.trans_lt hlt
  have hm2 : 0 < m ^ 2 := by positivity
  have hB : 0 < m ^ 2 * (E - E') ^ 2 := mul_pos hm2 (by
    have := sub_ne_zero.2 hne
    positivity)
  refine lt_of_le_of_lt ?_ (div_sub_lt_emissionVirtuality_zero hm hE hE' hne)
  exact div_le_div_of_nonneg_left hB.le hA (by linarith)

/-! ### The emission virtuality of on-shell four-momenta -/

/-- **The virtuality of the emitted photon.** If a source of mass `m` with four-momentum `p` emits
a photon and leaves with four-momentum `p'` of the same mass, the photon `q = p - p'` has
virtuality `-q² = emissionVirtuality m E E' θ`, with `E`, `E'` the two energies and `θ` the angle
between the spatial momenta. -/
theorem neg_minkowskiProduct_sub_self_eq_emissionVirtuality {d : ℕ} {p p' : Lorentz.Vector d}
    {m : ℝ} (hp : ⟪p, p⟫ₘ = m ^ 2) (hp' : ⟪p', p'⟫ₘ = m ^ 2) :
    -⟪p - p', p - p'⟫ₘ = emissionVirtuality m p.timeComponent p'.timeComponent
      (angle p.spatialPart p'.spatialPart) := by
  rw [Lorentz.Vector.minkowskiProduct_sub_self, hp, hp',
    Lorentz.Vector.minkowskiProduct_eq_timeComponent_spatialPart, ← cos_angle_mul_norm_mul_norm,
    Lorentz.Vector.norm_spatialPart_eq_sqrt hp, Lorentz.Vector.norm_spatialPart_eq_sqrt hp',
    emissionVirtuality]
  ring

/-! ### The charged source and the photon variables -/

/-- A charged source of equivalent photons, as explicit data: its charge in units of the positron
charge, its mass, its charge radius, and its Lorentz factor in the collider frame. -/
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
structure PhotonKin where
  /-- Energy of the photon in the collider frame. -/
  energy : ℝ
  /-- Virtuality `Q² = -q²` of the photon. -/
  virtuality : ℝ

namespace ChargedSource

/-- The energy `γ m` of the source in the collider frame. -/
def energy (s : ChargedSource) : ℝ := s.gamma * s.mass

theorem energy_def (s : ChargedSource) : s.energy = s.gamma * s.mass := (rfl)

end ChargedSource

namespace PhotonKin

/-- The real-photon point `Q² = 0`. -/
def IsReal (k : PhotonKin) : Prop := k.virtuality = 0

/-- A photon is real exactly at zero virtuality. -/
@[simp]
theorem isReal_iff (k : PhotonKin) : k.IsReal ↔ k.virtuality = 0 := (Iff.rfl)

/-- The fraction `x = k / E` of the source energy carried by the photon. -/
def energyFraction (k : PhotonKin) (s : ChargedSource) : ℝ := k.energy / s.energy

theorem energyFraction_def (k : PhotonKin) (s : ChargedSource) :
    k.energyFraction s = k.energy / s.energy :=
  (rfl)

/-- The source keeps the fraction `1 - x` of its energy. -/
theorem one_sub_energyFraction_mul_energy (k : PhotonKin) {s : ChargedSource}
    (hs : s.energy ≠ 0) : (1 - k.energyFraction s) * s.energy = s.energy - k.energy := by
  rw [energyFraction, sub_mul, div_mul_cancel₀ _ hs, one_mul]

/-- The photon `q = p - p'` emitted by a source going from four-momentum `p` to `p'`: its energy
is the energy lost by the source, and its virtuality is `-q²`. -/
def ofEmission {d : ℕ} (p p' : Lorentz.Vector d) : PhotonKin where
  energy := p.timeComponent - p'.timeComponent
  virtuality := -⟪p - p', p - p'⟫ₘ

@[simp]
theorem ofEmission_energy {d : ℕ} (p p' : Lorentz.Vector d) :
    (ofEmission p p').energy = p.timeComponent - p'.timeComponent :=
  (rfl)

@[simp]
theorem ofEmission_virtuality {d : ℕ} (p p' : Lorentz.Vector d) :
    (ofEmission p p').virtuality = -⟪p - p', p - p'⟫ₘ :=
  (rfl)

end PhotonKin

namespace ChargedSource

variable (s : ChargedSource)

/-- The virtuality of a photon carrying the energy fraction `x`, emitted by the source `s` at
scattering angle `θ`. -/
def photonVirtuality (x θ : ℝ) : ℝ :=
  emissionVirtuality s.mass s.energy ((1 - x) * s.energy) θ

theorem photonVirtuality_def (x θ : ℝ) :
    s.photonVirtuality x θ = emissionVirtuality s.mass s.energy ((1 - x) * s.energy) θ :=
  (rfl)

/-- The kinematic minimum of the virtuality of a photon carrying the energy fraction `x`, reached
at zero scattering angle. -/
def photonVirtualityMin (x : ℝ) : ℝ := s.photonVirtuality x 0

theorem photonVirtualityMin_def (x : ℝ) : s.photonVirtualityMin x = s.photonVirtuality x 0 :=
  (rfl)

/-- The kinematic minimum is a lower bound for the virtuality at every scattering angle in
`[0, π]`. -/
theorem photonVirtualityMin_le_photonVirtuality (x : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ ≤ π) :
    s.photonVirtualityMin x ≤ s.photonVirtuality x θ :=
  monotoneOn_emissionVirtuality _ _ _ ⟨le_rfl, pi_pos.le⟩ ⟨h0, hπ⟩ h0

variable {s}

/-- Under the hypotheses `0 < x < 1` and `1 ≤ (1 - x) γ` (the source stays on shell after the
emission), the energies of the source before and after lie above its mass and differ. -/
private theorem energy_bounds (hm : 0 < s.mass) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hγ : 1 ≤ (1 - x) * s.gamma) :
    |s.mass| ≤ s.energy ∧ |s.mass| ≤ (1 - x) * s.energy ∧ s.energy ≠ (1 - x) * s.energy := by
  have hg : 1 ≤ s.gamma := by nlinarith
  rw [abs_of_pos hm, energy]
  refine ⟨by nlinarith, by nlinarith, fun h => ?_⟩
  nlinarith [mul_pos (mul_pos hx (by linarith : (0 : ℝ) < s.gamma)) hm]

/-- **A massive source emits only at strictly positive virtuality.** -/
theorem photonVirtualityMin_pos (hm : 0 < s.mass) {x : ℝ} (hx : 0 < x) (hx1 : x < 1)
    (hγ : 1 ≤ (1 - x) * s.gamma) : 0 < s.photonVirtualityMin x := by
  obtain ⟨hE, hE', hne⟩ := energy_bounds hm hx hx1 hγ
  exact (emissionVirtuality_zero_pos_iff hE hE').2 ⟨hm.ne', hne⟩

/-- **The kinematic minimum strictly exceeds `m² x² / (1 - x)`**, the form in which it is usually
quoted for a high-energy source. -/
theorem sq_mass_mul_sq_div_lt_photonVirtualityMin (hm : 0 < s.mass) {x : ℝ} (hx : 0 < x)
    (hx1 : x < 1) (hγ : 1 ≤ (1 - x) * s.gamma) :
    s.mass ^ 2 * x ^ 2 / (1 - x) < s.photonVirtualityMin x := by
  obtain ⟨hE, hE', hne⟩ := energy_bounds hm hx hx1 hγ
  have hlt := div_lt_emissionVirtuality_zero hm.ne' hE hE' hne
  have hEpos : s.energy ≠ 0 := ((abs_pos.2 hm.ne').trans_le hE).ne'
  have h1x : 1 - x ≠ 0 := by linarith
  rw [photonVirtualityMin, photonVirtuality]
  convert hlt using 1
  field_simp
  ring

/-- The photon variables a source `s` can emit at scattering angle at most `θmax`: the photon
carries energy, the source keeps more energy than its mass (so that it leaves with a non-zero
momentum and the scattering angle is defined), and the virtuality lies between the kinematic
minimum and its value at `θmax`. -/
def photonRegion (s : ChargedSource) (θmax : ℝ) : Set PhotonKin :=
  {k | 0 < k.energy ∧ k.energy < s.energy - s.mass ∧
    s.photonVirtualityMin (k.energyFraction s) ≤ k.virtuality ∧
    k.virtuality ≤ s.photonVirtuality (k.energyFraction s) θmax}

/-- Membership in the photon region, unfolded. -/
theorem mem_photonRegion {θmax : ℝ} {k : PhotonKin} :
    k ∈ s.photonRegion θmax ↔ 0 < k.energy ∧ k.energy < s.energy - s.mass ∧
      s.photonVirtualityMin (k.energyFraction s) ≤ k.virtuality ∧
      k.virtuality ≤ s.photonVirtuality (k.energyFraction s) θmax :=
  (Iff.rfl)

/-- In terms of the photon energy `k`, the source energy after the emission is `E - k`. -/
private theorem photonVirtuality_energyFraction (k : PhotonKin) (hs : s.energy ≠ 0) (θ : ℝ) :
    s.photonVirtuality (k.energyFraction s) θ =
      emissionVirtuality s.mass s.energy (s.energy - k.energy) θ := by
  rw [photonVirtuality, k.one_sub_energyFraction_mul_energy hs]

/-- **Every photon emitted at scattering angle at most `θmax` lies in the photon region.** -/
theorem ofEmission_mem_photonRegion {d : ℕ} {p p' : Lorentz.Vector d}
    (hp : ⟪p, p⟫ₘ = s.mass ^ 2) (hp' : ⟪p', p'⟫ₘ = s.mass ^ 2)
    (hE : p.timeComponent = s.energy) (hE' : s.mass < p'.timeComponent)
    (hk : p'.timeComponent < p.timeComponent) {θmax : ℝ}
    (hθ : angle p.spatialPart p'.spatialPart ≤ θmax) (hπ : θmax ≤ π) :
    PhotonKin.ofEmission p p' ∈ s.photonRegion θmax := by
  have hk0 : 0 < (PhotonKin.ofEmission p p').energy := by simp; linarith
  have hk1 : (PhotonKin.ofEmission p p').energy < s.energy - s.mass := by simp; linarith
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
  refine mem_photonRegion.2 ⟨hk0, hk1, ?_⟩
  rw [photonVirtualityMin, photonVirtuality_energyFraction _ hs,
    photonVirtuality_energyFraction _ hs, PhotonKin.ofEmission_virtuality,
    neg_minkowskiProduct_sub_self_eq_emissionVirtuality hp hp', PhotonKin.ofEmission_energy, hE,
    sub_sub_cancel]
  have hmono := monotoneOn_emissionVirtuality s.mass s.energy p'.timeComponent
  exact ⟨hmono ⟨le_rfl, pi_pos.le⟩ ⟨angle_nonneg _ _, angle_le_pi _ _⟩ (angle_nonneg _ _),
    hmono ⟨angle_nonneg _ _, angle_le_pi _ _⟩ ⟨(angle_nonneg _ _).trans hθ, hπ⟩ hθ⟩

/-- **The photon region is exactly the set of photons emitted at scattering angle at most
`θmax`.** In at least two spatial dimensions, a photon lies in `s.photonRegion θmax` if and only
if it is the photon `p - p'` of an emission in which the source, on its mass shell, has energy
`s.energy` before and keeps more than its mass after, with scattering angle at most `θmax`. -/
theorem mem_photonRegion_iff_exists (hm : 0 ≤ s.mass) {d : ℕ} (hd : 2 ≤ d) {θmax : ℝ}
    (h0 : 0 ≤ θmax) (hπ : θmax ≤ π) {k : PhotonKin} :
    k ∈ s.photonRegion θmax ↔ ∃ p p' : Lorentz.Vector d, ⟪p, p⟫ₘ = s.mass ^ 2 ∧
      ⟪p', p'⟫ₘ = s.mass ^ 2 ∧ p.timeComponent = s.energy ∧ s.mass < p'.timeComponent ∧
      p'.timeComponent < p.timeComponent ∧ angle p.spatialPart p'.spatialPart ≤ θmax ∧
      PhotonKin.ofEmission p p' = k := by
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
    obtain ⟨p, p', hpm, hp'm, hpt, hp't, hang⟩ := Lorentz.Vector.exists_massShell_pair_angle_eq hd
      (m := m) (E := E) (E' := E') (by rw [abs_of_nonneg hm]; linarith)
      (by rw [abs_of_nonneg hm]; linarith) hθ0 (hθ.trans hπ)
    refine ⟨p, p', hpm, hp'm, hpt, hp't ▸ hE'm, by simp only [hpt, hp't, E']; linarith,
      hang.trans_le hθ, ?_⟩
    ext
    · simp [hpt, hp't, E']
    · rw [PhotonKin.ofEmission_virtuality,
        neg_minkowskiProduct_sub_self_eq_emissionVirtuality hpm hp'm, hpt, hp't, hang, hθk]
  · rintro ⟨p, p', hp, hp', hE, hE', hk, hθ, rfl⟩
    exact ofEmission_mem_photonRegion hp hp' hE hE' hk hθ hπ

/-- **A massive source never emits a real photon.** Every photon in the photon region of a
source of positive mass has strictly positive virtuality. -/
theorem not_isReal_of_mem_photonRegion (hm : 0 < s.mass) {θmax : ℝ} {k : PhotonKin}
    (hk : k ∈ s.photonRegion θmax) : ¬ k.IsReal := by
  obtain ⟨hk0, hk1, hmin, -⟩ := hk
  rw [photonVirtualityMin, photonVirtuality_energyFraction _ (by linarith)] at hmin
  have hpos : 0 < emissionVirtuality s.mass s.energy (s.energy - k.energy) 0 :=
    (emissionVirtuality_zero_pos_iff (by rw [abs_of_pos hm]; linarith)
      (by rw [abs_of_pos hm]; linarith)).2 ⟨hm.ne', by linarith⟩
  rw [PhotonKin.isReal_iff]
  linarith

end ChargedSource

end Photoproduction
end Scattering
end QFT
end EpsilonEridani
