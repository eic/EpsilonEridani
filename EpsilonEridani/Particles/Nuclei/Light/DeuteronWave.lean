/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The deuteron radial wave function and the d-state probability

The deuteron is the spin-triplet, isospin-singlet bound state of a proton and a neutron with
total angular momentum one and positive parity. Its wave function has two partial waves, the
`³S₁` and `³D₁` channels, coupled by the tensor force. This file records the radial part of
that wave function and the functionals of it that the deuteron's structure is described by.

Radial amplitudes are the `r`-weighted ones: for a channel with radial function `R`, the
object carried is `u r = r * R r`, so that the probability carried by the channel is
`∫₀^∞ u r ^ 2 dr`, with no factor `r ^ 2`. A `DeuteronWave` is a pair `(uS, uD)` of such
amplitudes on the half-line `r > 0`, square integrable there, vanishing for `r ≤ 0` (which
includes the boundary condition `u 0 = 0` and pins the amplitudes off the half-line), and
normalised by `∫₀^∞ (uS r ^ 2 + uD r ^ 2) dr = 1`.

* The s-state and d-state probabilities `sStateProbability`, `dStateProbability` are the
  channel weights. They are non-negative, add up to one, and vanish exactly when the
  corresponding amplitude vanishes almost everywhere.
* The electric quadrupole moment is the functional
  `Q = (1 / 20) ∫₀^∞ r ^ 2 uD (√8 uS - uD) dr` (`quadrupoleMoment`), an area when `r` is a
  length. It vanishes for a pure s-wave, so a non-zero quadrupole
  moment forces a non-zero d-state probability
  (`dStateProbability_pos_of_quadrupoleMoment_ne_zero`).
* `HasAsymptoticNormalization ψ κ A` says that `uS r` behaves as `A * exp (-κ * r)` at large
  `r`, where `κ` is the binding momentum: `A` is the asymptotic s-state normalisation.

The d-state probability is not an observable. The asymptotic normalisations are properties of
the wave function outside the range of the force, and the quadrupole moment is a single
moment, so neither determines the weight of the d-wave inside that range:
`exists_eqOn_Ioi_quadrupoleMoment_eq_dStateProbability_ne` shows that for every exterior
`(vS, vD)` on `r > R` of total weight below one there are two deuteron wave functions equal
to it for `r > R`, with the quadrupole moment of that exterior and different d-state
probabilities. `exists_hasAsymptoticNormalization_quadrupoleMoment_eq_dStateProbability_ne`
specialises this to exponential tails `uS = uD = t * exp (-κ * r)`, giving two wave functions
with the same non-zero asymptotic normalisation and the same positive quadrupole moment. The
two wave functions differ only for `r ≤ R`, where they are constant; `DeuteronWave` imposes
no regularity, and the statement is about the functionals, not about a particular potential.
The d-state probability is therefore meaningful only relative to a stated nucleon-nucleon
potential, whose ground state fixes the interior.

## Main definitions

* `DeuteronWave`: the pair of `r`-weighted radial amplitudes of the `³S₁` and `³D₁` channels.
* `DeuteronWave.sStateProbability`, `DeuteronWave.dStateProbability`: the channel weights.
* `DeuteronWave.quadrupoleMoment`: the electric quadrupole moment.
* `DeuteronWave.HasAsymptoticNormalization`: the asymptotic s-state normalisation.

## Main statements

* `DeuteronWave.sStateProbability_add_dStateProbability`, `DeuteronWave.dStateProbability_mem_Icc`.
* `DeuteronWave.dStateProbability_eq_zero_iff`: `P_D = 0` iff `uD = 0` almost everywhere.
* `DeuteronWave.quadrupoleMoment_eq_zero_of_dStateProbability_eq_zero`.
* `DeuteronWave.exists_eqOn_Ioi_quadrupoleMoment_eq_dStateProbability_ne` and
  `DeuteronWave.exists_hasAsymptoticNormalization_quadrupoleMoment_eq_dStateProbability_ne`:
  the d-state probability is not determined by the exterior wave function and the quadrupole
  moment.

## References

* T. E. O. Ericson and W. Weise, *Pions and Nuclei*, Clarendon Press (1988).
* R. Machleidt, *High-precision, charge-dependent Bonn nucleon-nucleon potential*,
  Phys. Rev. C **63** (2001) 024001 (the quadrupole moment in terms of `u` and `w`).
* R. D. Amado, Phys. Rev. C **19** (1979) 1473 (the d-state probability is not an
  observable).
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology

namespace EpsilonEridani.Particles.Nuclei

/-- A deuteron wave function, as the pair of `r`-weighted radial amplitudes `uS r = r * R_S r`
and `uD r = r * R_D r` of its `³S₁` and `³D₁` channels.

The amplitudes are square integrable on the half-line `r > 0`, vanish for `r ≤ 0` (the
boundary condition `u 0 = 0`, extended so that no value off the half-line is free data), and
are normalised so that the two channel weights add up to one. -/
@[ext]
structure DeuteronWave where
  /-- The `r`-weighted radial amplitude of the `³S₁` channel. -/
  uS : ℝ → ℝ
  /-- The `r`-weighted radial amplitude of the `³D₁` channel. -/
  uD : ℝ → ℝ
  /-- The s-wave amplitude vanishes off the open half-line, in particular `uS 0 = 0`. -/
  uS_eq_zero_of_nonpos : ∀ r ≤ 0, uS r = 0
  /-- The d-wave amplitude vanishes off the open half-line, in particular `uD 0 = 0`. -/
  uD_eq_zero_of_nonpos : ∀ r ≤ 0, uD r = 0
  /-- The s-wave amplitude is square integrable on the half-line. -/
  memLp_uS : MemLp uS 2 (volume.restrict (Ioi 0))
  /-- The d-wave amplitude is square integrable on the half-line. -/
  memLp_uD : MemLp uD 2 (volume.restrict (Ioi 0))
  /-- The two channel weights add up to one. -/
  normalised : ∫ r in Ioi 0, (uS r ^ 2 + uD r ^ 2) = 1

namespace DeuteronWave

variable (ψ : DeuteronWave)

/-! ### The channel weights -/

/-- The s-state probability `P_S = ∫₀^∞ uS r ^ 2 dr`: the weight of the `³S₁` channel. -/
def sStateProbability : ℝ :=
  ∫ r in Ioi 0, ψ.uS r ^ 2

/-- The d-state probability `P_D = ∫₀^∞ uD r ^ 2 dr`: the weight of the `³D₁` channel. -/
def dStateProbability : ℝ :=
  ∫ r in Ioi 0, ψ.uD r ^ 2

theorem sStateProbability_def : ψ.sStateProbability = ∫ r in Ioi 0, ψ.uS r ^ 2 := (rfl)

theorem dStateProbability_def : ψ.dStateProbability = ∫ r in Ioi 0, ψ.uD r ^ 2 := (rfl)

/-- The two channel weights add up to one. -/
theorem sStateProbability_add_dStateProbability :
    ψ.sStateProbability + ψ.dStateProbability = 1 := by
  rw [sStateProbability_def, dStateProbability_def, ← integral_add ψ.memLp_uS.integrable_sq
    ψ.memLp_uD.integrable_sq, ψ.normalised]

theorem sStateProbability_nonneg : 0 ≤ ψ.sStateProbability :=
  integral_nonneg fun _ => sq_nonneg _

theorem dStateProbability_nonneg : 0 ≤ ψ.dStateProbability :=
  integral_nonneg fun _ => sq_nonneg _

theorem sStateProbability_le_one : ψ.sStateProbability ≤ 1 := by
  linarith [ψ.sStateProbability_add_dStateProbability, ψ.dStateProbability_nonneg]

theorem dStateProbability_le_one : ψ.dStateProbability ≤ 1 := by
  linarith [ψ.sStateProbability_add_dStateProbability, ψ.sStateProbability_nonneg]

/-- The d-state probability lies in the unit interval. -/
theorem dStateProbability_mem_Icc : ψ.dStateProbability ∈ Icc (0 : ℝ) 1 :=
  ⟨ψ.dStateProbability_nonneg, ψ.dStateProbability_le_one⟩

/-- The s-state probability lies in the unit interval. -/
theorem sStateProbability_mem_Icc : ψ.sStateProbability ∈ Icc (0 : ℝ) 1 :=
  ⟨ψ.sStateProbability_nonneg, ψ.sStateProbability_le_one⟩

/-- The s-state probability vanishes exactly when the s-wave amplitude vanishes almost
everywhere on the half-line. -/
theorem sStateProbability_eq_zero_iff :
    ψ.sStateProbability = 0 ↔ ψ.uS =ᵐ[volume.restrict (Ioi 0)] 0 := by
  rw [sStateProbability_def, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
    ψ.memLp_uS.integrable_sq]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with r hr <;> simpa using hr

/-- The d-state probability vanishes exactly when the d-wave amplitude vanishes almost
everywhere on the half-line. -/
theorem dStateProbability_eq_zero_iff :
    ψ.dStateProbability = 0 ↔ ψ.uD =ᵐ[volume.restrict (Ioi 0)] 0 := by
  rw [dStateProbability_def, integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _)
    ψ.memLp_uD.integrable_sq]
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> filter_upwards [h] with r hr <;> simpa using hr

/-! ### The quadrupole moment -/

/-- The electric quadrupole moment of the deuteron,
`Q = (1 / 20) ∫₀^∞ r ^ 2 uD r (√8 uS r - uD r) dr`.

The `√8 uS uD` term is the s-d interference and the `- uD ^ 2` term the pure d-wave
contribution; a pure s-wave is spherical and has no quadrupole moment. The integral is the
Bochner integral, which is `0` when the integrand is not integrable; a wave function with a
finite quadrupole moment has an integrable integrand. -/
def quadrupoleMoment : ℝ :=
  (1 / 20) * ∫ r in Ioi 0, r ^ 2 * ψ.uD r * (√8 * ψ.uS r - ψ.uD r)

theorem quadrupoleMoment_def :
    ψ.quadrupoleMoment = (1 / 20) * ∫ r in Ioi 0, r ^ 2 * ψ.uD r * (√8 * ψ.uS r - ψ.uD r) :=
  (rfl)

/-- A wave function with no d-state has no quadrupole moment. -/
theorem quadrupoleMoment_eq_zero_of_dStateProbability_eq_zero
    (h : ψ.dStateProbability = 0) : ψ.quadrupoleMoment = 0 := by
  rw [quadrupoleMoment_def, integral_eq_zero_of_ae, mul_zero]
  filter_upwards [ψ.dStateProbability_eq_zero_iff.1 h] with r hr
  simp [hr]

/-- A non-zero quadrupole moment forces a non-zero d-state probability: the deuteron's
quadrupole moment is the evidence for the tensor force. -/
theorem dStateProbability_pos_of_quadrupoleMoment_ne_zero (h : ψ.quadrupoleMoment ≠ 0) :
    0 < ψ.dStateProbability :=
  ψ.dStateProbability_nonneg.lt_of_ne fun h' =>
    h (ψ.quadrupoleMoment_eq_zero_of_dStateProbability_eq_zero h'.symm)

/-! ### The asymptotic normalisation -/

/-- `ψ` has asymptotic s-state normalisation `A` at binding momentum `κ`: the s-wave amplitude
behaves as `uS r ~ A * exp (-κ * r)` as `r → ∞`.

Outside the range of the nuclear force the s-wave amplitude is the decaying free solution, and
`κ` is fixed by the binding energy `B` through `κ ^ 2 = 2 m_red B`, with `m_red` the reduced
mass of the proton-neutron pair (in natural units). -/
def HasAsymptoticNormalization (κ A : ℝ) : Prop :=
  Tendsto (fun r => Real.exp (κ * r) * ψ.uS r) atTop (𝓝 A)

theorem hasAsymptoticNormalization_iff {κ A : ℝ} :
    ψ.HasAsymptoticNormalization κ A ↔
      Tendsto (fun r => Real.exp (κ * r) * ψ.uS r) atTop (𝓝 A) :=
  Iff.rfl

/-- The asymptotic normalisation at a given binding momentum is unique. -/
theorem HasAsymptoticNormalization.unique {ψ : DeuteronWave} {κ A A' : ℝ}
    (h : ψ.HasAsymptoticNormalization κ A) (h' : ψ.HasAsymptoticNormalization κ A') :
    A = A' :=
  tendsto_nhds_unique h h'

/-- The asymptotic normalisation depends only on the s-wave amplitude at large `r`. -/
theorem HasAsymptoticNormalization.congr {ψ ψ' : DeuteronWave} {κ A : ℝ}
    (h : ψ.HasAsymptoticNormalization κ A) (hψ : ψ.uS =ᶠ[atTop] ψ'.uS) :
    ψ'.HasAsymptoticNormalization κ A :=
  h.congr' (hψ.mono fun r hr => by rw [hr])

/-! ### The d-state probability is not an observable -/

/-- The amplitude equal to `a` on `(0, R]` and to `v` on `(R, ∞)`, and zero for `r ≤ 0`. -/
private def glue (R a : ℝ) (v : ℝ → ℝ) : ℝ → ℝ :=
  (Ioc 0 R).indicator (fun _ => a) + (Ioi R).indicator v

private theorem glue_of_mem_Ioc {R a r : ℝ} {v : ℝ → ℝ} (hr : r ∈ Ioc 0 R) :
    glue R a v r = a := by
  simp [glue, hr, notMem_Ioi.2 hr.2]

private theorem glue_of_lt {R a r : ℝ} {v : ℝ → ℝ} (hr : R < r) : glue R a v r = v r := by
  have : r ∉ Ioc 0 R := fun h => hr.not_ge h.2
  simp [glue, this, mem_Ioi.2 hr]

private theorem glue_of_nonpos {R a r : ℝ} {v : ℝ → ℝ} (hR : 0 ≤ R) (hr : r ≤ 0) :
    glue R a v r = 0 := by
  simp [glue, notMem_Ioc_of_le hr, notMem_Ioi.2 (hr.trans hR)]

private theorem memLp_glue {R : ℝ} (a : ℝ) {v : ℝ → ℝ} (hv : MemLp v 2 (volume.restrict (Ioi R))) :
    MemLp (glue R a v) 2 (volume.restrict (Ioi 0)) :=
  ((memLp_indicator_const 2 measurableSet_Ioc.nullMeasurableSet a
    (Or.inr measure_Ioc_lt_top.ne)).add
    ((memLp_indicator_iff_restrict measurableSet_Ioi.nullMeasurableSet).2 hv)).restrict _

private theorem integral_glue_sq {R : ℝ} (hR : 0 ≤ R) (a : ℝ) {v : ℝ → ℝ}
    (hv : MemLp v 2 (volume.restrict (Ioi R))) :
    ∫ r in Ioi 0, glue R a v r ^ 2 = R * a ^ 2 + ∫ r in Ioi R, v r ^ 2 := by
  have hIoc : EqOn (fun r => glue R a v r ^ 2) (fun _ => a ^ 2) (Ioc 0 R) :=
    fun r hr => by simp only [glue_of_mem_Ioc hr]
  have hIoi : EqOn (fun r => glue R a v r ^ 2) (fun r => v r ^ 2) (Ioi R) :=
    fun r hr => by simp only [glue_of_lt (mem_Ioi.1 hr)]
  rw [← Ioc_union_Ioi_eq_Ioi hR, setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    ((integrableOn_const measure_Ioc_lt_top.ne).congr_fun hIoc.symm measurableSet_Ioc)
    (IntegrableOn.congr_fun hv.integrable_sq hIoi.symm measurableSet_Ioi),
    setIntegral_congr_fun measurableSet_Ioc hIoc, setIntegral_congr_fun measurableSet_Ioi hIoi,
    setIntegral_const, Real.volume_real_Ioc_of_le hR, sub_zero, smul_eq_mul]

/-- The deuteron wave function equal to `(aS, aD)` on `(0, R]` and to `(vS, vD)` on `(R, ∞)`,
for interior values making the total weight one. -/
private def glued {R : ℝ} (hR : 0 ≤ R) (aS aD : ℝ) {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi R))) (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (h : R * (aS ^ 2 + aD ^ 2) + ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) = 1) : DeuteronWave where
  uS := glue R aS vS
  uD := glue R aD vD
  uS_eq_zero_of_nonpos _ hr := glue_of_nonpos hR hr
  uD_eq_zero_of_nonpos _ hr := glue_of_nonpos hR hr
  memLp_uS := memLp_glue aS hS
  memLp_uD := memLp_glue aD hD
  normalised := by
    rw [integral_add (memLp_glue aS hS).integrable_sq (memLp_glue aD hD).integrable_sq,
      integral_glue_sq hR aS hS, integral_glue_sq hR aD hD, ← h,
      integral_add hS.integrable_sq hD.integrable_sq]
    ring

private theorem dStateProbability_glued {R : ℝ} (hR : 0 ≤ R) (aS aD : ℝ) {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi R))) (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (h : R * (aS ^ 2 + aD ^ 2) + ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) = 1) :
    (glued hR aS aD hS hD h).dStateProbability = R * aD ^ 2 + ∫ r in Ioi R, vD r ^ 2 :=
  integral_glue_sq hR aD hD

/-- A glued wave function whose interior values give a vanishing quadrupole integrand has the
quadrupole moment of its exterior. -/
private theorem quadrupoleMoment_glued {R : ℝ} (hR : 0 ≤ R) (aS aD : ℝ) {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi R))) (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (h : R * (aS ^ 2 + aD ^ 2) + ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) = 1)
    (h0 : aD * (√8 * aS - aD) = 0) :
    (glued hR aS aD hS hD h).quadrupoleMoment =
      (1 / 20) * ∫ r in Ioi R, r ^ 2 * vD r * (√8 * vS r - vD r) := by
  rw [quadrupoleMoment_def, ← inter_eq_right.2 (Ioi_subset_Ioi hR),
    ← setIntegral_indicator measurableSet_Ioi]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_
  simp only [glued]
  rcases le_or_gt r R with hrR | hrR
  · rw [glue_of_mem_Ioc ⟨hr, hrR⟩, glue_of_mem_Ioc ⟨hr, hrR⟩, mul_assoc, h0, mul_zero,
      indicator_of_notMem (notMem_Ioi.2 hrR)]
  · rw [glue_of_lt hrR, glue_of_lt hrR, indicator_of_mem (mem_Ioi.2 hrR)]

/-- **The d-state probability is not an observable.** Fix an exterior `(vS, vD)` on `r > R`,
square integrable there with total weight below one. There are two deuteron wave functions
that both equal `(vS, vD)` for `r > R`, so that they share every asymptotic property (the
asymptotic s- and d-state normalisations and their ratio), have the same quadrupole moment,
namely the one `(1 / 20) ∫_R^∞ r ^ 2 vD (√8 vS - vD) dr` of the exterior, and have different
d-state probabilities. -/
theorem exists_eqOn_Ioi_quadrupoleMoment_eq_dStateProbability_ne {R : ℝ} (hR : 0 < R)
    {vS vD : ℝ → ℝ} (hS : MemLp vS 2 (volume.restrict (Ioi R)))
    (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (hlt : ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) < 1) :
    ∃ ψ₁ ψ₂ : DeuteronWave, EqOn ψ₁.uS vS (Ioi R) ∧ EqOn ψ₁.uD vD (Ioi R) ∧
      EqOn ψ₂.uS vS (Ioi R) ∧ EqOn ψ₂.uD vD (Ioi R) ∧
      ψ₁.quadrupoleMoment = (1 / 20) * ∫ r in Ioi R, r ^ 2 * vD r * (√8 * vS r - vD r) ∧
      ψ₂.quadrupoleMoment = (1 / 20) * ∫ r in Ioi R, r ^ 2 * vD r * (√8 * vS r - vD r) ∧
      ψ₁.dStateProbability ≠ ψ₂.dStateProbability := by
  set E := ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2)
  -- The interiors are `(3c, 0)` and `(c, √8 c)` on `(0, R]`, both of weight `9 R c ^ 2`, and
  -- both with vanishing quadrupole integrand there.
  set c := √((1 - E) / (9 * R))
  have hc : c ^ 2 = (1 - E) / (9 * R) := Real.sq_sqrt (div_nonneg (by linarith) (by positivity))
  have hcpos : 0 < c := Real.sqrt_pos.2 (div_pos (by linarith) (by positivity))
  have h8 : √8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have h₁ : R * ((3 * c) ^ 2 + 0 ^ 2) + E = 1 := by
    rw [mul_pow, hc]; field_simp; ring
  have h₂ : R * (c ^ 2 + (√8 * c) ^ 2) + E = 1 := by
    rw [mul_pow, h8, hc]; field_simp; ring
  refine ⟨glued hR.le _ _ hS hD h₁, glued hR.le _ _ hS hD h₂, fun r hr => glue_of_lt hr,
    fun r hr => glue_of_lt hr, fun r hr => glue_of_lt hr, fun r hr => glue_of_lt hr,
    quadrupoleMoment_glued _ _ _ _ _ _ (by ring), quadrupoleMoment_glued _ _ _ _ _ _ (by ring),
    ?_⟩
  rw [dStateProbability_glued, dStateProbability_glued, Ne, add_left_inj, mul_pow, h8]
  nlinarith [mul_pos hR (pow_pos hcpos 2)]

/-- Two deuteron wave functions with the same non-zero asymptotic s-state normalisation, at any
binding momentum `κ > 0`, the same positive quadrupole moment and different d-state
probabilities: the d-state probability is not fixed by the asymptotic normalisation and the
quadrupole moment. -/
theorem exists_hasAsymptoticNormalization_quadrupoleMoment_eq_dStateProbability_ne {κ : ℝ}
    (hκ : 0 < κ) :
    ∃ A ≠ 0, ∃ ψ₁ ψ₂ : DeuteronWave, ψ₁.HasAsymptoticNormalization κ A ∧
      ψ₂.HasAsymptoticNormalization κ A ∧ 0 < ψ₁.quadrupoleMoment ∧
      ψ₁.quadrupoleMoment = ψ₂.quadrupoleMoment ∧
      ψ₁.dStateProbability ≠ ψ₂.dStateProbability := by
  -- The exterior on `r > 1` is `(t * exp (-κ r), t * exp (-κ r))`, with `t` small enough that
  -- its weight is below one.
  set I := ∫ r in Ioi (1 : ℝ), Real.exp (-(2 * κ) * r)
  have hI : 0 ≤ I := integral_nonneg fun _ => (Real.exp_pos _).le
  set t := (√(2 * I + 1))⁻¹
  have htpos : 0 < t := inv_pos.2 (Real.sqrt_pos.2 (by linarith))
  have ht : t ^ 2 = (2 * I + 1)⁻¹ := by rw [inv_pow, Real.sq_sqrt (by linarith)]
  have hexp : ∀ r, Real.exp (-κ * r) ^ 2 = Real.exp (-(2 * κ) * r) := fun r => by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsq : ∀ r, (t * Real.exp (-κ * r)) ^ 2 = t ^ 2 * Real.exp (-(2 * κ) * r) := fun r => by
    rw [mul_pow, hexp]
  have hS : MemLp (fun r => t * Real.exp (-κ * r)) 2 (volume.restrict (Ioi 1)) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 <| by
      simpa only [hsq] using (exp_neg_integrableOn_Ioi 1 (by positivity : 0 < 2 * κ)).const_mul _
  have hlt : ∫ r in Ioi (1 : ℝ), ((t * Real.exp (-κ * r)) ^ 2 + (t * Real.exp (-κ * r)) ^ 2)
      < 1 := by
    simp only [hsq, ← two_mul, integral_const_mul, ht]
    rw [← mul_assoc, mul_comm 2, mul_assoc, inv_mul_eq_div, div_lt_one (by linarith)]
    linarith
  obtain ⟨ψ₁, ψ₂, h₁S, -, h₂S, -, hQ₁, hQ₂, hP⟩ :=
    exists_eqOn_Ioi_quadrupoleMoment_eq_dStateProbability_ne one_pos hS hS hlt
  have hA : ψ₁.HasAsymptoticNormalization κ t := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with r hr
    simp only [h₁S hr]
    rw [mul_left_comm, ← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero, mul_one]
  have hψ : ψ₁.uS =ᶠ[atTop] ψ₂.uS := by
    filter_upwards [eventually_gt_atTop 1] with r hr
    rw [h₁S hr, h₂S hr]
  -- The quadrupole moment of the exterior is `(t ^ 2 (√8 - 1) / 20) ∫_1^∞ r ^ 2 e^{-2κr} dr`.
  have h8 : 0 < √8 - 1 := by
    have : (1 : ℝ) < √8 := by rw [Real.lt_sqrt zero_le_one]; norm_num
    linarith
  have hint : IntegrableOn (fun r : ℝ => r ^ 2 * Real.exp (-(2 * κ) * r)) (Ioi 1) :=
    ((integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (by norm_num) one_pos
      (by positivity : 0 < 2 * κ)).mono_set (Ioi_subset_Ioi zero_le_one)).congr_fun
      (fun r _ => by simp [Real.rpow_one]) measurableSet_Ioi
  have hpos : 0 < ψ₁.quadrupoleMoment := by
    rw [hQ₁, setIntegral_congr_fun measurableSet_Ioi fun r _ => (show
      r ^ 2 * (t * Real.exp (-κ * r)) * (√8 * (t * Real.exp (-κ * r)) - t * Real.exp (-κ * r))
        = t ^ 2 * (√8 - 1) * (r ^ 2 * Real.exp (-(2 * κ) * r)) by rw [← hexp]; ring)]
    refine mul_pos (by norm_num) ((setIntegral_pos_iff_support_of_nonneg_ae ?_
      (hint.const_mul _)).2 ?_)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r _
      positivity
    · refine lt_of_lt_of_le (by simp [Real.volume_Ioi]) (measure_mono (s := Ioi 1)
        fun r (hr : r ∈ Ioi 1) => ⟨(mul_pos (mul_pos (pow_pos htpos 2) h8)
          (mul_pos (pow_pos (one_pos.trans hr) 2) (Real.exp_pos _))).ne', hr⟩)
  exact ⟨t, htpos.ne', ψ₁, ψ₂, hA, hA.congr hψ, hpos,
    hQ₁.trans hQ₂.symm, hP⟩

end DeuteronWave

end EpsilonEridani.Particles.Nuclei
