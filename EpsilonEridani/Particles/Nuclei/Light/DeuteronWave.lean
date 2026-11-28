/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.MeasureTheory.HalfLine
public import EpsilonEridani.Mathematics.MeasureTheory.MemLp
public import Mathlib.MeasureTheory.Integral.ExpDecay

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
* `HasAsymptoticSStateNormalization ψ κ A` says that `uS r` behaves as `A * exp (-κ * r)` at large
  `r`, where `κ` is the binding momentum: `A` is the asymptotic s-state normalisation.

The d-state probability is not an observable. The asymptotic normalisations are properties of
the wave function outside the range of the force, and the quadrupole moment is a single
moment, so neither determines the weight of the d-wave inside that range:
`exists_eqOn_Ioi_quadrupoleMoment_eq_dStateProbability_ne` shows that for every `R > 0` and
every exterior `(vS, vD)` square integrable on `r > R` of total weight below one there are two
deuteron wave functions equal to it for `r > R`, with the quadrupole moment of that exterior
and different d-state probabilities.
`exists_hasAsymptoticSStateNormalization_quadrupoleMoment_eq_dStateProbability_ne` specialises
this to exponential tails `uS = uD = A * exp (-κ * r)`: for every binding momentum `κ > 0` and
every non-zero `A` there are two wave functions with asymptotic normalisation `A` and the same
positive quadrupole moment. The
two wave functions differ only for `r ≤ R`, where they are constant; `DeuteronWave` imposes
no regularity, and the statement is about the functionals, not about a particular potential.
The d-state probability is therefore meaningful only relative to a stated nucleon-nucleon
potential, whose ground state fixes the interior.

## Main definitions

* `DeuteronWave`: the pair of `r`-weighted radial amplitudes of the `³S₁` and `³D₁` channels.
* `DeuteronWave.ofHalfLine`: the deuteron wave function with given amplitudes on `r > 0`,
  extended by zero; its channel weights and quadrupole moment are the integrals of the given
  amplitudes (`dStateProbability_ofHalfLine` and its companions).
* `DeuteronWave.sStateProbability`, `DeuteronWave.dStateProbability`: the channel weights.
* `DeuteronWave.quadrupoleMoment`: the electric quadrupole moment.
* `DeuteronWave.HasAsymptoticSStateNormalization`: the asymptotic s-state normalisation.

## Main statements

* `DeuteronWave.ext_of_eqOn_Ioi`: a deuteron wave function is determined by its amplitudes on
  `r > 0`; `DeuteronWave.memLp_uS`, `DeuteronWave.memLp_uD`: the amplitudes are
  square integrable on all of `ℝ`.
* `DeuteronWave.sStateProbability_add_dStateProbability`, `DeuteronWave.dStateProbability_mem_Icc`.
* `DeuteronWave.dStateProbability_eq_zero_iff`: `P_D = 0` iff `uD = 0` almost everywhere.
* `DeuteronWave.quadrupoleMoment_eq_zero_of_dStateProbability_eq_zero`.
* `DeuteronWave.exists_eqOn_Ioi_quadrupoleMoment_eq_dStateProbability_ne` and
  `DeuteronWave.exists_hasAsymptoticSStateNormalization_quadrupoleMoment_eq_dStateProbability_ne`:
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
  memLp_uS_Ioi : MemLp uS 2 (volume.restrict (Ioi 0))
  /-- The d-wave amplitude is square integrable on the half-line. -/
  memLp_uD_Ioi : MemLp uD 2 (volume.restrict (Ioi 0))
  /-- The two channel weights add up to one. -/
  normalized : ∫ r in Ioi 0, (uS r ^ 2 + uD r ^ 2) = 1

namespace DeuteronWave

/-! ### Introduction and extensionality -/

/-- The s-wave amplitude is supported in the half-line `r > 0`. -/
theorem support_uS_subset (ψ : DeuteronWave) : Function.support ψ.uS ⊆ Ioi 0 :=
  Function.support_subset_iff'.2 fun r hr => ψ.uS_eq_zero_of_nonpos r (not_lt.1 hr)

/-- The d-wave amplitude is supported in the half-line `r > 0`. -/
theorem support_uD_subset (ψ : DeuteronWave) : Function.support ψ.uD ⊆ Ioi 0 :=
  Function.support_subset_iff'.2 fun r hr => ψ.uD_eq_zero_of_nonpos r (not_lt.1 hr)

/-- A deuteron wave function is determined by its amplitudes on the half-line `r > 0`. -/
theorem ext_of_eqOn_Ioi {ψ ψ' : DeuteronWave} (hS : EqOn ψ.uS ψ'.uS (Ioi 0))
    (hD : EqOn ψ.uD ψ'.uD (Ioi 0)) : ψ = ψ' := by
  ext1
  · rw [← indicator_eq_self.2 ψ.support_uS_subset, ← indicator_eq_self.2 ψ'.support_uS_subset,
      indicator_congr hS]
  · rw [← indicator_eq_self.2 ψ.support_uD_subset, ← indicator_eq_self.2 ψ'.support_uD_subset,
      indicator_congr hD]

/-- The s-wave amplitude is square integrable on all of `ℝ`, as it vanishes off the
half-line. -/
theorem memLp_uS (ψ : DeuteronWave) : MemLp ψ.uS 2 volume :=
  memLp_of_support_subset_of_restrict measurableSet_Ioi.nullMeasurableSet ψ.support_uS_subset
    ψ.memLp_uS_Ioi

/-- The d-wave amplitude is square integrable on all of `ℝ`, as it vanishes off the
half-line. -/
theorem memLp_uD (ψ : DeuteronWave) : MemLp ψ.uD 2 volume :=
  memLp_of_support_subset_of_restrict measurableSet_Ioi.nullMeasurableSet ψ.support_uD_subset
    ψ.memLp_uD_Ioi

/-- The deuteron wave function with amplitudes `vS`, `vD` on the half-line `r > 0`, extended by
zero to `r ≤ 0`. Only the values of `vS` and `vD` on the half-line enter. -/
def ofHalfLine (vS vD : ℝ → ℝ) (hS : MemLp vS 2 (volume.restrict (Ioi 0)))
    (hD : MemLp vD 2 (volume.restrict (Ioi 0)))
    (h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1) : DeuteronWave where
  uS := (Ioi 0).indicator vS
  uD := (Ioi 0).indicator vD
  uS_eq_zero_of_nonpos _ hr := indicator_of_notMem (notMem_Ioi.2 hr) _
  uD_eq_zero_of_nonpos _ hr := indicator_of_notMem (notMem_Ioi.2 hr) _
  memLp_uS_Ioi := hS.ae_eq (indicator_ae_eq_restrict measurableSet_Ioi.nullMeasurableSet).symm
  memLp_uD_Ioi := hD.ae_eq (indicator_ae_eq_restrict measurableSet_Ioi.nullMeasurableSet).symm
  normalized := by
    rw [← h]
    exact setIntegral_congr_fun measurableSet_Ioi fun r hr => by
      simp only [indicator_of_mem hr]

theorem ofHalfLine_uS (vS vD : ℝ → ℝ) (hS : MemLp vS 2 (volume.restrict (Ioi 0)))
    (hD : MemLp vD 2 (volume.restrict (Ioi 0)))
    (h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1) :
    (ofHalfLine vS vD hS hD h).uS = (Ioi 0).indicator vS := (rfl)

theorem ofHalfLine_uD (vS vD : ℝ → ℝ) (hS : MemLp vS 2 (volume.restrict (Ioi 0)))
    (hD : MemLp vD 2 (volume.restrict (Ioi 0)))
    (h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1) :
    (ofHalfLine vS vD hS hD h).uD = (Ioi 0).indicator vD := (rfl)

@[simp] theorem ofHalfLine_uS_of_pos {vS vD : ℝ → ℝ} {hS : MemLp vS 2 (volume.restrict (Ioi 0))}
    {hD : MemLp vD 2 (volume.restrict (Ioi 0))} {h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1}
    {r : ℝ} (hr : 0 < r) : (ofHalfLine vS vD hS hD h).uS r = vS r := by
  rw [ofHalfLine_uS, indicator_of_mem hr]

@[simp] theorem ofHalfLine_uD_of_pos {vS vD : ℝ → ℝ} {hS : MemLp vS 2 (volume.restrict (Ioi 0))}
    {hD : MemLp vD 2 (volume.restrict (Ioi 0))} {h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1}
    {r : ℝ} (hr : 0 < r) : (ofHalfLine vS vD hS hD h).uD r = vD r := by
  rw [ofHalfLine_uD, indicator_of_mem hr]

/-- Every deuteron wave function is the one built from its own amplitudes by `ofHalfLine`. -/
@[simp] theorem ofHalfLine_eta (ψ : DeuteronWave) :
    ofHalfLine ψ.uS ψ.uD ψ.memLp_uS_Ioi ψ.memLp_uD_Ioi ψ.normalized = ψ :=
  ext_of_eqOn_Ioi (fun _ hr => ofHalfLine_uS_of_pos hr) fun _ hr => ofHalfLine_uD_of_pos hr

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
  rw [sStateProbability_def, dStateProbability_def, ← integral_add ψ.memLp_uS_Ioi.integrable_sq
    ψ.memLp_uD_Ioi.integrable_sq, ψ.normalized]

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
    ψ.sStateProbability = 0 ↔ ψ.uS =ᵐ[volume.restrict (Ioi 0)] 0 :=
  integral_sq_eq_zero_iff ψ.memLp_uS_Ioi.integrable_sq

/-- The d-state probability vanishes exactly when the d-wave amplitude vanishes almost
everywhere on the half-line. -/
theorem dStateProbability_eq_zero_iff :
    ψ.dStateProbability = 0 ↔ ψ.uD =ᵐ[volume.restrict (Ioi 0)] 0 :=
  integral_sq_eq_zero_iff ψ.memLp_uD_Ioi.integrable_sq

/-! ### The quadrupole moment -/

/-- The electric quadrupole moment of the deuteron,
`Q = (1 / 20) ∫₀^∞ r ^ 2 uD r (√8 uS r - uD r) dr`.

The `√8 uS uD` term is the s-d interference and the `- uD ^ 2` term the pure d-wave
contribution; a pure s-wave is spherical and has no quadrupole moment. The integral is the
Bochner integral, which assigns `0` to a non-integrable integrand, so the value is the physical
quadrupole moment only for wave functions whose integrand `r ^ 2 * uD r * (√8 * uS r - uD r)`
is integrable on `Ioi 0`. -/
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
def HasAsymptoticSStateNormalization (κ A : ℝ) : Prop :=
  Tendsto (fun r => Real.exp (κ * r) * ψ.uS r) atTop (𝓝 A)

/-- The unfolding of `HasAsymptoticSStateNormalization`, whose body is not exposed outside this
module: this is how a downstream file proves or uses the predicate. -/
theorem hasAsymptoticSStateNormalization_iff {κ A : ℝ} :
    ψ.HasAsymptoticSStateNormalization κ A ↔
      Tendsto (fun r => Real.exp (κ * r) * ψ.uS r) atTop (𝓝 A) :=
  Iff.rfl

/-- The asymptotic normalisation at a given binding momentum is unique. -/
theorem HasAsymptoticSStateNormalization.unique {ψ : DeuteronWave} {κ A A' : ℝ}
    (h : ψ.HasAsymptoticSStateNormalization κ A) (h' : ψ.HasAsymptoticSStateNormalization κ A') :
    A = A' :=
  tendsto_nhds_unique h h'

/-- The asymptotic normalisation depends only on the s-wave amplitude at large `r`. -/
theorem HasAsymptoticSStateNormalization.congr' {ψ ψ' : DeuteronWave} {κ A : ℝ}
    (h : ψ.HasAsymptoticSStateNormalization κ A) (hψ : ψ.uS =ᶠ[atTop] ψ'.uS) :
    ψ'.HasAsymptoticSStateNormalization κ A :=
  Tendsto.congr' (hψ.mono fun r hr => by rw [hr]) h

/-! ### The functionals of a wave function built on the half-line -/

/-- An integral over the half-line of an expression in the amplitudes of `ofHalfLine vS vD`
is the same integral in `vS` and `vD`. -/
private theorem setIntegral_ofHalfLine {vS vD : ℝ → ℝ}
    {hS : MemLp vS 2 (volume.restrict (Ioi 0))} {hD : MemLp vD 2 (volume.restrict (Ioi 0))}
    {h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1} (F : ℝ → ℝ → ℝ → ℝ) :
    ∫ r in Ioi 0, F r ((ofHalfLine vS vD hS hD h).uS r) ((ofHalfLine vS vD hS hD h).uD r) =
      ∫ r in Ioi 0, F r (vS r) (vD r) :=
  setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => by
    simp only [ofHalfLine_uS_of_pos hr, ofHalfLine_uD_of_pos hr]

@[simp] theorem sStateProbability_ofHalfLine {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi 0))) (hD : MemLp vD 2 (volume.restrict (Ioi 0)))
    (h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1) :
    (ofHalfLine vS vD hS hD h).sStateProbability = ∫ r in Ioi 0, vS r ^ 2 := by
  rw [sStateProbability_def]
  exact setIntegral_ofHalfLine fun _ s _ => s ^ 2

@[simp] theorem dStateProbability_ofHalfLine {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi 0))) (hD : MemLp vD 2 (volume.restrict (Ioi 0)))
    (h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1) :
    (ofHalfLine vS vD hS hD h).dStateProbability = ∫ r in Ioi 0, vD r ^ 2 := by
  rw [dStateProbability_def]
  exact setIntegral_ofHalfLine fun _ _ d => d ^ 2

@[simp] theorem quadrupoleMoment_ofHalfLine {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi 0))) (hD : MemLp vD 2 (volume.restrict (Ioi 0)))
    (h : ∫ r in Ioi 0, (vS r ^ 2 + vD r ^ 2) = 1) :
    (ofHalfLine vS vD hS hD h).quadrupoleMoment =
      (1 / 20) * ∫ r in Ioi 0, r ^ 2 * vD r * (√8 * vS r - vD r) := by
  rw [quadrupoleMoment_def]
  congr 1
  exact setIntegral_ofHalfLine fun r s d => r ^ 2 * d * (√8 * s - d)

/-! ### The d-state probability is not an observable -/

/-- The deuteron wave function equal to `(aS, aD)` on `(0, R]` and to `(vS, vD)` on `(R, ∞)`,
for interior values making the total weight one. -/
private def glued {R : ℝ} (hR : 0 ≤ R) (aS aD : ℝ) {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi R))) (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (h : R * (aS ^ 2 + aD ^ 2) + ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) = 1) : DeuteronWave :=
  ofHalfLine ((Ioi R).piecewise vS fun _ => aS) ((Ioi R).piecewise vD fun _ => aD)
    (memLp_piecewise_Ioi_const hR aS hS) (memLp_piecewise_Ioi_const hR aD hD) (by
    rw [integral_add (memLp_piecewise_Ioi_const hR aS hS).integrable_sq
      (memLp_piecewise_Ioi_const hR aD hD).integrable_sq,
      setIntegral_piecewise_Ioi_const_sq hR aS hS.integrable_sq,
      setIntegral_piecewise_Ioi_const_sq hR aD hD.integrable_sq, sub_zero, ← h,
      integral_add hS.integrable_sq hD.integrable_sq]
    ring)

/-- A glued wave function equals its exterior on `r > R`. -/
private theorem eqOn_Ioi_glued {R : ℝ} (hR : 0 ≤ R) (aS aD : ℝ) {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi R))) (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (h : R * (aS ^ 2 + aD ^ 2) + ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) = 1) :
    EqOn (glued hR aS aD hS hD h).uS vS (Ioi R) ∧ EqOn (glued hR aS aD hS hD h).uD vD (Ioi R) :=
  ⟨fun r (hr : R < r) => by
      rw [glued, ofHalfLine_uS_of_pos (hR.trans_lt hr), piecewise_eq_of_mem _ _ _ hr],
    fun r (hr : R < r) => by
      rw [glued, ofHalfLine_uD_of_pos (hR.trans_lt hr), piecewise_eq_of_mem _ _ _ hr]⟩

private theorem dStateProbability_glued {R : ℝ} (hR : 0 ≤ R) (aS aD : ℝ) {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi R))) (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (h : R * (aS ^ 2 + aD ^ 2) + ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) = 1) :
    (glued hR aS aD hS hD h).dStateProbability = R * aD ^ 2 + ∫ r in Ioi R, vD r ^ 2 := by
  rw [glued, dStateProbability_ofHalfLine,
    setIntegral_piecewise_Ioi_const_sq hR aD hD.integrable_sq, sub_zero]

/-- A glued wave function whose interior values give a vanishing quadrupole integrand has the
quadrupole moment of its exterior. -/
private theorem quadrupoleMoment_glued {R : ℝ} (hR : 0 ≤ R) (aS aD : ℝ) {vS vD : ℝ → ℝ}
    (hS : MemLp vS 2 (volume.restrict (Ioi R))) (hD : MemLp vD 2 (volume.restrict (Ioi R)))
    (h : R * (aS ^ 2 + aD ^ 2) + ∫ r in Ioi R, (vS r ^ 2 + vD r ^ 2) = 1)
    (h0 : aD * (√8 * aS - aD) = 0) :
    (glued hR aS aD hS hD h).quadrupoleMoment =
      (1 / 20) * ∫ r in Ioi R, r ^ 2 * vD r * (√8 * vS r - vD r) := by
  -- Write both sides as integrals over `Ioi 0`, the exterior one through the indicator of
  -- `Ioi R`, so that they can be compared pointwise.
  rw [glued, quadrupoleMoment_ofHalfLine]
  conv_rhs => rw [← inter_eq_right.2 (Ioi_subset_Ioi hR),
    ← setIntegral_indicator measurableSet_Ioi]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rcases le_or_gt r R with hrR | hrR
  · simp only [piecewise_eq_of_notMem _ _ _ (notMem_Ioi.2 hrR),
      indicator_of_notMem (notMem_Ioi.2 hrR)]
    rw [mul_assoc, h0, mul_zero]
  · simp only [piecewise_eq_of_mem _ _ _ (mem_Ioi.2 hrR), indicator_of_mem (mem_Ioi.2 hrR)]

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
  obtain ⟨h₁S, h₁D⟩ := eqOn_Ioi_glued hR.le (3 * c) 0 hS hD h₁
  obtain ⟨h₂S, h₂D⟩ := eqOn_Ioi_glued hR.le c (√8 * c) hS hD h₂
  refine ⟨glued hR.le (3 * c) 0 hS hD h₁, glued hR.le c (√8 * c) hS hD h₂, h₁S, h₁D, h₂S, h₂D,
    quadrupoleMoment_glued hR.le (3 * c) 0 hS hD h₁ (by ring),
    quadrupoleMoment_glued hR.le c (√8 * c) hS hD h₂ (by ring), ?_⟩
  rw [dStateProbability_glued, dStateProbability_glued, Ne, add_left_inj, mul_pow, h8]
  nlinarith [mul_pos hR (pow_pos hcpos 2)]

/-- Two deuteron wave functions with the same prescribed non-zero asymptotic s-state
normalisation `A`, at any binding momentum `κ > 0`, the same positive quadrupole moment and
different d-state probabilities: the d-state probability is not fixed by the asymptotic
normalisation and the quadrupole moment. -/
theorem exists_hasAsymptoticSStateNormalization_quadrupoleMoment_eq_dStateProbability_ne {κ A : ℝ}
    (hκ : 0 < κ) (hA : A ≠ 0) :
    ∃ ψ₁ ψ₂ : DeuteronWave, ψ₁.HasAsymptoticSStateNormalization κ A ∧
      ψ₂.HasAsymptoticSStateNormalization κ A ∧ 0 < ψ₁.quadrupoleMoment ∧
      ψ₁.quadrupoleMoment = ψ₂.quadrupoleMoment ∧
      ψ₁.dStateProbability ≠ ψ₂.dStateProbability := by
  -- The exterior on `r > R` is `(A * exp (-κ r), A * exp (-κ r))`, of weight
  -- `A ^ 2 * exp (-2 κ R) / κ`, with `R` large enough that this is below one.
  set R := (A ^ 2 / κ + 1) / (2 * κ)
  have hR : 0 < R := by positivity
  have hexp : ∀ r, Real.exp (-κ * r) ^ 2 = Real.exp (-(2 * κ) * r) := fun r => by
    rw [sq, ← Real.exp_add]; ring_nf
  have hsq : ∀ r, (A * Real.exp (-κ * r)) ^ 2 = A ^ 2 * Real.exp (-(2 * κ) * r) := fun r => by
    rw [mul_pow, hexp]
  have hS : MemLp (fun r => A * Real.exp (-κ * r)) 2 (volume.restrict (Ioi R)) :=
    (memLp_two_iff_integrable_sq (by fun_prop)).2 <| by
      simpa only [hsq] using (exp_neg_integrableOn_Ioi R (by positivity : 0 < 2 * κ)).const_mul _
  have hlt : ∫ r in Ioi R, ((A * Real.exp (-κ * r)) ^ 2 + (A * Real.exp (-κ * r)) ^ 2)
      < 1 := by
    simp only [hsq, ← two_mul, integral_const_mul]
    rw [integral_exp_mul_Ioi (by linarith), neg_div_neg_eq, neg_mul, Real.exp_neg]
    have h2R : 2 * κ * R = A ^ 2 / κ + 1 := by
      simp only [R]; field_simp
    have hE : A ^ 2 / κ + 1 < Real.exp (2 * κ * R) := by
      linarith [Real.add_one_lt_exp (x := 2 * κ * R) (by positivity)]
    have hEpos := Real.exp_pos (2 * κ * R)
    rw [div_add_one hκ.ne', div_lt_iff₀ hκ] at hE
    field_simp
    nlinarith
  obtain ⟨ψ₁, ψ₂, h₁S, -, h₂S, -, hQ₁, hQ₂, hP⟩ :=
    exists_eqOn_Ioi_quadrupoleMoment_eq_dStateProbability_ne hR hS hS hlt
  have hA₁ : ψ₁.HasAsymptoticSStateNormalization κ A := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop R] with r hr
    simp only [h₁S hr]
    rw [mul_left_comm, ← Real.exp_add]
    simp
  have hψ : ψ₁.uS =ᶠ[atTop] ψ₂.uS := by
    filter_upwards [eventually_gt_atTop R] with r hr
    rw [h₁S hr, h₂S hr]
  -- The quadrupole moment of the exterior is `(A ^ 2 (√8 - 1) / 20) ∫_R^∞ r ^ 2 e^{-2κr} dr`.
  have h8 : 0 < √8 - 1 := by
    have : (1 : ℝ) < √8 := by rw [Real.lt_sqrt zero_le_one]; norm_num
    linarith
  have hpos : 0 < ψ₁.quadrupoleMoment := by
    rw [hQ₁, setIntegral_congr_fun measurableSet_Ioi fun r _ => (show
      r ^ 2 * (A * Real.exp (-κ * r)) * (√8 * (A * Real.exp (-κ * r)) - A * Real.exp (-κ * r))
        = A ^ 2 * (√8 - 1) * (r ^ 2 * Real.exp (-(2 * κ) * r)) by rw [← hexp]; ring),
      integral_const_mul]
    have := setIntegral_Ioi_pow_mul_exp_neg_pos 2 hR.le (by positivity : 0 < 2 * κ)
    have := pow_pos (abs_pos.2 hA) 2
    rw [sq_abs] at this
    positivity
  exact ⟨ψ₁, ψ₂, hA₁, hA₁.congr' hψ, hpos, hQ₁.trans hQ₂.symm, hP⟩

end DeuteronWave

end EpsilonEridani.Particles.Nuclei
