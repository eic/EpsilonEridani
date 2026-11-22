/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.Flavor
public import EpsilonEridani.QFT.Scattering.DIS.Polarized.SumRules

/-!
# The axial charges and the first moment of `g₁` in the charge basis

The quark helicity charges `Δu(Q²)`, `Δd(Q²)`, `Δs(Q²)` of a nucleon are the first moments
`Δq(Q²) = ∫₀¹ dx (Δq(x, Q²) + Δqbar(x, Q²))` of its light-quark helicity densities, the forward
matrix elements of the flavour-diagonal axial currents `qbar γ^μ γ₅ q`. The same information is
carried by the three axial charges of flavour `SU(3)`, the matrix elements of the isovector, octet
and singlet axial currents:

```text
a₃ = Δu − Δd,      a₈ = Δu + Δd − 2Δs,      a₀ = Δu + Δd + Δs.
```

`a₃` is the isovector charge usually written `g_A`, and `a₀` is the quark spin content usually
written `ΔΣ`. This module makes the two parametrisations interchangeable by proved identities
rather than by numerical substitution, and restates the existing Bjorken and Ellis–Jaffe sum rules
of `EpsilonEridani.QFT.Scattering.DIS.Polarized.SumRules` in the charge basis.

`HelicityCharges` carries the quark helicity charges `Δu`, `Δd`, `Δs` as functions of `Q²` and
nothing else; `HelicityCharges.delta` reads them as a function on `LightFlavor`, and the axial
charges `HelicityCharges.a0`, `HelicityCharges.a3`, `HelicityCharges.a8` are derived from them.
The change of basis is invertible: `HelicityCharges.ofAxialCharges` builds the flavour charges
from prescribed axial charges (`HelicityCharges.a0_ofAxialCharges`, …,
`HelicityCharges.ofAxialCharges_a0_a3_a8`), so either triple may be supplied as data, and two charge
records agree exactly when their axial charges do (`HelicityCharges.ext_a0_a3_a8_iff`).

`HelicityCharges.partonFirstMomentG1` is the leading-twist parton-model value `½ Σ_q e_q² Δq` of the
first moment of `g₁`, before the radiative correction. It is a function of the charges, distinct
from the first moment `firstMomentG1` of a structure function; the two are related only through
the decomposition hypothesis `Γ₁ = (½ Σ_q e_q² Δq) (1 + Δ)`.

Two operations act on the flavour charges.

* `HelicityCharges.isospinConj` exchanges `Δu` and `Δd`, the relabelling of flavours by the
  isospin involution `Equiv.swap u d` (`HelicityCharges.delta_isospinConj`). Under isospin
  symmetry the neutron's charges are the proton's, conjugated; the conjugation reverses `a₃` and
  fixes `a₈` and `a₀`.
* `HelicityCharges.addUniform` adds a common function `s` to every flavour, the form of a
  flavour-universal contribution such as the gluon's. It shifts `a₀` by `3s`, fixes `a₃` and
  `a₈`, and shifts the parton-model first moment by `s / 3`
  (`HelicityCharges.partonFirstMomentG1_addUniform`); these shifts are exactly the changes invisible
  to `a₃` and `a₈` (`HelicityCharges.a3_eq_and_a8_eq_iff_exists_eq_addUniform`). So the non-singlet
  charges, and in particular the isovector combination that the Bjorken sum rule measures, receive
  no flavour-universal contribution.

## Main statements

* `HelicityCharges.partonFirstMomentG1_eq_axialCharges`: the change of basis for the leading-twist
  first moment, `½ ((4/9) Δu + (1/9) Δd + (1/9) Δs) = (1/12) a₃ + (1/36) a₈ + (1/9) a₀`.
* `HelicityCharges.partonFirstMomentG1_isospinConj`,
  `HelicityCharges.partonFirstMomentG1_sub_partonFirstMomentG1_isospinConj`: at charge level, the
  isospin-conjugate value `−(1/12) a₃ + (1/36) a₈ + (1/9) a₀` and the isovector difference
  `Γ₁(a) − Γ₁(a.isospinConj) = (1/6) a₃`.
* `HelicityCharges.deltaS_eq_zero_iff_a0_eq_a8`: a vanishing strange polarisation is exactly
  `a₀ = a₈`, the content of the Ellis–Jaffe hypothesis in the charge basis.
* `HelicityCharges.partonFirstMomentG1_eq_ellisJaffe_add_deltaS`: the parton-model first moment is
  the Ellis–Jaffe value `(1/12) a₃ + (5/36) a₈` plus `Δs / 3`;
  `firstMomentG1_eq_ellisJaffe_add_deltaS` is the same split of a measured `Γ₁ᵖ` satisfying the
  leading-twist decomposition.
* `ellisJaffeSumRule_iff`: the existing `EllisJaffeSumRule` is the leading-twist decomposition
  together with `a₀ = a₈`; `firstMomentG1_eq_of_ellisJaffeSumRule` is its prediction
  `Γ₁ᵖ = ((1/12) a₃ + (5/36) a₈) (1 + Δ)`.
* `deltaS_ne_zero_of_firstMomentG1_ne` and `deltaS_neg_of_firstMomentG1_lt`: given the
  leading-twist decomposition at `Q²`, a measured `Γ₁ᵖ` that misses the Ellis–Jaffe value forces
  `Δs ≠ 0`, and one below it (with `1 + Δ > 0`) forces `Δs < 0`. The derivation is sound; the
  hypothesis is what fails.
* `a0_eq_of_firstMomentG1`: given the decomposition at `Q²` and `1 + Δ ≠ 0`, `a₀` is determined by
  `Γ₁ᵖ`, `a₃` and `a₈`, which is what makes the quark spin content a measured rather than a
  predicted number.
* `firstMomentG1_sub_firstMomentG1_eq`: the measured isovector difference
  `Γ₁ᵖ − Γ₁ⁿ = (1/6) a₃ (1 + Δ)`, given the proton decomposition and its isospin conjugate for the
  neutron.
* `bjorkenSumRule_iff`: given those two decompositions and `1 + Δ ≠ 0`, the existing
  `BjorkenSumRule` holds exactly when `a₃ = |g_A/g_V|` at every scale.

## References

* J. D. Bjorken, *Applications of the chiral U(6) ⊗ U(6) algebra of current densities*,
  Phys. Rev. **148** (1966) 1467.
* J. Ellis and R. L. Jaffe, *Sum rule for deep-inelastic electroproduction from polarized
  protons*, Phys. Rev. D **9** (1974) 1444.
* M. Anselmino, A. Efremov and E. Leader, *The theory and phenomenology of polarized deep
  inelastic scattering*, Phys. Rept. **261** (1995) 1, §7.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

/-- The light-quark helicity charges of a nucleon as functions of the scale `Q²`:
`Δq(Q²) = ∫₀¹ dx (Δq(x, Q²) + Δqbar(x, Q²))` for `q = u, d, s`, the forward matrix elements of the
flavour-diagonal axial currents. They are the data; the `SU(3)` axial charges `a₀`, `a₃`, `a₈`
are derived from them by `HelicityCharges.a0`, `HelicityCharges.a3` and `HelicityCharges.a8`, and
`HelicityCharges.ofAxialCharges` goes the other way. No numerical value is ever substituted. -/
@[ext]
structure HelicityCharges where
  /-- The up-quark helicity charge `Δu(Q²)`. -/
  deltaU : ℝ → ℝ
  /-- The down-quark helicity charge `Δd(Q²)`. -/
  deltaD : ℝ → ℝ
  /-- The strange-quark helicity charge `Δs(Q²)`. -/
  deltaS : ℝ → ℝ

namespace HelicityCharges

variable (a b : HelicityCharges)

open Particles.Parton

/-- The helicity charges as a function of the light flavour, `Δ_f` for `f = u, d, s`. -/
def delta : LightFlavor → ℝ → ℝ
  | .u => a.deltaU
  | .d => a.deltaD
  | .s => a.deltaS

@[simp]
theorem delta_u : a.delta .u = a.deltaU := (rfl)

@[simp]
theorem delta_d : a.delta .d = a.deltaD := (rfl)

@[simp]
theorem delta_s : a.delta .s = a.deltaS := (rfl)

/-! ### The axial charges -/

/-- The flavour-singlet axial charge `a₀ = Δu + Δd + Δs`, the quark spin content `ΔΣ`. -/
def a0 : ℝ → ℝ := fun Q2 => a.deltaU Q2 + a.deltaD Q2 + a.deltaS Q2

/-- The isovector axial charge `a₃ = Δu − Δd`, usually written `g_A`. -/
def a3 : ℝ → ℝ := fun Q2 => a.deltaU Q2 - a.deltaD Q2

/-- The octet axial charge `a₈ = Δu + Δd − 2Δs`. -/
def a8 : ℝ → ℝ := fun Q2 => a.deltaU Q2 + a.deltaD Q2 - 2 * a.deltaS Q2

theorem a0_apply (Q2 : ℝ) : a.a0 Q2 = a.deltaU Q2 + a.deltaD Q2 + a.deltaS Q2 := (rfl)

theorem a3_apply (Q2 : ℝ) : a.a3 Q2 = a.deltaU Q2 - a.deltaD Q2 := (rfl)

theorem a8_apply (Q2 : ℝ) : a.a8 Q2 = a.deltaU Q2 + a.deltaD Q2 - 2 * a.deltaS Q2 := (rfl)

/-- The up-quark charge in the charge basis, `Δu = a₀/3 + a₃/2 + a₈/6`. -/
theorem deltaU_eq (Q2 : ℝ) : a.deltaU Q2 = a.a0 Q2 / 3 + a.a3 Q2 / 2 + a.a8 Q2 / 6 := by
  rw [a0_apply, a3_apply, a8_apply]
  ring

/-- The down-quark charge in the charge basis, `Δd = a₀/3 − a₃/2 + a₈/6`. -/
theorem deltaD_eq (Q2 : ℝ) : a.deltaD Q2 = a.a0 Q2 / 3 - a.a3 Q2 / 2 + a.a8 Q2 / 6 := by
  rw [a0_apply, a3_apply, a8_apply]
  ring

/-- The strange-quark charge in the charge basis, `Δs = (a₀ − a₈)/3`. -/
theorem deltaS_eq (Q2 : ℝ) : a.deltaS Q2 = (a.a0 Q2 - a.a8 Q2) / 3 := by
  rw [a0_apply, a8_apply]
  ring

/-- **The Ellis–Jaffe hypothesis in the charge basis.** A vanishing strange polarisation is
exactly the coincidence of the singlet and octet charges. -/
theorem deltaS_eq_zero_iff_a0_eq_a8 (Q2 : ℝ) : a.deltaS Q2 = 0 ↔ a.a0 Q2 = a.a8 Q2 := by
  rw [deltaS_eq]
  constructor <;> intro h <;> linarith

/-! ### Prescribing the axial charges -/

/-- The flavour charges with prescribed axial charges `a₀`, `a₃`, `a₈`: the inverse of the change
of basis, `Δu = a₀/3 + a₃/2 + a₈/6`, `Δd = a₀/3 − a₃/2 + a₈/6`, `Δs = (a₀ − a₈)/3`. -/
def ofAxialCharges (a0 a3 a8 : ℝ → ℝ) : HelicityCharges where
  deltaU Q2 := a0 Q2 / 3 + a3 Q2 / 2 + a8 Q2 / 6
  deltaD Q2 := a0 Q2 / 3 - a3 Q2 / 2 + a8 Q2 / 6
  deltaS Q2 := (a0 Q2 - a8 Q2) / 3

@[simp]
theorem deltaU_ofAxialCharges (a0 a3 a8 : ℝ → ℝ) (Q2 : ℝ) :
    (ofAxialCharges a0 a3 a8).deltaU Q2 = a0 Q2 / 3 + a3 Q2 / 2 + a8 Q2 / 6 := (rfl)

@[simp]
theorem deltaD_ofAxialCharges (a0 a3 a8 : ℝ → ℝ) (Q2 : ℝ) :
    (ofAxialCharges a0 a3 a8).deltaD Q2 = a0 Q2 / 3 - a3 Q2 / 2 + a8 Q2 / 6 := (rfl)

@[simp]
theorem deltaS_ofAxialCharges (a0 a3 a8 : ℝ → ℝ) (Q2 : ℝ) :
    (ofAxialCharges a0 a3 a8).deltaS Q2 = (a0 Q2 - a8 Q2) / 3 := (rfl)

@[simp]
theorem a0_ofAxialCharges (a0 a3 a8 : ℝ → ℝ) : (ofAxialCharges a0 a3 a8).a0 = a0 := by
  funext Q2
  rw [a0_apply, deltaU_ofAxialCharges, deltaD_ofAxialCharges, deltaS_ofAxialCharges]
  ring

@[simp]
theorem a3_ofAxialCharges (a0 a3 a8 : ℝ → ℝ) : (ofAxialCharges a0 a3 a8).a3 = a3 := by
  funext Q2
  rw [a3_apply, deltaU_ofAxialCharges, deltaD_ofAxialCharges]
  ring

@[simp]
theorem a8_ofAxialCharges (a0 a3 a8 : ℝ → ℝ) : (ofAxialCharges a0 a3 a8).a8 = a8 := by
  funext Q2
  rw [a8_apply, deltaU_ofAxialCharges, deltaD_ofAxialCharges, deltaS_ofAxialCharges]
  ring

/-- Rebuilding the flavour charges from their own axial charges returns the original record:
`ofAxialCharges` is a left inverse of `(a0, a3, a8)`. -/
@[simp]
theorem ofAxialCharges_a0_a3_a8 : ofAxialCharges a.a0 a.a3 a.a8 = a := by
  ext Q2
  · exact (a.deltaU_eq Q2).symm
  · exact (a.deltaD_eq Q2).symm
  · exact (a.deltaS_eq Q2).symm

/-- Two charge records with the same axial charges are equal. -/
theorem ext_a0_a3_a8 (h0 : a.a0 = b.a0) (h3 : a.a3 = b.a3) (h8 : a.a8 = b.a8) : a = b := by
  rw [← ofAxialCharges_a0_a3_a8 a, ← ofAxialCharges_a0_a3_a8 b, h0, h3, h8]

theorem ext_a0_a3_a8_iff : a = b ↔ a.a0 = b.a0 ∧ a.a3 = b.a3 ∧ a.a8 = b.a8 :=
  ⟨fun h => h ▸ ⟨rfl, rfl, rfl⟩, fun ⟨h0, h3, h8⟩ => ext_a0_a3_a8 a b h0 h3 h8⟩

/-! ### Isospin conjugation -/

/-- The isospin-conjugate charges, with `Δu` and `Δd` exchanged and `Δs` unchanged. Under isospin
symmetry these are the neutron's charges when `a` are the proton's. -/
def isospinConj : HelicityCharges where
  deltaU := a.deltaD
  deltaD := a.deltaU
  deltaS := a.deltaS

@[simp]
theorem deltaU_isospinConj : a.isospinConj.deltaU = a.deltaD := (rfl)

@[simp]
theorem deltaD_isospinConj : a.isospinConj.deltaD = a.deltaU := (rfl)

@[simp]
theorem deltaS_isospinConj : a.isospinConj.deltaS = a.deltaS := (rfl)

/-- Isospin conjugation is the relabelling of flavours by the isospin involution `swap u d`. -/
theorem delta_isospinConj (f : LightFlavor) :
    a.isospinConj.delta f = a.delta (Equiv.swap .u .d f) := by
  cases f
  · rw [Equiv.swap_apply_left, delta_u, delta_d, deltaU_isospinConj]
  · rw [Equiv.swap_apply_right, delta_u, delta_d, deltaD_isospinConj]
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), delta_s, delta_s, deltaS_isospinConj]

@[simp]
theorem isospinConj_isospinConj : a.isospinConj.isospinConj = a := (rfl)

/-- Isospin conjugation fixes the singlet charge. -/
@[simp]
theorem a0_isospinConj : a.isospinConj.a0 = a.a0 := by
  funext Q2
  simp only [a0_apply, deltaU_isospinConj, deltaD_isospinConj, deltaS_isospinConj]
  ring

/-- Isospin conjugation reverses the isovector charge. -/
@[simp]
theorem a3_isospinConj : a.isospinConj.a3 = -a.a3 := by
  funext Q2
  simp only [a3_apply, deltaU_isospinConj, deltaD_isospinConj, Pi.neg_apply]
  ring

/-- Isospin conjugation fixes the octet charge. -/
@[simp]
theorem a8_isospinConj : a.isospinConj.a8 = a.a8 := by
  funext Q2
  simp only [a8_apply, deltaU_isospinConj, deltaD_isospinConj, deltaS_isospinConj]
  ring

/-! ### Flavour-universal shifts -/

/-- The charges shifted by a common amount `s(Q²)` in every flavour: the form of a
flavour-universal contribution, such as the gluon's, to the quark helicity charges. -/
def addUniform (s : ℝ → ℝ) : HelicityCharges where
  deltaU Q2 := a.deltaU Q2 + s Q2
  deltaD Q2 := a.deltaD Q2 + s Q2
  deltaS Q2 := a.deltaS Q2 + s Q2

@[simp]
theorem deltaU_addUniform (s : ℝ → ℝ) (Q2 : ℝ) :
    (a.addUniform s).deltaU Q2 = a.deltaU Q2 + s Q2 := (rfl)

@[simp]
theorem deltaD_addUniform (s : ℝ → ℝ) (Q2 : ℝ) :
    (a.addUniform s).deltaD Q2 = a.deltaD Q2 + s Q2 := (rfl)

@[simp]
theorem deltaS_addUniform (s : ℝ → ℝ) (Q2 : ℝ) :
    (a.addUniform s).deltaS Q2 = a.deltaS Q2 + s Q2 := (rfl)

/-- A flavour-universal shift adds `s` to the helicity charge of every light flavour. -/
@[simp]
theorem delta_addUniform (s : ℝ → ℝ) (f : LightFlavor) (Q2 : ℝ) :
    (a.addUniform s).delta f Q2 = a.delta f Q2 + s Q2 := by
  cases f
  · rw [delta_u, delta_u, deltaU_addUniform]
  · rw [delta_d, delta_d, deltaD_addUniform]
  · rw [delta_s, delta_s, deltaS_addUniform]

/-- A flavour-universal shift by `s` shifts the singlet charge by `3 s`. -/
@[simp]
theorem a0_addUniform (s : ℝ → ℝ) : (a.addUniform s).a0 = fun Q2 => a.a0 Q2 + 3 * s Q2 := by
  funext Q2
  simp only [a0_apply, deltaU_addUniform, deltaD_addUniform, deltaS_addUniform]
  ring

/-- A flavour-universal shift does not change the isovector charge. -/
@[simp]
theorem a3_addUniform (s : ℝ → ℝ) : (a.addUniform s).a3 = a.a3 := by
  funext Q2
  simp only [a3_apply, deltaU_addUniform, deltaD_addUniform]
  ring

/-- A flavour-universal shift does not change the octet charge. -/
@[simp]
theorem a8_addUniform (s : ℝ → ℝ) : (a.addUniform s).a8 = a.a8 := by
  funext Q2
  simp only [a8_apply, deltaU_addUniform, deltaD_addUniform, deltaS_addUniform]
  ring

/-- **The non-singlet charges see no flavour-universal contribution.** Two charge records have
the same isovector and octet charges exactly when they differ by a flavour-universal shift; only
the singlet charge `a₀` can tell them apart. -/
theorem a3_eq_and_a8_eq_iff_exists_eq_addUniform :
    b.a3 = a.a3 ∧ b.a8 = a.a8 ↔ ∃ s : ℝ → ℝ, b = a.addUniform s := by
  constructor
  · rintro ⟨h3, h8⟩
    refine ⟨fun Q2 => (b.a0 Q2 - a.a0 Q2) / 3, ext_a0_a3_a8 _ _ ?_ ?_ ?_⟩
    · rw [a0_addUniform]
      funext Q2
      ring
    · rw [a3_addUniform, h3]
    · rw [a8_addUniform, h8]
  · rintro ⟨s, rfl⟩
    exact ⟨a3_addUniform a s, a8_addUniform a s⟩

/-! ### The first moment of `g₁` -/

/-- The leading-twist parton-model first moment of `g₁` of the target whose helicity charges these
are, before the radiative correction: `½ Σ_f e_f² Δ_f`, with `e_f` the quark charge
`LightFlavor.charge`. -/
def partonFirstMomentG1 : ℝ → ℝ := fun Q2 => (1 / 2) * ∑ f, LightFlavor.charge f ^ 2 * a.delta f Q2

theorem partonFirstMomentG1_apply (Q2 : ℝ) :
    a.partonFirstMomentG1 Q2 = (1 / 2) * ∑ f, LightFlavor.charge f ^ 2 * a.delta f Q2 := (rfl)

/-- The parton-model first moment with the light-quark charges evaluated,
`½ ((4/9) Δu + (1/9) Δd + (1/9) Δs)`: the combination in the field
`EllisJaffeSumRule.moment_decomposition`. -/
theorem partonFirstMomentG1_eq_helicityCharges (Q2 : ℝ) :
    a.partonFirstMomentG1 Q2
      = (1 / 2) * ((4 / 9) * a.deltaU Q2 + (1 / 9) * a.deltaD Q2 + (1 / 9) * a.deltaS Q2) := by
  rw [partonFirstMomentG1_apply, LightFlavor.sum_univ, LightFlavor.charge_u, LightFlavor.charge_d,
    LightFlavor.charge_s, delta_u, delta_d, delta_s]
  ring

/-- **The change of basis** for the parton-model first moment: the charge-weighted flavour sum is
`(1/12) a₃ + (1/36) a₈ + (1/9) a₀`. -/
theorem partonFirstMomentG1_eq_axialCharges (Q2 : ℝ) :
    a.partonFirstMomentG1 Q2 = (1 / 12) * a.a3 Q2 + (1 / 36) * a.a8 Q2 + (1 / 9) * a.a0 Q2 := by
  rw [partonFirstMomentG1_eq_helicityCharges, a0_apply, a3_apply, a8_apply]
  ring

/-- The parton-model first moment of the isospin-conjugate target,
`−(1/12) a₃ + (1/36) a₈ + (1/9) a₀`: under isospin symmetry, the neutron value in terms of the
proton's charges. -/
theorem partonFirstMomentG1_isospinConj (Q2 : ℝ) :
    a.isospinConj.partonFirstMomentG1 Q2
      = -(1 / 12) * a.a3 Q2 + (1 / 36) * a.a8 Q2 + (1 / 9) * a.a0 Q2 := by
  rw [partonFirstMomentG1_eq_axialCharges, a0_isospinConj, a3_isospinConj, a8_isospinConj,
    Pi.neg_apply]
  ring

/-- **The isovector first moment.** The difference of the parton-model first moments of a target
and its isospin conjugate is `(1/6) a₃`; neither `a₈` nor `a₀` enters. -/
theorem partonFirstMomentG1_sub_partonFirstMomentG1_isospinConj (Q2 : ℝ) :
    a.partonFirstMomentG1 Q2 - a.isospinConj.partonFirstMomentG1 Q2 = (1 / 6) * a.a3 Q2 := by
  rw [partonFirstMomentG1_isospinConj, partonFirstMomentG1_eq_axialCharges]
  ring

/-- The isoscalar first moment: the sum of the first moments of a target and its isospin conjugate
is `(1/18) a₈ + (2/9) a₀`, with no isovector part. -/
theorem partonFirstMomentG1_add_partonFirstMomentG1_isospinConj (Q2 : ℝ) :
    a.partonFirstMomentG1 Q2 + a.isospinConj.partonFirstMomentG1 Q2
      = (1 / 18) * a.a8 Q2 + (2 / 9) * a.a0 Q2 := by
  rw [partonFirstMomentG1_isospinConj, partonFirstMomentG1_eq_axialCharges]
  ring

/-- A flavour-universal shift by `s` shifts the parton-model first moment by `s / 3`, through the
singlet charge alone. -/
@[simp]
theorem partonFirstMomentG1_addUniform (s : ℝ → ℝ) (Q2 : ℝ) :
    (a.addUniform s).partonFirstMomentG1 Q2 = a.partonFirstMomentG1 Q2 + s Q2 / 3 := by
  rw [partonFirstMomentG1_eq_helicityCharges, partonFirstMomentG1_eq_helicityCharges,
    deltaU_addUniform, deltaD_addUniform, deltaS_addUniform]
  ring

/-- The parton-model first moment is the Ellis–Jaffe value `(1/12) a₃ + (5/36) a₈` plus `Δs / 3`. -/
theorem partonFirstMomentG1_eq_ellisJaffe_add_deltaS (Q2 : ℝ) :
    a.partonFirstMomentG1 Q2 = (1 / 12) * a.a3 Q2 + (5 / 36) * a.a8 Q2 + a.deltaS Q2 / 3 := by
  rw [partonFirstMomentG1_eq_axialCharges, deltaS_eq]
  ring

/-- The singlet charge in terms of the parton-model first moment `Γ₁(a)` and the non-singlet
charges, `a₀ = 9 Γ₁(a) − (3/4) a₃ − (1/4) a₈`. -/
theorem a0_eq_nine_mul_partonFirstMomentG1_sub (Q2 : ℝ) :
    a.a0 Q2 = 9 * a.partonFirstMomentG1 Q2 - (3 / 4) * a.a3 Q2 - (1 / 4) * a.a8 Q2 := by
  rw [partonFirstMomentG1_eq_axialCharges]
  ring

end HelicityCharges

/-! ### The sum rules in the charge basis -/

open HelicityCharges

/-- **The Ellis–Jaffe sum rule in the charge basis.** `EllisJaffeSumRule` for the charges `a` is
the leading-twist decomposition `Γ₁ᵖ = Γ₁(a) (1 + Δ)` together with `a₀ = a₈` at every scale: the
vanishing-strange hypothesis is an `SU(3)`-flavour statement about the singlet and octet
charges. -/
theorem ellisJaffeSumRule_iff (Gp : StructureFunctions) (a : HelicityCharges) (correction : ℝ → ℝ) :
    EllisJaffeSumRule Gp a.deltaU a.deltaD a.deltaS correction ↔
      (∀ Q2, firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2)) ∧
        ∀ Q2, a.a0 Q2 = a.a8 Q2 := by
  simp only [← deltaS_eq_zero_iff_a0_eq_a8, partonFirstMomentG1_eq_helicityCharges]
  exact ⟨fun h => ⟨h.moment_decomposition, h.strange_unpolarized⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **The measured first moment split at the Ellis–Jaffe value.** If the leading-twist
decomposition `Γ₁ᵖ = Γ₁(a) (1 + Δ)` holds at `Q²`, then
`Γ₁ᵖ(Q²) = ((1/12) a₃ + (5/36) a₈) (1 + Δ(Q²)) + (Δs / 3) (1 + Δ(Q²))`: the measured moment is the
Ellis–Jaffe value plus the strange contribution. -/
theorem firstMomentG1_eq_ellisJaffe_add_deltaS {Gp : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} {Q2 : ℝ}
    (hdec : firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2)) :
    firstMomentG1 Gp Q2
      = ((1 / 12) * a.a3 Q2 + (5 / 36) * a.a8 Q2) * (1 + correction Q2)
        + a.deltaS Q2 / 3 * (1 + correction Q2) := by
  rw [hdec, partonFirstMomentG1_eq_ellisJaffe_add_deltaS]
  ring

/-- **The Ellis–Jaffe prediction in the charge basis**,
`Γ₁ᵖ(Q²) = ((1/12) a₃ + (5/36) a₈) (1 + Δ(Q²))`: the proton first moment is fixed by the isovector
and octet charges alone. -/
theorem firstMomentG1_eq_of_ellisJaffeSumRule {Gp : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} (h : EllisJaffeSumRule Gp a.deltaU a.deltaD a.deltaS correction)
    (Q2 : ℝ) :
    firstMomentG1 Gp Q2
      = ((1 / 12) * a.a3 Q2 + (5 / 36) * a.a8 Q2) * (1 + correction Q2) := by
  rw [firstMomentG1_eq_ellisJaffe_add_deltaS (((ellisJaffeSumRule_iff Gp a correction).1 h).1 Q2),
    h.strange_unpolarized Q2, zero_div, zero_mul, add_zero]

/-- **The violation of the Ellis–Jaffe sum rule is a nonzero strange polarisation.** If the
leading-twist decomposition holds at `Q²` and the measured `Γ₁ᵖ(Q²)` differs from the Ellis–Jaffe
value, then `Δs(Q²) ≠ 0`. The derivation of the sum rule is sound; its hypothesis is what
fails. -/
theorem deltaS_ne_zero_of_firstMomentG1_ne {Gp : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} {Q2 : ℝ}
    (hdec : firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (hne : firstMomentG1 Gp Q2
      ≠ ((1 / 12) * a.a3 Q2 + (5 / 36) * a.a8 Q2) * (1 + correction Q2)) :
    a.deltaS Q2 ≠ 0 := by
  intro hs
  rw [firstMomentG1_eq_ellisJaffe_add_deltaS hdec, hs, zero_div, zero_mul, add_zero] at hne
  exact hne rfl

/-- The signed form of the violation: with a positive correction factor `1 + Δ(Q²)`, a measured
`Γ₁ᵖ(Q²)` below the Ellis–Jaffe value forces a negative strange polarisation. -/
theorem deltaS_neg_of_firstMomentG1_lt {Gp : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} {Q2 : ℝ}
    (hdec : firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (hc : 0 < 1 + correction Q2)
    (hlt : firstMomentG1 Gp Q2
      < ((1 / 12) * a.a3 Q2 + (5 / 36) * a.a8 Q2) * (1 + correction Q2)) :
    a.deltaS Q2 < 0 := by
  rw [firstMomentG1_eq_ellisJaffe_add_deltaS hdec] at hlt
  have h : a.deltaS Q2 / 3 * (1 + correction Q2) < 0 := by linarith
  linarith [neg_of_mul_neg_left h hc.le]

/-- **The singlet charge is measured.** If the leading-twist decomposition holds at `Q²` with a
nonzero correction factor, then `a₀(Q²)` is determined by the measured `Γ₁ᵖ(Q²)` and the
non-singlet charges: `a₀ = 9 Γ₁ᵖ / (1 + Δ) − (3/4) a₃ − (1/4) a₈`. -/
theorem a0_eq_of_firstMomentG1 {Gp : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} {Q2 : ℝ}
    (hdec : firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (hc : 1 + correction Q2 ≠ 0) :
    a.a0 Q2
      = 9 * (firstMomentG1 Gp Q2 / (1 + correction Q2)) - (3 / 4) * a.a3 Q2
        - (1 / 4) * a.a8 Q2 := by
  rw [hdec, mul_div_cancel_right₀ _ hc, a0_eq_nine_mul_partonFirstMomentG1_sub]

/-- The isovector combination of first moments in the charge basis: if the proton moment is the
leading-twist value of the charges `a` and the neutron moment that of their isospin conjugate,
with a common correction, then `Γ₁ᵖ − Γ₁ⁿ = (1/6) a₃ (1 + Δ)`. -/
theorem firstMomentG1_sub_firstMomentG1_eq {Gp Gn : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} {Q2 : ℝ}
    (hp : firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (hn : firstMomentG1 Gn Q2 = a.isospinConj.partonFirstMomentG1 Q2 * (1 + correction Q2)) :
    firstMomentG1 Gp Q2 - firstMomentG1 Gn Q2 = (1 / 6) * a.a3 Q2 * (1 + correction Q2) := by
  rw [hp, hn, ← sub_mul, partonFirstMomentG1_sub_partonFirstMomentG1_isospinConj]

/-- The Bjorken sum rule holds when the isovector charge is `|g_A/g_V|` at every scale, given the
leading-twist decomposition of the proton moment and its isospin conjugate for the neutron. -/
theorem bjorkenSumRule_of_forall_a3_eq {Gp Gn : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} {gAOverGV : ℝ}
    (hp : ∀ Q2, firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (hn : ∀ Q2, firstMomentG1 Gn Q2 = a.isospinConj.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (h3 : ∀ Q2, a.a3 Q2 = |gAOverGV|) :
    BjorkenSumRule Gp Gn gAOverGV correction :=
  ⟨fun Q2 => by rw [firstMomentG1_sub_firstMomentG1_eq (hp Q2) (hn Q2), h3 Q2]⟩

/-- **The Bjorken sum rule in the charge basis.** Given the leading-twist decomposition of the
proton moment and its isospin conjugate for the neutron, with a nowhere-vanishing correction
factor, the `BjorkenSumRule` with axial-charge ratio `g_A/g_V` holds exactly when the isovector
charge `a₃` is `|g_A/g_V|` at every scale: under the decomposition, the sum rule is exactly this
assignment of the isovector charge. -/
theorem bjorkenSumRule_iff {Gp Gn : StructureFunctions} {a : HelicityCharges}
    {correction : ℝ → ℝ} {gAOverGV : ℝ}
    (hp : ∀ Q2, firstMomentG1 Gp Q2 = a.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (hn : ∀ Q2, firstMomentG1 Gn Q2 = a.isospinConj.partonFirstMomentG1 Q2 * (1 + correction Q2))
    (hc : ∀ Q2, 1 + correction Q2 ≠ 0) :
    BjorkenSumRule Gp Gn gAOverGV correction ↔ ∀ Q2, a.a3 Q2 = |gAOverGV| := by
  refine ⟨fun hB Q2 => ?_, bjorkenSumRule_of_forall_a3_eq hp hn⟩
  have h := hB.bjorken Q2
  rw [firstMomentG1_sub_firstMomentG1_eq (hp Q2) (hn Q2)] at h
  have h' := mul_right_cancel₀ (hc Q2) h
  linarith

end Polarized
end DIS
end Scattering
end QFT
end EpsilonEridani
