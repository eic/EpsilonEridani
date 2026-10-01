/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.CrossSection
public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Longitudinal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The inclusive cross section, its inelasticity structure, and the reduced cross section

For unpolarised lepton-nucleon scattering through a vector/axial-vector exchange, with the lepton
mass neglected, the doubly differential inclusive cross section is

  `d²σ/dx dQ² = (K / (x Q²)) · [2 x y² F₁ + 2 (1 - y - M² x² y² / Q²) F₂ ∓ Y₋ x F₃]`,

where `M` is the target mass, `K` is the exchange-dependent flux factor (`K = 2π α² / Q²` for
pure photon exchange) and

  `Y₊ := 1 + (1 - y)²`,  `Y₋ := 1 - (1 - y)²`.

This file defines the bracket (`crossSectionBracket`), the cross section built from it
(`dSigma`) and the reduced cross section `σ_r := bracket / Y₊` (`reducedCrossSection`), and
proves the algebraic facts about the inelasticity dependence on which the extraction of structure
functions from measured cross sections rests.

## Main results

* `crossSectionBracket_eq_FL`: the bracket in terms of the longitudinal structure function
  `F_L = F₂ - 2 x F₁`, `Y₊ F₂ ∓ Y₋ x F₃ - y² F_L - (2 M² x² y² / Q²) F₂`, exactly; at `M = 0`
  this is the familiar `Y₊ F₂ ∓ Y₋ x F₃ - y² F_L` (`crossSectionBracket_zero_mass`). The target
  mass enters only through the last term.
* `Yplus_eq_two_mul_yFactor` and `dSigma_eq_loNCdSigma`: for photon exchange, no parity-odd
  term, zero target mass and the Callan-Gross relation, `dSigma` is the leading-order
  cross section `loNCdSigma`.
* `Yminus_le_Yplus`, `one_le_Yplus`, `Yminus_le_two_mul`: the inelasticity inequalities. They
  are sharp: `Y₊ - Y₋ = 2 (1 - y)²` (`Yplus_sub_Yminus`), so the parity-odd coefficient reaches
  the parity-even one at `y = 1`.
* `reducedCrossSection_eq_F2_iff`, `reducedCrossSection_zero_mass_eq_F2_iff`: `σ_r = F₂`
  exactly when the parity-odd, longitudinal and target-mass contributions sum to zero; at `M = 0`,
  exactly when `±Y₋ x F₃ + y² F_L = 0`. In particular `σ_r = F₂` at `y = 0`
  (`reducedCrossSection_at_zero_inelasticity`, `tendsto_reducedCrossSection_nhds_zero`).
* `existsUnique_reducedCrossSection_eq`: **separation of the structure functions.** At fixed
  `(x, Q²)`, with `x ≠ 0` and a non-zero beam-charge sign, the reduced cross sections at three
  distinct inelasticities determine `F₁`, `F₂` and `F₃`, and every triple of values is attained:
  the `3 × 3` matrix of inelasticity coefficients (`separationMatrix`) has determinant
  `-8 s x² (y₁ - y₀)(y₂ - y₀)(y₂ - y₁)` (`det_separationMatrix`).

## Conventions

`x`, `y`, `Q²` are the invariants of `Kinematics.DisKinematics` and the structure functions are
the dimensionless ones, with `F₂` in the physical normalisation of `Tensors.Longitudinal`. The
real parameter `s` is the sign of the parity-odd term: `s = 1` for a positron or antineutrino
beam and `s = -1` for an electron or neutrino beam. Nothing here constrains `s` to `±1`; only
`s ≠ 0` is ever needed. The flux factor `K` is an argument, since its propagator content
depends on the exchanged boson.

## References

* Particle Data Group, *Review of Particle Physics*, section "Structure functions",
  for the target-mass-exact form of the bracket.
* R. Devenish and A. Cooper-Sarkar, *Deep Inelastic Scattering*, Oxford University Press
  (2004), ch. 4.
* H1 and ZEUS Collaborations, *Combination of measurements of inclusive deep inelastic
  e±p scattering cross sections and QCD analysis of HERA data*, Eur. Phys. J. C **75** (2015)
  580, for the reduced cross section.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Inclusive

open Filter Topology
open Tensors.Longitudinal (FL IsCallanGross)

/-!
## The inelasticity factors `Y₊` and `Y₋`
-/

/-- The inelasticity factor `Y₊ := 1 + (1 - y)²` multiplying `F₂` in the inclusive cross
section. -/
def Yplus (y : ℝ) : ℝ := 1 + (1 - y) ^ 2

/-- The inelasticity factor `Y₋ := 1 - (1 - y)²` multiplying the parity-odd term `x F₃` in the
inclusive cross section. -/
def Yminus (y : ℝ) : ℝ := 1 - (1 - y) ^ 2

lemma Yplus_def (y : ℝ) : Yplus y = 1 + (1 - y) ^ 2 := (rfl)

lemma Yminus_def (y : ℝ) : Yminus y = 1 - (1 - y) ^ 2 := (rfl)

@[simp] lemma Yplus_zero : Yplus 0 = 2 := by norm_num [Yplus_def]

@[simp] lemma Yminus_zero : Yminus 0 = 0 := by norm_num [Yminus_def]

/-- `Y₊` is twice the leading-order inelasticity factor `yFactor`. -/
lemma Yplus_eq_two_mul_yFactor (y : ℝ) : Yplus y = 2 * yFactor y := by
  rw [Yplus_def, two_mul_yFactor]

/-- `Y₋ = y (2 - y)`. -/
lemma Yminus_eq_mul (y : ℝ) : Yminus y = y * (2 - y) := by
  rw [Yminus_def]
  ring

lemma Yplus_add_Yminus (y : ℝ) : Yplus y + Yminus y = 2 := by
  rw [Yplus_def, Yminus_def]
  ring

lemma Yplus_sub_Yminus (y : ℝ) : Yplus y - Yminus y = 2 * (1 - y) ^ 2 := by
  rw [Yplus_def, Yminus_def]
  ring

lemma one_le_Yplus (y : ℝ) : 1 ≤ Yplus y := by
  have := yFactor_ge_half y
  rw [Yplus_eq_two_mul_yFactor]
  linarith

lemma Yplus_pos (y : ℝ) : 0 < Yplus y := lt_of_lt_of_le one_pos (one_le_Yplus y)

lemma Yplus_ne_zero (y : ℝ) : Yplus y ≠ 0 := (Yplus_pos y).ne'

/-- The parity-odd inelasticity factor never exceeds the parity-even one, for every real `y`;
equality holds only at `y = 1` (`Yplus_sub_Yminus`). -/
lemma Yminus_le_Yplus (y : ℝ) : Yminus y ≤ Yplus y := by
  linarith [Yplus_sub_Yminus y, sq_nonneg (1 - y)]

lemma Yminus_le_one (y : ℝ) : Yminus y ≤ 1 := by
  rw [Yminus_def]
  linarith [sq_nonneg (1 - y)]

/-- `Y₋ ≤ 2 y`: the parity-odd term is suppressed linearly at small inelasticity, while
`Y₊ ≥ 1` (`one_le_Yplus`). -/
lemma Yminus_le_two_mul (y : ℝ) : Yminus y ≤ 2 * y := by
  rw [Yminus_eq_mul]
  nlinarith [sq_nonneg y]

lemma Yminus_nonneg {y : ℝ} (h0 : 0 ≤ y) (h2 : y ≤ 2) : 0 ≤ Yminus y := by
  rw [Yminus_eq_mul]
  exact mul_nonneg h0 (by linarith)

/-!
## The cross-section bracket and the cross section
-/

/-- The bracket of the inclusive cross section `d²σ/dx dQ²`,
`2 x y² F₁ + 2 (1 - y - M² x² y² / Q²) F₂ - s Y₋ x F₃`, exact in the target mass `M`, at Bjorken
variable `x`, virtuality `Q²` and inelasticity `y`. The sign `s` of the parity-odd term is `1`
for a positron or antineutrino beam and `-1` for an electron or neutrino beam. -/
def crossSectionBracket (M s x Q2 y F1 F2 F3 : ℝ) : ℝ :=
  2 * x * y ^ 2 * F1 + 2 * (1 - y - M ^ 2 * x ^ 2 * y ^ 2 / Q2) * F2 - s * Yminus y * (x * F3)

lemma crossSectionBracket_def (M s x Q2 y F1 F2 F3 : ℝ) :
    crossSectionBracket M s x Q2 y F1 F2 F3 =
      2 * x * y ^ 2 * F1 + 2 * (1 - y - M ^ 2 * x ^ 2 * y ^ 2 / Q2) * F2
        - s * Yminus y * (x * F3) := (rfl)

/-- **The bracket in terms of `F_L`.** Trading `F₁` for the longitudinal structure function
`F_L = F₂ - 2 x F₁` gives the familiar `Y₊ F₂ ∓ Y₋ x F₃ - y² F_L` plus the target-mass term
`-(2 M² x² y² / Q²) F₂`, exactly. -/
theorem crossSectionBracket_eq_FL (M s x Q2 y F1 F2 F3 : ℝ) :
    crossSectionBracket M s x Q2 y F1 F2 F3 =
      Yplus y * F2 - s * Yminus y * (x * F3) - y ^ 2 * FL x F1 F2
        - 2 * M ^ 2 * x ^ 2 * y ^ 2 / Q2 * F2 := by
  rw [crossSectionBracket_def, Yplus_def]
  unfold FL
  ring

/-- At zero target mass the bracket is `Y₊ F₂ ∓ Y₋ x F₃ - y² F_L`. -/
@[simp] theorem crossSectionBracket_zero_mass (s x Q2 y F1 F2 F3 : ℝ) :
    crossSectionBracket 0 s x Q2 y F1 F2 F3 =
      Yplus y * F2 - s * Yminus y * (x * F3) - y ^ 2 * FL x F1 F2 := by
  rw [crossSectionBracket_eq_FL]
  ring

/-- The inclusive cross section `d²σ/dx dQ² = (K / (x Q²)) · bracket` for an exchange with flux
factor `K`; for pure photon exchange `K = 2π α² / Q²`. -/
def dSigma (K M s x Q2 y F1 F2 F3 : ℝ) : ℝ :=
  K / (x * Q2) * crossSectionBracket M s x Q2 y F1 F2 F3

lemma dSigma_def (K M s x Q2 y F1 F2 F3 : ℝ) :
    dSigma K M s x Q2 y F1 F2 F3 = K / (x * Q2) * crossSectionBracket M s x Q2 y F1 F2 F3 :=
  (rfl)

/-- **Compatibility with the leading-order cross section.** For photon exchange
(`K = 2π α² / Q²`), with no parity-odd term, zero target mass and the Callan-Gross relation,
the inclusive cross section is `loNCdSigma`. -/
theorem dSigma_eq_loNCdSigma (α s x Q2 y F1 F2 : ℝ) (h : IsCallanGross x F1 F2) :
    dSigma (2 * Real.pi * α ^ 2 / Q2) 0 s x Q2 y F1 F2 0 = loNCdSigma α x Q2 y F2 := by
  unfold IsCallanGross at h
  rw [dSigma_def, crossSectionBracket_zero_mass, h, Yplus_eq_two_mul_yFactor, loNCdSigma]
  ring

/-!
## The reduced cross section
-/

/-- The reduced cross section `σ_r := bracket / Y₊`, so that `d²σ/dx dQ² = (K / (x Q²)) Y₊ σ_r`
(`dSigma_eq_mul_reducedCrossSection`). At zero target mass it is
`F₂ ∓ (Y₋ / Y₊) x F₃ - (y² / Y₊) F_L` (`reducedCrossSection_zero_mass`). -/
def reducedCrossSection (M s x Q2 y F1 F2 F3 : ℝ) : ℝ :=
  crossSectionBracket M s x Q2 y F1 F2 F3 / Yplus y

lemma reducedCrossSection_def (M s x Q2 y F1 F2 F3 : ℝ) :
    reducedCrossSection M s x Q2 y F1 F2 F3 =
      crossSectionBracket M s x Q2 y F1 F2 F3 / Yplus y := (rfl)

/-- The reduced cross section is well posed for every inelasticity, since `Y₊ > 0`: it
recovers the bracket. -/
lemma Yplus_mul_reducedCrossSection (M s x Q2 y F1 F2 F3 : ℝ) :
    Yplus y * reducedCrossSection M s x Q2 y F1 F2 F3 =
      crossSectionBracket M s x Q2 y F1 F2 F3 := by
  rw [reducedCrossSection_def, mul_div_cancel₀ _ (Yplus_ne_zero y)]

lemma dSigma_eq_mul_reducedCrossSection (K M s x Q2 y F1 F2 F3 : ℝ) :
    dSigma K M s x Q2 y F1 F2 F3 =
      K / (x * Q2) * Yplus y * reducedCrossSection M s x Q2 y F1 F2 F3 := by
  rw [mul_assoc, Yplus_mul_reducedCrossSection, dSigma_def]

/-- At zero target mass, `σ_r = F₂ ∓ (Y₋ / Y₊) x F₃ - (y² / Y₊) F_L`. -/
theorem reducedCrossSection_zero_mass (s x Q2 y F1 F2 F3 : ℝ) :
    reducedCrossSection 0 s x Q2 y F1 F2 F3 =
      F2 - s * (Yminus y / Yplus y) * (x * F3) - y ^ 2 / Yplus y * FL x F1 F2 := by
  rw [reducedCrossSection_def, crossSectionBracket_zero_mass]
  field_simp [Yplus_ne_zero y]

/-- `σ_r = F₂` exactly when the parity-odd, longitudinal and target-mass contributions sum to
zero. -/
theorem reducedCrossSection_eq_F2_iff (M s x Q2 y F1 F2 F3 : ℝ) :
    reducedCrossSection M s x Q2 y F1 F2 F3 = F2 ↔
      s * Yminus y * (x * F3) + y ^ 2 * FL x F1 F2 + 2 * M ^ 2 * x ^ 2 * y ^ 2 / Q2 * F2
        = 0 := by
  rw [reducedCrossSection_def, div_eq_iff (Yplus_ne_zero y), crossSectionBracket_eq_FL]
  constructor <;> intro h <;> linarith

/-- At zero target mass, `σ_r = F₂` exactly when `±Y₋ x F₃ + y² F_L = 0`. -/
theorem reducedCrossSection_zero_mass_eq_F2_iff (s x Q2 y F1 F2 F3 : ℝ) :
    reducedCrossSection 0 s x Q2 y F1 F2 F3 = F2 ↔
      s * Yminus y * (x * F3) + y ^ 2 * FL x F1 F2 = 0 := by
  rw [reducedCrossSection_eq_F2_iff]
  simp

/-- At vanishing inelasticity the reduced cross section is `F₂`. -/
@[simp] theorem reducedCrossSection_at_zero_inelasticity (M s x Q2 F1 F2 F3 : ℝ) :
    reducedCrossSection M s x Q2 0 F1 F2 F3 = F2 := by
  rw [reducedCrossSection_eq_F2_iff]
  simp

theorem continuous_reducedCrossSection (M s x Q2 F1 F2 F3 : ℝ) :
    Continuous fun y => reducedCrossSection M s x Q2 y F1 F2 F3 := by
  simp only [reducedCrossSection_def, crossSectionBracket_def, Yplus_def, Yminus_def]
  exact Continuous.div (by fun_prop) (by fun_prop) fun y => Yplus_ne_zero y

/-- As `y → 0` the reduced cross section tends to `F₂`. -/
theorem tendsto_reducedCrossSection_nhds_zero (M s x Q2 F1 F2 F3 : ℝ) :
    Tendsto (fun y => reducedCrossSection M s x Q2 y F1 F2 F3) (𝓝 0) (𝓝 F2) := by
  simpa using (continuous_reducedCrossSection M s x Q2 F1 F2 F3).tendsto 0

/-!
## Separation of `F₁`, `F₂`, `F₃` from three inelasticities
-/

/-- The matrix of inelasticity coefficients of the bracket at three inelasticities `y i`: row
`i` holds the coefficients of `(F₁, F₂, F₃)` in `crossSectionBracket M s x Q2 (y i)`
(`separationMatrix_mulVec`). -/
def separationMatrix (M s x Q2 : ℝ) (y : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i =>
    ![2 * x * y i ^ 2, 2 * (1 - y i - M ^ 2 * x ^ 2 * y i ^ 2 / Q2), -(s * Yminus (y i) * x)]

lemma separationMatrix_apply (M s x Q2 : ℝ) (y : Fin 3 → ℝ) (i j : Fin 3) :
    separationMatrix M s x Q2 y i j =
      ![2 * x * y i ^ 2, 2 * (1 - y i - M ^ 2 * x ^ 2 * y i ^ 2 / Q2),
        -(s * Yminus (y i) * x)] j := (rfl)

theorem separationMatrix_mulVec (M s x Q2 : ℝ) (y F : Fin 3 → ℝ) (i : Fin 3) :
    (separationMatrix M s x Q2 y).mulVec F i =
      crossSectionBracket M s x Q2 (y i) (F 0) (F 1) (F 2) := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three, separationMatrix_apply,
    crossSectionBracket_def]
  simp
  ring

/-- The determinant of the separation matrix: the mass-independent constant `-8 s x²` times the
Vandermonde determinant of the three inelasticities. -/
theorem det_separationMatrix (M s x Q2 : ℝ) (y : Fin 3 → ℝ) :
    (separationMatrix M s x Q2 y).det =
      -8 * s * x ^ 2 * ((y 1 - y 0) * (y 2 - y 0) * (y 2 - y 1)) := by
  rw [Matrix.det_fin_three]
  simp only [separationMatrix_apply, Yminus_def]
  simp
  ring

theorem det_separationMatrix_ne_zero {M s x Q2 : ℝ} {y : Fin 3 → ℝ} (hs : s ≠ 0) (hx : x ≠ 0)
    (hy : Function.Injective y) : (separationMatrix M s x Q2 y).det ≠ 0 := by
  have h10 : y 1 - y 0 ≠ 0 := sub_ne_zero.2 (hy.ne (by decide))
  have h20 : y 2 - y 0 ≠ 0 := sub_ne_zero.2 (hy.ne (by decide))
  have h21 : y 2 - y 1 ≠ 0 := sub_ne_zero.2 (hy.ne (by decide))
  rw [det_separationMatrix]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs) (pow_ne_zero 2 hx))
    (mul_ne_zero (mul_ne_zero h10 h20) h21)

/-- **Separation of the structure functions.** At fixed `(x, Q²)` with `x ≠ 0` and `s ≠ 0`, for
three distinct inelasticities `y i` and any three values `σ i`, there is exactly one triple
`(F₁, F₂, F₃)` whose reduced cross sections at the `y i` are the `σ i`. -/
theorem existsUnique_reducedCrossSection_eq {M s x Q2 : ℝ} {y : Fin 3 → ℝ} (hs : s ≠ 0) (hx : x ≠ 0)
    (hy : Function.Injective y) (σ : Fin 3 → ℝ) :
    ∃! F : Fin 3 → ℝ, ∀ i, reducedCrossSection M s x Q2 (y i) (F 0) (F 1) (F 2) = σ i := by
  have hA : IsUnit (separationMatrix M s x Q2 y) :=
    (Matrix.isUnit_iff_isUnit_det _).2
      (isUnit_iff_ne_zero.2 (det_separationMatrix_ne_zero hs hx hy))
  have key : ∀ F : Fin 3 → ℝ, (∀ i, reducedCrossSection M s x Q2 (y i) (F 0) (F 1) (F 2) = σ i) ↔
      (separationMatrix M s x Q2 y).mulVec F = fun i => Yplus (y i) * σ i := by
    intro F
    simp only [funext_iff, separationMatrix_mulVec, reducedCrossSection_def,
      div_eq_iff (Yplus_ne_zero _), mul_comm (σ _)]
  simp only [key]
  obtain ⟨F, hF⟩ := Matrix.mulVec_surjective_iff_isUnit.2 hA fun i => Yplus (y i) * σ i
  exact ⟨F, hF, fun F' hF' => Matrix.mulVec_injective_iff_isUnit.2 hA (hF'.trans hF.symm)⟩

/-- The reduced cross sections at three distinct inelasticities determine `F₁`, `F₂` and `F₃`,
given `x ≠ 0` and `s ≠ 0`. -/
theorem eq_of_forall_reducedCrossSection_eq {M s x Q2 : ℝ} {y : Fin 3 → ℝ} (hs : s ≠ 0) (hx : x ≠ 0)
    (hy : Function.Injective y) {F1 F2 F3 F1' F2' F3' : ℝ}
    (h : ∀ i, reducedCrossSection M s x Q2 (y i) F1 F2 F3 =
      reducedCrossSection M s x Q2 (y i) F1' F2' F3') :
    F1 = F1' ∧ F2 = F2' ∧ F3 = F3' := by
  have := (existsUnique_reducedCrossSection_eq (M := M) (Q2 := Q2) hs hx hy
    fun i => reducedCrossSection M s x Q2 (y i) F1' F2' F3').unique (y₁ := ![F1, F2, F3])
    (y₂ := ![F1', F2', F3']) (by simpa using h) (by simp)
  exact ⟨congrFun this 0, congrFun this 1, congrFun this 2⟩

end Inclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
