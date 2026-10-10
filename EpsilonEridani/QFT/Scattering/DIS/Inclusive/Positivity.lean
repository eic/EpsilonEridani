/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Inclusive.CrossSection
public import TauCeti.Analysis.Matrix.PosSemidef

/-!
# Positivity of the inclusive structure functions from the helicity matrix

The forward virtual-boson–nucleon amplitude of an unpolarised target, written in the helicity
basis `(+1, 0, -1)` of the exchanged current, is a `3 × 3` positive-semidefinite matrix: its
diagonal entries are the absorption cross sections `σ₊`, `σ_L`, `σ₋` of the three current
polarisations, and positive semidefiniteness is the statement that every polarisation state of
the current is absorbed with non-negative probability. In terms of the dimensionless structure
functions, exactly in the target mass `M`,

  `σ₊ = F₁ - √(1 + γ²) F₃ / 2`,  `σ₋ = F₁ + √(1 + γ²) F₃ / 2`,  `2 x σ_L = F_L^{exact}`,

with `γ² = 4 M² x² / Q²` and `F_L^{exact} = (1 + γ²) F₂ - 2 x F₁` (`Tensors.Longitudinal.FLExact`).
The factor `√(1 + γ²) = |𝐪| / ν` in the target rest frame is the size of the parity-odd structure
`ε(e₁, e₂, p, q) / (p·q)` on the two transverse polarisation directions; at `M = 0` it is `1`.

This module bundles that matrix as `HelicityMatrix`, records the identification of its diagonal
entries with the structure functions as the predicate `IsHelicityMatrixOf`, and derives the
positivity constraints on `F₁`, `F₂`, `F₃` and `F_L^{exact}` from positive semidefiniteness
alone, as theorems rather than assumptions.

## Main results

* `IsHelicityMatrixOf.F1_nonneg`, `IsHelicityMatrixOf.abs_F3_le_two_mul_F1`,
  `IsHelicityMatrixOf.FLExact_nonneg`, `IsHelicityMatrixOf.F2_nonneg`: the bounds
  `F₁ ≥ 0`, `|F₃| ≤ 2 F₁` (sharpened by the factor `√(1 + γ²)` in
  `IsHelicityMatrixOf.sqrt_mul_abs_F3_le_two_mul_F1`), `F_L^{exact} ≥ 0` and `F₂ ≥ 0`.
* `IsHelicityMatrixOf.two_mul_mul_F1_le`: `2 x F₁ ≤ (1 + 4 M² x² / Q²) F₂`, which is
  `F_L^{exact} ≥ 0` rewritten. It is strictly weaker than the Callan-Gross relation
  (`exists_isHelicityMatrixOf_iff_of_isCallanGross`,
  `exists_isHelicityMatrixOf_and_not_isCallanGross`).
* `exists_isHelicityMatrixOf_iff`: the bounds are complete. A triple `(F₁, F₂, F₃)` is
  represented by some positive-semidefinite helicity matrix exactly when
  `√(1 + γ²) |F₃| ≤ 2 F₁` and `F_L^{exact} ≥ 0`.
* `IsHelicityMatrixOf.sq_apply_plus_minus_le`: the Cauchy-Schwarz bound on the helicity-flip
  interference entry in terms of the transverse absorption cross sections.
* `IsHelicityMatrixOf.crossSectionBracket_nonneg`: the inclusive cross section of
  `Inclusive.CrossSection` is non-negative throughout the physical region
  `1 - y - M² x² y² / Q² ≥ 0`, for either sign of the parity-odd term. It is a non-negative
  combination of `σ₊`, `σ₋` and `σ_L`.
* `forall_apply_self_nonneg_iff_exists_isHelicityMatrixOf`: for a parity-even hadronic tensor in
  the transverse basis of `Tensors.Hadronic`, positivity of the tensor on every vector is
  equivalent to the existence of a positive-semidefinite helicity matrix for its structure
  functions with `F₃ = 0`. This derives the transverse and longitudinal identifications of the
  diagonal entries from the tensor.

## Conventions

The matrix is real, following `Particles.Parton.PDF.SpinDensity`. The structure functions are
the dimensionless ones of `Inclusive.CrossSection`, with `F₂` in the physical normalisation of
`Tensors.Longitudinal.structureF2`. The sign attaching `-F₃` to helicity `+1` is a convention for
the orientation of the transverse plane; every bound below is symmetric under `F₃ ↦ -F₃`.

## References

* R. Devenish and A. Cooper-Sarkar, *Deep Inelastic Scattering*, Oxford University Press
  (2004), ch. 4.
* Particle Data Group, *Review of Particle Physics*, section "Structure functions".
* L. N. Hand, *Experimental investigation of pion electroproduction*, Phys. Rev. **129** (1963)
  1834, for the virtual-photon absorption cross sections.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Inclusive

open Tensors.Longitudinal (FL FLExact IsCallanGross structureF2)

/-!
## The helicity matrix
-/

/-- The forward virtual-boson–nucleon helicity-amplitude matrix of an unpolarised target, at one
value of `(x, Q²)`, in the helicity basis `(+1, 0, -1)` of the exchanged current
(`HelicityMatrix.idxPlus`, `HelicityMatrix.idxLong`, `HelicityMatrix.idxMinus`). Its diagonal
entries are the absorption cross sections of the three current polarisations; the only field
beyond the matrix is positive semidefiniteness, which is what the probability interpretation of
the amplitudes provides. -/
@[ext]
structure HelicityMatrix where
  /-- The matrix of forward helicity amplitudes, in the basis `(+1, 0, -1)`. -/
  mat : Matrix (Fin 3) (Fin 3) ℝ
  /-- Positive semidefiniteness of the forward helicity amplitudes. -/
  posSemidef : mat.PosSemidef

namespace HelicityMatrix

/-- Basis index of current helicity `+1`. -/
def idxPlus : Fin 3 := 0

/-- Basis index of current helicity `0`, the longitudinal polarisation. -/
def idxLong : Fin 3 := 1

/-- Basis index of current helicity `-1`. -/
def idxMinus : Fin 3 := 2

lemma idxPlus_def : idxPlus = 0 := (rfl)

lemma idxLong_def : idxLong = 1 := (rfl)

lemma idxMinus_def : idxMinus = 2 := (rfl)

/-- **Cauchy-Schwarz for the helicity amplitudes.** An interference entry is bounded by the
geometric mean of the two absorption cross sections it interferes. -/
lemma sq_apply_le (H : HelicityMatrix) (i j : Fin 3) :
    H.mat i j ^ 2 ≤ H.mat i i * H.mat j j := by
  simpa [RCLike.normSq_apply, sq] using H.posSemidef.normSq_le i j

/-- The diagonal helicity matrix with non-negative absorption cross sections `d`. -/
def diagonal (d : Fin 3 → ℝ) (hd : 0 ≤ d) : HelicityMatrix where
  mat := Matrix.diagonal d
  posSemidef := Matrix.PosSemidef.diagonal hd

@[simp] lemma diagonal_mat (d : Fin 3 → ℝ) (hd : 0 ≤ d) :
    (diagonal d hd).mat = Matrix.diagonal d := (rfl)

end HelicityMatrix

open HelicityMatrix

/-!
## Identification with the structure functions
-/

/-- The diagonal entries of the helicity matrix `H` are the absorption cross sections of the
structure functions `F₁`, `F₂`, `F₃` at target mass `M`, Bjorken variable `x` and virtuality
`Q²`:
`σ₊ = F₁ - √(1 + γ²) F₃ / 2`, `σ₋ = F₁ + √(1 + γ²) F₃ / 2` and `2 x σ_L = F_L^{exact}`, with
`γ² = 4 M² x² / Q²`. The off-diagonal interference entries are not constrained. -/
structure IsHelicityMatrixOf (H : HelicityMatrix) (M x Q2 F1 F2 F3 : ℝ) : Prop where
  /-- The helicity `+1` absorption cross section. -/
  plus : H.mat idxPlus idxPlus = F1 - Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2) * F3 / 2
  /-- The helicity `-1` absorption cross section. -/
  minus : H.mat idxMinus idxMinus = F1 + Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2) * F3 / 2
  /-- The longitudinal absorption cross section. -/
  long : 2 * x * H.mat idxLong idxLong = FLExact M x Q2 F1 F2

/-- At non-negative virtuality the target-mass factor `√(1 + 4 M² x² / Q²)` is at least `1`. -/
private lemma one_le_sqrt_one_add_targetMass (M x : ℝ) {Q2 : ℝ} (hQ2 : 0 ≤ Q2) :
    1 ≤ Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2) :=
  Real.one_le_sqrt.mpr (le_add_of_nonneg_right (by positivity))

namespace IsHelicityMatrixOf

variable {H : HelicityMatrix} {M x Q2 F1 F2 F3 : ℝ}

/-- `F₁` is the average of the two transverse absorption cross sections. -/
lemma F1_eq (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) :
    F1 = (H.mat idxPlus idxPlus + H.mat idxMinus idxMinus) / 2 := by
  rw [h.plus, h.minus]
  ring

/-- **`F₁ ≥ 0`**, from the non-negativity of the two transverse absorption cross sections. -/
theorem F1_nonneg (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) : 0 ≤ F1 := by
  rw [h.F1_eq]
  have := H.posSemidef.diag_nonneg (i := idxPlus)
  have := H.posSemidef.diag_nonneg (i := idxMinus)
  positivity

/-- **The parity-odd structure function is bounded by the parity-even one**, exactly in the
target mass: `√(1 + γ²) |F₃| ≤ 2 F₁`, from the non-negativity of each transverse absorption
cross section separately. -/
theorem sqrt_mul_abs_F3_le_two_mul_F1 (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) :
    Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2) * |F3| ≤ 2 * F1 := by
  have hp := H.posSemidef.diag_nonneg (i := idxPlus)
  have hm := H.posSemidef.diag_nonneg (i := idxMinus)
  rw [h.plus] at hp
  rw [h.minus] at hm
  rw [← abs_of_nonneg (Real.sqrt_nonneg (1 + 4 * M ^ 2 * x ^ 2 / Q2)), ← abs_mul, abs_le]
  constructor <;> linarith

/-- **`|F₃| ≤ 2 F₁`.** The parity-odd structure function cannot exceed twice `F₁`; at finite
target mass this is weakened from `sqrt_mul_abs_F3_le_two_mul_F1` by `√(1 + γ²) ≥ 1`. -/
theorem abs_F3_le_two_mul_F1 (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hQ2 : 0 ≤ Q2) :
    |F3| ≤ 2 * F1 :=
  le_trans (le_mul_of_one_le_left (abs_nonneg F3) (one_le_sqrt_one_add_targetMass M x hQ2))
    h.sqrt_mul_abs_F3_le_two_mul_F1

/-- **`F_L^{exact} ≥ 0`**, from the non-negativity of the longitudinal absorption cross
section. -/
theorem FLExact_nonneg (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hx : 0 ≤ x) :
    0 ≤ FLExact M x Q2 F1 F2 := by
  rw [← h.long]
  have := H.posSemidef.diag_nonneg (i := idxLong)
  positivity

/-- **`2 x F₁ ≤ (1 + 4 M² x² / Q²) F₂`**, the non-negativity of the longitudinal absorption
cross section written in `F₁` and `F₂`. -/
theorem two_mul_mul_F1_le (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hx : 0 ≤ x) :
    2 * x * F1 ≤ (1 + 4 * M ^ 2 * x ^ 2 / Q2) * F2 := by
  have := h.FLExact_nonneg hx
  rw [Tensors.Longitudinal.FLExact] at this
  linarith

/-- **`F₂ ≥ 0`.** Since `F₁ ≥ 0`, the longitudinal bound `two_mul_mul_F1_le` forces `F₂` to be
non-negative. -/
theorem F2_nonneg (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hx : 0 ≤ x) (hQ2 : 0 ≤ Q2) :
    0 ≤ F2 := by
  have hle := h.two_mul_mul_F1_le hx
  have hF1 := h.F1_nonneg
  have hpos : 0 < 1 + 4 * M ^ 2 * x ^ 2 / Q2 := by positivity
  exact nonneg_of_mul_nonneg_right (le_trans (by positivity) hle) hpos

/-- **Cauchy-Schwarz for the helicity-flip interference.** The `(+1, -1)` entry of the helicity
matrix is bounded by the product of the transverse absorption cross sections,
`F₁² - (1 + γ²) F₃² / 4`. -/
theorem sq_apply_plus_minus_le (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hQ2 : 0 ≤ Q2) :
    H.mat idxPlus idxMinus ^ 2 ≤ F1 ^ 2 - (1 + 4 * M ^ 2 * x ^ 2 / Q2) * F3 ^ 2 / 4 := by
  have hs : Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2) ^ 2 = 1 + 4 * M ^ 2 * x ^ 2 / Q2 :=
    Real.sq_sqrt (by positivity)
  have hcs := H.sq_apply_le idxPlus idxMinus
  rw [h.plus, h.minus] at hcs
  linear_combination hcs - F3 ^ 2 / 4 * hs

end IsHelicityMatrixOf

/-!
## Completeness of the bounds
-/

/-- **The positivity bounds are complete.** At positive `x`, a triple of structure functions is
represented by a positive-semidefinite helicity matrix exactly when `√(1 + γ²) |F₃| ≤ 2 F₁`
and `F_L^{exact} ≥ 0`; a diagonal matrix then suffices. -/
theorem exists_isHelicityMatrixOf_iff {M x Q2 F1 F2 F3 : ℝ} (hx : 0 < x) :
    (∃ H, IsHelicityMatrixOf H M x Q2 F1 F2 F3) ↔
      Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2) * |F3| ≤ 2 * F1 ∧ 0 ≤ FLExact M x Q2 F1 F2 := by
  refine ⟨fun ⟨H, h⟩ => ⟨h.sqrt_mul_abs_F3_le_two_mul_F1, h.FLExact_nonneg hx.le⟩,
    fun ⟨h3, hL⟩ => ?_⟩
  set r := Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have h3' : |r * F3| ≤ 2 * F1 := by rwa [abs_mul, abs_of_nonneg hr]
  obtain ⟨h3l, h3r⟩ := abs_le.mp h3'
  let d : Fin 3 → ℝ := ![F1 - r * F3 / 2, FLExact M x Q2 F1 F2 / (2 * x), F1 + r * F3 / 2]
  have hd : 0 ≤ d := by
    intro i
    fin_cases i
    · simpa [d] using (by linarith : 0 ≤ F1 - r * F3 / 2)
    · simpa [d] using (by positivity : 0 ≤ FLExact M x Q2 F1 F2 / (2 * x))
    · simpa [d] using (by linarith : 0 ≤ F1 + r * F3 / 2)
  refine ⟨HelicityMatrix.diagonal d hd, ⟨?_, ?_, ?_⟩⟩
  · simp [idxPlus_def, d, r]
  · simp [idxMinus_def, d, r]
  · simp only [diagonal_mat, idxLong_def, Matrix.diagonal_apply_eq, d]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp

/-- **Callan-Gross implies the longitudinal bound.** Under the Callan-Gross relation, at positive
`x` and non-negative `Q²`, a triple of structure functions is represented by a
positive-semidefinite helicity matrix exactly when `√(1 + γ²) |F₃| ≤ 2 F₁`: the longitudinal
entry is the non-negative target-mass term. -/
theorem exists_isHelicityMatrixOf_iff_of_isCallanGross {M x Q2 F1 F2 F3 : ℝ} (hx : 0 < x)
    (hQ2 : 0 ≤ Q2) (hCG : IsCallanGross x F1 F2) :
    (∃ H, IsHelicityMatrixOf H M x Q2 F1 F2 F3) ↔
      Real.sqrt (1 + 4 * M ^ 2 * x ^ 2 / Q2) * |F3| ≤ 2 * F1 := by
  rw [exists_isHelicityMatrixOf_iff hx, and_iff_left_iff_imp]
  intro h3
  have hF1 : 0 ≤ F1 := by
    have := mul_nonneg (Real.sqrt_nonneg (1 + 4 * M ^ 2 * x ^ 2 / Q2)) (abs_nonneg F3)
    linarith
  rw [Tensors.Longitudinal.FLExact_eq_targetMassTerm_of_isCallanGross M x Q2 F1 F2 hCG,
    (Tensors.Longitudinal.isCallanGross_iff x F1 F2).mp hCG]
  positivity

/-- **The longitudinal bound is strictly weaker than Callan-Gross.** At every positive `x` and
non-negative `Q²` the triple `(F₁, F₂, F₃) = (0, 1, 0)`, pure longitudinal absorption, is
represented by a positive-semidefinite helicity matrix but violates the Callan-Gross
relation. -/
theorem exists_isHelicityMatrixOf_and_not_isCallanGross (M : ℝ) {x Q2 : ℝ} (hx : 0 < x)
    (hQ2 : 0 ≤ Q2) :
    (∃ H, IsHelicityMatrixOf H M x Q2 0 1 0) ∧ ¬ IsCallanGross x 0 1 := by
  refine ⟨(exists_isHelicityMatrixOf_iff hx).mpr ⟨by simp, ?_⟩, ?_⟩
  · rw [Tensors.Longitudinal.FLExact, mul_one, mul_zero, sub_zero]
    positivity
  · simp [IsCallanGross, FL]

/-!
## Positivity of the inclusive cross section
-/

/-- **The inclusive cross section is non-negative.** In the physical region
`1 - y - M² x² y² / Q² ≥ 0`, for a parity-odd sign `|s| ≤ 1`, the bracket of
`Inclusive.CrossSection` is non-negative whenever the structure functions are represented by a
positive-semidefinite helicity matrix: `(1 + γ²)` times the bracket is `x` times a combination
of the three absorption cross sections `σ₊`, `σ₋`, `σ_L` with non-negative coefficients. -/
theorem IsHelicityMatrixOf.crossSectionBracket_nonneg {H : HelicityMatrix}
    {M s x Q2 y F1 F2 F3 : ℝ} (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hx : 0 < x)
    (hQ2 : 0 ≤ Q2) (hs : |s| ≤ 1) (hy : 0 ≤ y) (hphys : 0 ≤ 1 - y - M ^ 2 * x ^ 2 * y ^ 2 / Q2) :
    0 ≤ crossSectionBracket M s x Q2 y F1 F2 F3 := by
  obtain ⟨G, hG⟩ : ∃ G, G = 4 * M ^ 2 * x ^ 2 / Q2 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (1 + G) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ by positivity
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have hr2 : r ^ 2 = 1 + G := hr ▸ Real.sq_sqrt (by positivity)
  have hMG : M ^ 2 * x ^ 2 * y ^ 2 / Q2 = G * y ^ 2 / 4 := by rw [hG]; ring
  rw [hMG] at hphys
  have hy1 : y ≤ 1 := by nlinarith
  -- the three absorption cross sections
  have hp := H.posSemidef.diag_nonneg (i := idxPlus)
  have hm := H.posSemidef.diag_nonneg (i := idxMinus)
  have hl := H.posSemidef.diag_nonneg (i := idxLong)
  have hplus := h.plus
  have hminus := h.minus
  have hlong := h.long
  rw [← hG, ← hr] at hplus hminus
  rw [Tensors.Longitudinal.FLExact, ← hG] at hlong
  -- the coefficient `A = y² - 2 y + 2 + γ² y² / 2` of `F₁` dominates the coefficient
  -- `Y₋ √(1 + γ²)` of `F₃`, because `A² - (1 + γ²) Y₋² = 4 (1 - y - γ² y² / 4)²`
  have hYm : 0 ≤ Yminus y := Yminus_nonneg hy (by linarith)
  have hkey : (y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2) ^ 2 - (Yminus y * r) ^ 2
      = (2 * (1 - y - G * y ^ 2 / 4)) ^ 2 := by
    rw [mul_pow, hr2, Yminus_eq_mul]
    ring
  have hA0 : 0 ≤ y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2 := by nlinarith
  have hdom : Yminus y * r ≤ y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2 :=
    (pow_le_pow_iff_left₀ (mul_nonneg hYm hr0) hA0 two_ne_zero).mp (by nlinarith)
  have hsY : |s * Yminus y * r| ≤ y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hYm, abs_of_nonneg hr0, mul_assoc]
    nlinarith [abs_nonneg s, mul_nonneg hYm hr0]
  obtain ⟨hsl, hsr⟩ := abs_le.mp hsY
  -- the bracket as a non-negative combination of the absorption cross sections
  have hexp : (1 + G) * crossSectionBracket M s x Q2 y F1 F2 F3 =
      x * ((y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2 + s * Yminus y * r) * H.mat idxPlus idxPlus
        + (y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2 - s * Yminus y * r) * H.mat idxMinus idxMinus
        + 4 * (1 - y - G * y ^ 2 / 4) * H.mat idxLong idxLong) := by
    rw [crossSectionBracket_def, hMG, hplus, hminus]
    linear_combination (-2 * (1 - y - G * y ^ 2 / 4)) * hlong + (s * Yminus y * x * F3) * hr2
  have hcomb : 0 ≤ (1 + G) * crossSectionBracket M s x Q2 y F1 F2 F3 := by
    rw [hexp]
    apply mul_nonneg hx.le
    have h1 := mul_nonneg (show 0 ≤ y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2 + s * Yminus y * r by
      linarith) hp
    have h2 := mul_nonneg (show 0 ≤ y ^ 2 - 2 * y + 2 + G * y ^ 2 / 2 - s * Yminus y * r by
      linarith) hm
    have h3 := mul_nonneg (mul_nonneg zero_le_four hphys) hl
    linarith
  exact (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < 1 + G)).mp hcomb

/-- **The inclusive cross section is non-negative**: `crossSectionBracket_nonneg` scaled by a
non-negative flux factor. -/
theorem IsHelicityMatrixOf.dSigmaDxDQ2_nonneg {H : HelicityMatrix} {K M s x Q2 y F1 F2 F3 : ℝ}
    (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hK : 0 ≤ K) (hx : 0 < x) (hQ2 : 0 ≤ Q2)
    (hs : |s| ≤ 1) (hy : 0 ≤ y) (hphys : 0 ≤ 1 - y - M ^ 2 * x ^ 2 * y ^ 2 / Q2) :
    0 ≤ dSigmaDxDQ2 K M s x Q2 y F1 F2 F3 := by
  rw [dSigmaDxDQ2_def]
  have := h.crossSectionBracket_nonneg hx hQ2 hs hy hphys
  positivity

/-- **The reduced cross section is non-negative** in the physical region. -/
theorem IsHelicityMatrixOf.reducedCrossSection_nonneg {H : HelicityMatrix}
    {M s x Q2 y F1 F2 F3 : ℝ} (h : IsHelicityMatrixOf H M x Q2 F1 F2 F3) (hx : 0 < x)
    (hQ2 : 0 ≤ Q2) (hs : |s| ≤ 1) (hy : 0 ≤ y)
    (hphys : 0 ≤ 1 - y - M ^ 2 * x ^ 2 * y ^ 2 / Q2) :
    0 ≤ reducedCrossSection M s x Q2 y F1 F2 F3 := by
  rw [reducedCrossSection_def]
  have := h.crossSectionBracket_nonneg hx hQ2 hs hy hphys
  have := Yplus_pos y
  positivity

/-!
## The parity-even hadronic tensor

For a hadronic tensor in the transverse basis of `Tensors.Hadronic`, the transverse and
longitudinal entries of the helicity matrix are values of the tensor itself: on a spectator
direction `e`, `g`-orthogonal to `q` and to `p_T`, the tensor is `-(e·e) F₁`
(`Tensors.Hadronic.apply_self_of_isF1F2Decomposition_of_spectator`), and on the
longitudinal direction `p_T` it is `F_L^{exact}` up to the positive factor `(p_T·p_T) / (2 x)`
(`Tensors.Longitudinal.two_xBj_mul_apply_pTransverse`). Positivity of the tensor is then
equivalent to the existence of a helicity matrix with `F₃ = 0`.
-/

section Tensor

open Kinematics (Bilin DisKinematics)
open Tensors.Hadronic (IsF1F2Decomposition pTransverse transverseMetric_apply)

variable {V : Type} [AddCommGroup V] [Module ℝ V]

/-- **Positivity of a parity-even hadronic tensor is the existence of its helicity matrix.**
Let `W` be a tensor in the transverse basis with coefficients `F₁` and `F₂ / (p·q)`, in the
physical region `Q² > 0`, `x > 0` with real target mass `M`. Suppose the spectator subspace,
`g`-orthogonal to `q` and to `p_T`, is negative semidefinite (as
`Tensors.Hadronic.SpectatorAssumptions.definite` provides) and contains a spacelike direction
`e`. Then `W v v ≥ 0` for every `v` exactly when the structure functions `(F₁, F₂, 0)` are
represented by a positive-semidefinite helicity matrix. -/
theorem forall_apply_self_nonneg_iff_exists_isHelicityMatrixOf (g : Bilin V)
    (K : DisKinematics V) {W : Bilin V} (hSymm : g.IsSymm) (hQ2 : 0 < K.Q2 g)
    (hx : 0 < K.xBj g) {M : ℝ} (hM : g K.p K.p = M ^ 2)
    (hspec : ∀ u : V, g K.q u = 0 → g (pTransverse g K) u = 0 → g u u ≤ 0) {e : V}
    (hqe : g K.q e = 0) (hTe : g (pTransverse g K) e = 0) (hee : g e e < 0) {F1 F2c : ℝ}
    (hW : IsF1F2Decomposition g K W F1 F2c) :
    (∀ v, 0 ≤ W v v) ↔
      ∃ H, IsHelicityMatrixOf H M (K.xBj g) (K.Q2 g) F1 (structureF2 g K F2c) 0 := by
  rw [exists_isHelicityMatrixOf_iff hx, abs_zero, mul_zero,
    Tensors.Longitudinal.FLExact_nonneg_iff_apply_pTransverse_nonneg g K W hSymm hQ2 hM hx F1
      F2c hW]
  set T := pTransverse g K
  have hqq : g K.q K.q ≠ 0 := (Tensors.Hadronic.q_sq_ne_zero_iff g K).mpr hQ2.ne'
  have hpq := K.pq_ne_zero_of_xBj_ne_zero g hx.ne'
  have hTT : 0 < g T T :=
    Tensors.Longitudinal.pTransverse_self_pos g K hSymm hQ2 hpq (hM ▸ sq_nonneg M)
  have hTq : g T K.q = 0 := Tensors.Hadronic.pTransverse_orthogonal_q g K hqq
  have hqT : g K.q T = 0 := by rw [hSymm.eq, hTq]
  refine ⟨fun h => ⟨?_, h T⟩, fun ⟨hF1, hL⟩ v => ?_⟩
  · have := h e
    rw [Tensors.Hadronic.apply_self_of_isF1F2Decomposition_of_spectator g K hW hqe hTe] at this
    nlinarith
  -- split `v` into its `q`, `p_T` and spectator components
  set a := g K.q v / g K.q K.q
  set b := g T v / g T T
  set u := v - a • K.q - b • T
  have hqu : g K.q u = 0 := by
    simp only [u, map_sub, map_smul, smul_eq_mul, hqT, a]
    field_simp
    ring
  have hTu : g T u = 0 := by
    simp only [u, map_sub, map_smul, smul_eq_mul, hTq, b]
    field_simp
    ring
  have huu : g u u = g v v - g K.q v ^ 2 / g K.q K.q - g T v ^ 2 / g T T := by
    simp only [u, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      hqT, hTq, hSymm.eq v K.q, hSymm.eq v T, a, b]
    field_simp
    ring
  have hWT := Tensors.Longitudinal.apply_pTransverse_self g K W hSymm hqq F1 F2c hW
  have hWv : W v v = -F1 * g u u + b ^ 2 * W T T := by
    rw [hW, transverseMetric_apply, huu, hWT]
    simp only [b]
    field_simp
    ring
  rw [hWv]
  have := hspec u hqu hTu
  have : 0 ≤ W T T := hL
  nlinarith [sq_nonneg b, mul_nonneg (sq_nonneg b) this]

end Tensor

end Inclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
