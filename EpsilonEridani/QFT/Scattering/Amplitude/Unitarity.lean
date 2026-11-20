/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import EpsilonEridani.Mathematics.LinearAlgebra.UnitaryGroup

/-!
# Unitarity of a partial-wave amplitude

Fix a partial wave and a finite set `n` of open two-body channels, the channel `i` carrying the
real phase-space factor `ρ i > 0`. The partial-wave S-matrix and T-matrix are related by

`S = 1 + 2 i √ρ T √ρ`,

where `√ρ` is the diagonal matrix of the square roots of the phase-space factors. Conservation of
probability is the unitarity of `S`. This file proves the equivalent forms of that condition on `T`
which amplitude analysis works with:

* `T - Tᴴ = 2 i Tᴴ ρ T`, the form quadratic in `T`;
* `T⁻¹ - (T⁻¹)ᴴ = -2 i ρ`, i.e. `Im T⁻¹ = -ρ` for the imaginary part
  `Im M = (M - Mᴴ) / 2i`, wherever `T` is invertible. This form is linear in `T⁻¹`, and it says
  that `T⁻¹ + i ρ` is Hermitian: this Hermitian matrix is the inverse of the K-matrix.

For a single elastic channel the S-matrix is the complex number `S = 1 + 2 i ρ t`, and unitarity
is `|S| = 1`. It is equivalent to the amplitude `t` lying on the Argand circle
`|t - i / 2ρ| = 1 / 2ρ`, it implies the unitarity bound `|t| ≤ 1 / ρ`, and it is equivalent to the
existence of a real phase shift `δ` with `t = e^{iδ} sin δ / ρ` and `S = e^{2iδ}`. The phase shift
is determined by `t` modulo `π`.

## Main definitions

* `sMatrix ρ T`: the partial-wave S-matrix `1 + 2 i √ρ T √ρ` of a T-matrix.
* `elasticSMatrix ρ t`: the single-channel S-matrix `1 + 2 i ρ t`.
* `phaseShiftAmplitude ρ δ`: the single-channel amplitude `e^{iδ} sin δ / ρ` of a phase shift
  `δ : ℂ`; a real `δ` is the elastic case and `Im δ > 0` describes absorption.

## Main results

* `sMatrix_mem_unitaryGroup_iff`: `S` is unitary iff `T - Tᴴ = 2 i Tᴴ ρ T`.
* `sMatrix_mem_unitaryGroup_iff_inv`: for invertible `T`, `S` is unitary iff
  `T⁻¹ - (T⁻¹)ᴴ = -2 i ρ`.
* `sMatrix_mem_unitaryGroup_iff_isHermitian`: for invertible `T`, `S` is unitary iff `T⁻¹ + i ρ`
  is Hermitian.
* `norm_elasticSMatrix`: `|S| = 2ρ |t - i / 2ρ|`, the distance from the centre of the Argand circle.
* `norm_elasticSMatrix_eq_one_iff_norm_sub_eq`: single-channel unitarity is the Argand circle.
* `sMatrix_apply_same_eq_elasticSMatrix`: a diagonal entry of `sMatrix` is a single-channel
  S-matrix.
* `sMatrix_mem_unitaryGroup_iff_norm_elasticSMatrix_eq_one`: with one channel, unitarity of
  `sMatrix` is `|S| = 1` for the single-channel S-matrix.
* `norm_elasticSMatrix_le_one_iff_norm_sub_le`: `|S| ≤ 1` is the disc bounded by the Argand circle.
* `norm_elasticSMatrix_eq_one_iff_im_eq_mul_normSq`: single-channel unitarity is `Im t = ρ |t|²`.
* `norm_le_one_div_of_norm_elasticSMatrix_le_one`: the unitarity bound `|t| ≤ 1 / ρ`, for `|S| ≤ 1`.
* `norm_elasticSMatrix_eq_one_iff_inv_im_eq_neg`: single-channel unitarity is `Im t⁻¹ = -ρ`.
* `norm_elasticSMatrix_eq_one_iff_exists_real_phaseShiftAmplitude`: single-channel unitarity is
  the existence of a real phase shift, and
  `phaseShiftAmplitude_eq_phaseShiftAmplitude_iff_exists_int` its uniqueness modulo `π`.
* `elasticSMatrix_eq_iff`: the amplitude is read off the S-matrix as `t = (S - 1) / 2iρ`.
* `norm_elasticSMatrix_phaseShiftAmplitude`: a complex phase shift `δ` gives `|S| = e^{-2 Im δ}`.

## References

* R. J. Eden, P. V. Landshoff, D. I. Olive and J. C. Polkinghorne, *The Analytic S-Matrix*,
  Cambridge University Press (1966).
* I. J. R. Aitchison, "The K-matrix formalism for overlapping resonances", *Nucl. Phys.* A189
  (1972) 417.
* S. U. Chung, J. Brose, R. Hackmann, E. Klempt, S. Spanier and C. Strassburger, "Partial wave
  analysis in K-matrix formalism", *Ann. Phys. (Leipzig)* 4 (1995) 404.
-/

public section

namespace EpsilonEridani.QFT.Scattering.Amplitude

open Complex Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The multichannel S-matrix -/

/-- The partial-wave S-matrix `S = 1 + 2 i √ρ T √ρ` of the T-matrix `T`, for the open channels `n`
with phase-space factors `ρ`. -/
noncomputable def sMatrix (ρ : n → ℝ) (T : Matrix n n ℂ) : Matrix n n ℂ :=
  1 + (2 * I) • (diagonal (fun i ↦ (√(ρ i) : ℂ)) * T * diagonal (fun i ↦ (√(ρ i) : ℂ)))

theorem sMatrix_def (ρ : n → ℝ) (T : Matrix n n ℂ) :
    sMatrix ρ T =
      1 + (2 * I) • (diagonal (fun i ↦ (√(ρ i) : ℂ)) * T * diagonal (fun i ↦ (√(ρ i) : ℂ))) :=
  (rfl)

@[simp]
theorem sMatrix_zero (ρ : n → ℝ) : sMatrix ρ 0 = 1 := by
  simp [sMatrix_def]

theorem sMatrix_apply (ρ : n → ℝ) (T : Matrix n n ℂ) (i j : n) :
    sMatrix ρ T i j = (1 : Matrix n n ℂ) i j + 2 * I * √(ρ i) * T i j * √(ρ j) := by
  rw [sMatrix_def, Matrix.add_apply, Matrix.smul_apply, mul_diagonal, diagonal_mul, smul_eq_mul]
  ring

/-- **Unitarity in quadratic form.** For positive phase-space factors, the partial-wave S-matrix is
unitary iff `T - Tᴴ = 2 i Tᴴ ρ T`. -/
theorem sMatrix_mem_unitaryGroup_iff {ρ : n → ℝ} (hρ : ∀ i, 0 < ρ i) (T : Matrix n n ℂ) :
    sMatrix ρ T ∈ unitaryGroup n ℂ ↔
      T - Tᴴ = (2 * I) • (Tᴴ * diagonal (fun i ↦ (ρ i : ℂ)) * T) := by
  set R := diagonal (fun i ↦ (√(ρ i) : ℂ))
  have hRH : Rᴴ = R := by simp [R, diagonal_conjTranspose, Pi.star_def]
  have hRR : R * R = diagonal (fun i ↦ (ρ i : ℂ)) := by
    rw [diagonal_mul_diagonal]
    congr 1
    ext i
    rw [← ofReal_mul, Real.mul_self_sqrt (hρ i).le]
  have hR : IsUnit R :=
    isUnit_diagonal.2 (Pi.isUnit_iff.2 fun i ↦ (ofReal_ne_zero.2
      (Real.sqrt_pos.2 (hρ i)).ne').isUnit)
  -- `Sᴴ S = 1 + 2 i R (T - Tᴴ - 2 i Tᴴ R² T) R`, and `R` is invertible.
  have key : (sMatrix ρ T)ᴴ * sMatrix ρ T =
      1 + (2 * I) • (R * (T - Tᴴ - (2 * I) • (Tᴴ * (R * R) * T)) * R) := by
    have hc : star (2 * I) = -(2 * I) := by simp
    rw [sMatrix_def, conjTranspose_add, conjTranspose_one, conjTranspose_smul, conjTranspose_mul,
      conjTranspose_mul, hRH, hc]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    module
  rw [mem_unitaryGroup_iff', star_eq_conjTranspose, key, add_eq_left, smul_eq_zero,
    or_iff_right (by simp), hR.mul_left_eq_zero, hR.mul_right_eq_zero, sub_eq_zero, hRR]

/-- **Unitarity in inverse form.** For positive phase-space factors and an invertible `T`, the
partial-wave S-matrix is unitary iff `Im T⁻¹ = -ρ`, where `Im M = (M - Mᴴ) / 2i`. -/
theorem sMatrix_mem_unitaryGroup_iff_inv {ρ : n → ℝ} (hρ : ∀ i, 0 < ρ i) {T : Matrix n n ℂ}
    (hT : IsUnit T.det) :
    sMatrix ρ T ∈ unitaryGroup n ℂ ↔
      T⁻¹ - (T⁻¹)ᴴ = -(2 * I) • diagonal (fun i ↦ (ρ i : ℂ)) := by
  set D := diagonal (fun i ↦ (ρ i : ℂ))
  have hTH : IsUnit Tᴴ.det := by rwa [det_conjTranspose, isUnit_star]
  rw [sMatrix_mem_unitaryGroup_iff hρ, conjTranspose_nonsing_inv]
  -- Multiply by `(Tᴴ)⁻¹` on the left and `T⁻¹` on the right, and back by `Tᴴ` and `T`.
  have hu : IsUnit Tᴴ ↔ IsUnit T :=
    iff_of_true ((isUnit_iff_isUnit_det _).2 hTH) ((isUnit_iff_isUnit_det _).2 hT)
  have hu' : IsUnit Tᴴ⁻¹ ↔ IsUnit T⁻¹ :=
    iff_of_true ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hTH))
      ((isUnit_iff_isUnit_det _).2 (isUnit_nonsing_inv_det _ hT))
  constructor
  · intro h
    calc T⁻¹ - Tᴴ⁻¹ = -(Tᴴ⁻¹ * (T - Tᴴ) * T⁻¹) := by rw [← inv_sub_inv hu, neg_sub]
      _ = -(2 * I) • D := by
          rw [h, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc Tᴴ,
            nonsing_inv_mul_cancel_left _ _ hTH, mul_nonsing_inv_cancel_right _ _ hT, neg_smul]
  · intro h
    calc T - Tᴴ = -(Tᴴ * (T⁻¹ - Tᴴ⁻¹) * T) := by
          have := inv_sub_inv hu'
          rw [nonsing_inv_nonsing_inv _ hTH, nonsing_inv_nonsing_inv _ hT] at this
          rw [← this, neg_sub]
      _ = (2 * I) • (Tᴴ * D * T) := by
          rw [h, Matrix.mul_smul, Matrix.smul_mul, neg_smul, neg_neg]

/-- **Unitarity as Hermiticity of `T⁻¹ + i ρ`.** For positive phase-space factors and an
invertible `T`, the partial-wave S-matrix is unitary iff `T⁻¹ + i ρ` is Hermitian; this Hermitian
matrix is the inverse of the K-matrix. -/
theorem sMatrix_mem_unitaryGroup_iff_isHermitian {ρ : n → ℝ} (hρ : ∀ i, 0 < ρ i)
    {T : Matrix n n ℂ} (hT : IsUnit T.det) :
    sMatrix ρ T ∈ unitaryGroup n ℂ ↔ (T⁻¹ + I • diagonal (fun i ↦ (ρ i : ℂ))).IsHermitian := by
  have hD : (diagonal (fun i ↦ (ρ i : ℂ)))ᴴ = diagonal (fun i ↦ (ρ i : ℂ)) := by
    simp [diagonal_conjTranspose, Pi.star_def]
  rw [sMatrix_mem_unitaryGroup_iff_inv hρ hT, IsHermitian, conjTranspose_add, conjTranspose_smul,
    hD, star_def, conj_I]
  constructor <;> intro h <;> linear_combination (norm := module) -h

/-! ### A single elastic channel -/

/-- The S-matrix `S = 1 + 2 i ρ t` of a single channel with phase-space factor `ρ` and partial-wave
amplitude `t`. -/
def elasticSMatrix (ρ : ℝ) (t : ℂ) : ℂ :=
  1 + 2 * I * ρ * t

theorem elasticSMatrix_def (ρ : ℝ) (t : ℂ) : elasticSMatrix ρ t = 1 + 2 * I * ρ * t :=
  (rfl)

@[simp]
theorem elasticSMatrix_zero (ρ : ℝ) : elasticSMatrix ρ 0 = 1 := by
  simp [elasticSMatrix_def]

/-- A diagonal entry `S i i` of the partial-wave S-matrix is the single-channel S-matrix of the
diagonal amplitude `T i i` with the phase-space factor of channel `i`. -/
theorem sMatrix_apply_same_eq_elasticSMatrix {ρ : n → ℝ} {i : n} (hρ : 0 ≤ ρ i)
    (T : Matrix n n ℂ) : sMatrix ρ T i i = elasticSMatrix (ρ i) (T i i) := by
  rw [sMatrix_apply, elasticSMatrix_def, one_apply_eq, mul_right_comm _ (T i i),
    mul_assoc (2 * I), ← ofReal_mul, Real.mul_self_sqrt hρ]

/-- **One-channel unitarity.** With a single channel, the partial-wave S-matrix is unitary iff the
single-channel S-matrix has modulus one. -/
theorem sMatrix_mem_unitaryGroup_iff_norm_elasticSMatrix_eq_one [Unique n] {ρ : n → ℝ}
    (hρ : 0 ≤ ρ default) (T : Matrix n n ℂ) :
    sMatrix ρ T ∈ unitaryGroup n ℂ ↔ ‖elasticSMatrix (ρ default) (T default default)‖ = 1 := by
  rw [mem_unitaryGroup_iff_norm_apply_default_eq_one, sMatrix_apply_same_eq_elasticSMatrix hρ]

/-- The single-channel S-matrix is `2 i ρ` times the displacement of `t` from the centre `i / 2ρ` of
the Argand circle. -/
theorem elasticSMatrix_eq_mul_sub {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℂ) :
    elasticSMatrix ρ t = 2 * I * ρ * (t - I / (2 * ρ)) := by
  have h : 2 * I * ρ * (I / (2 * ρ)) = -1 := by
    rw [mul_div_assoc', div_eq_iff (by simp [hρ])]
    linear_combination (2 * ρ : ℂ) * I_sq
  rw [elasticSMatrix_def, mul_sub, h, sub_neg_eq_add, add_comm]

/-- The modulus of the single-channel S-matrix is `2ρ` times the distance of `t` from the centre
`i / 2ρ` of the Argand circle. -/
theorem norm_elasticSMatrix {ρ : ℝ} (hρ : 0 < ρ) (t : ℂ) :
    ‖elasticSMatrix ρ t‖ = 2 * ρ * ‖t - I / (2 * ρ)‖ := by
  rw [elasticSMatrix_eq_mul_sub hρ.ne', norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_two,
    norm_real, Real.norm_of_nonneg hρ.le, mul_one]

/-- **The Argand circle.** For a single channel with `ρ > 0`, unitarity `|S| = 1` holds iff the
amplitude lies on the circle of radius `1 / 2ρ` about `i / 2ρ`. -/
theorem norm_elasticSMatrix_eq_one_iff_norm_sub_eq {ρ : ℝ} (hρ : 0 < ρ) (t : ℂ) :
    ‖elasticSMatrix ρ t‖ = 1 ↔ ‖t - I / (2 * ρ)‖ = 1 / (2 * ρ) := by
  rw [norm_elasticSMatrix hρ, eq_div_iff (by positivity), mul_comm]

/-- **The unitarity disc.** For a single channel with `ρ > 0`, `|S| ≤ 1` holds iff the amplitude
lies in the closed disc bounded by the Argand circle. -/
theorem norm_elasticSMatrix_le_one_iff_norm_sub_le {ρ : ℝ} (hρ : 0 < ρ) (t : ℂ) :
    ‖elasticSMatrix ρ t‖ ≤ 1 ↔ ‖t - I / (2 * ρ)‖ ≤ 1 / (2 * ρ) := by
  rw [norm_elasticSMatrix hρ, le_div_iff₀ (by positivity), mul_comm]

/-- The squared modulus of the single-channel S-matrix: `|S|² = 1 + 4 ρ (ρ |t|² - Im t)`. -/
theorem normSq_elasticSMatrix (ρ : ℝ) (t : ℂ) :
    normSq (elasticSMatrix ρ t) = 1 + 4 * ρ * (ρ * normSq t - t.im) := by
  rw [elasticSMatrix_def, normSq_apply, normSq_apply]
  simp only [add_re, one_re, mul_re, re_ofNat, I_re, im_ofNat, I_im, ofReal_re, ofReal_im,
    add_im, one_im, mul_im]
  ring

/-- Single-channel unitarity in quadratic form: `|S| = 1` iff `Im t = ρ |t|²`. -/
theorem norm_elasticSMatrix_eq_one_iff_im_eq_mul_normSq {ρ : ℝ} (hρ : ρ ≠ 0) (t : ℂ) :
    ‖elasticSMatrix ρ t‖ = 1 ↔ t.im = ρ * normSq t := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, ← normSq_eq_norm_sq,
    normSq_elasticSMatrix, add_eq_left, mul_eq_zero, or_iff_right (mul_ne_zero four_ne_zero hρ),
    sub_eq_zero, eq_comm]

/-- **The unitarity bound.** A single-channel amplitude with `|S| ≤ 1`, in particular a unitary
one, satisfies `|t| ≤ 1 / ρ`. -/
theorem norm_le_one_div_of_norm_elasticSMatrix_le_one {ρ : ℝ} (hρ : 0 < ρ) {t : ℂ}
    (ht : ‖elasticSMatrix ρ t‖ ≤ 1) : ‖t‖ ≤ 1 / ρ := by
  have hc : ‖I / (2 * ρ)‖ = 1 / (2 * ρ) := by simp [hρ.le]
  calc ‖t‖ = ‖(t - I / (2 * ρ)) + I / (2 * ρ)‖ := by rw [sub_add_cancel]
    _ ≤ ‖t - I / (2 * ρ)‖ + ‖I / (2 * ρ)‖ := norm_add_le _ _
    _ ≤ 1 / (2 * ρ) + 1 / (2 * ρ) := by
      rw [hc]
      exact add_le_add_left ((norm_elasticSMatrix_le_one_iff_norm_sub_le hρ t).1 ht) _
    _ = 1 / ρ := by ring

/-- **Single-channel unitarity in inverse form.** For a non-zero amplitude, `|S| = 1` iff
`Im t⁻¹ = -ρ`. -/
theorem norm_elasticSMatrix_eq_one_iff_inv_im_eq_neg {ρ : ℝ} (hρ : ρ ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    ‖elasticSMatrix ρ t‖ = 1 ↔ t⁻¹.im = -ρ := by
  have hn : normSq t ≠ 0 := normSq_eq_zero.not.2 ht
  rw [norm_elasticSMatrix_eq_one_iff_im_eq_mul_normSq hρ, inv_im, neg_div, neg_inj, div_eq_iff hn]

/-- For `ρ ≠ 0` the single-channel S-matrix determines the amplitude. -/
theorem elasticSMatrix_injective {ρ : ℝ} (hρ : ρ ≠ 0) : Function.Injective (elasticSMatrix ρ) := by
  intro u v h
  have : (2 * I * ρ : ℂ) ≠ 0 := by simp [hρ]
  rwa [elasticSMatrix_def, elasticSMatrix_def, add_right_inj, mul_right_inj' this] at h

/-- For `ρ ≠ 0` the amplitude is read off the single-channel S-matrix as `t = (S - 1) / 2iρ`. -/
theorem elasticSMatrix_eq_iff {ρ : ℝ} (hρ : ρ ≠ 0) {t s : ℂ} :
    elasticSMatrix ρ t = s ↔ t = (s - 1) / (2 * I * ρ) := by
  have : (2 * I * ρ : ℂ) ≠ 0 := by simp [hρ]
  rw [elasticSMatrix_def, eq_div_iff this, eq_sub_iff_add_eq', mul_comm t]

/-- The partial-wave amplitude `e^{iδ} sin δ / ρ` of phase shift `δ`, for a single channel with
phase-space factor `ρ`. The phase shift is real for an elastic channel; a complex `δ` with
`Im δ > 0` describes absorption. -/
noncomputable def phaseShiftAmplitude (ρ : ℝ) (δ : ℂ) : ℂ :=
  exp (δ * I) * sin δ / ρ

theorem phaseShiftAmplitude_def (ρ : ℝ) (δ : ℂ) :
    phaseShiftAmplitude ρ δ = exp (δ * I) * sin δ / ρ :=
  (rfl)

@[simp]
theorem phaseShiftAmplitude_zero (ρ : ℝ) : phaseShiftAmplitude ρ 0 = 0 := by
  simp [phaseShiftAmplitude_def]

/-- The amplitude of phase shift `δ` has S-matrix `e^{2iδ}`. -/
@[simp]
theorem elasticSMatrix_phaseShiftAmplitude {ρ : ℝ} (hρ : ρ ≠ 0) (δ : ℂ) :
    elasticSMatrix ρ (phaseShiftAmplitude ρ δ) = exp (2 * δ * I) := by
  have : (ρ : ℂ) ≠ 0 := ofReal_ne_zero.2 hρ
  rw [elasticSMatrix_def, phaseShiftAmplitude_def, mul_div_assoc', mul_right_comm (2 * I) (ρ : ℂ),
    mul_div_cancel_right₀ _ this]
  have h1 : exp (δ * I) * exp (-δ * I) = 1 := by rw [← exp_add, neg_mul, add_neg_cancel, exp_zero]
  have h2 : exp (2 * δ * I) = exp (δ * I) * exp (δ * I) := by rw [← exp_add]; congr 1; ring
  -- `2 i e^{iδ} sin δ = i e^{iδ} (e^{-iδ} - e^{iδ}) i = e^{2iδ} - 1`, by `two_sin`, `i² = -1`,
  -- `e^{iδ} e^{-iδ} = 1` and `e^{2iδ} = (e^{iδ})²`.
  linear_combination (I * exp (δ * I)) * two_sin δ +
    (exp (δ * I) * exp (-δ * I) - exp (δ * I) * exp (δ * I)) * I_sq - h1 - h2

/-- The single-channel S-matrix of the amplitude of a complex phase shift `δ` has modulus
`e^{-2 Im δ}`: it is unitary for real `δ`, and `Im δ > 0` describes absorption. -/
theorem norm_elasticSMatrix_phaseShiftAmplitude {ρ : ℝ} (hρ : ρ ≠ 0) (δ : ℂ) :
    ‖elasticSMatrix ρ (phaseShiftAmplitude ρ δ)‖ = Real.exp (-2 * δ.im) := by
  rw [elasticSMatrix_phaseShiftAmplitude hρ, norm_exp]
  simp

/-- **The phase shift.** For a single channel, `|S| = 1` iff the amplitude is `e^{iδ} sin δ / ρ`
for some real phase shift `δ`. -/
theorem norm_elasticSMatrix_eq_one_iff_exists_real_phaseShiftAmplitude {ρ : ℝ} (hρ : ρ ≠ 0)
    (t : ℂ) :
    ‖elasticSMatrix ρ t‖ = 1 ↔ ∃ δ : ℝ, t = phaseShiftAmplitude ρ δ := by
  constructor
  · intro h
    -- `S = e^{i arg S}` since `|S| = 1`, so `δ = arg S / 2`.
    refine ⟨arg (elasticSMatrix ρ t) / 2, elasticSMatrix_injective hρ ?_⟩
    rw [elasticSMatrix_phaseShiftAmplitude hρ]
    conv_lhs => rw [← norm_mul_exp_arg_mul_I (elasticSMatrix ρ t), h]
    push_cast
    rw [one_mul]
    congr 1
    ring
  · rintro ⟨δ, rfl⟩
    rw [elasticSMatrix_phaseShiftAmplitude hρ, ← ofReal_ofNat, ← ofReal_mul,
      norm_exp_ofReal_mul_I]

/-- **The phase shift is determined modulo `π`.** Two phase shifts give the same amplitude iff they
differ by an integer multiple of `π`. -/
theorem phaseShiftAmplitude_eq_phaseShiftAmplitude_iff_exists_int {ρ : ℝ} (hρ : ρ ≠ 0)
    (δ δ' : ℂ) :
    phaseShiftAmplitude ρ δ = phaseShiftAmplitude ρ δ' ↔ ∃ k : ℤ, δ = δ' + k * Real.pi := by
  rw [← (elasticSMatrix_injective hρ).eq_iff, elasticSMatrix_phaseShiftAmplitude hρ,
    elasticSMatrix_phaseShiftAmplitude hρ, exp_eq_exp_iff_exists_int]
  refine exists_congr fun k ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have : (2 * I : ℂ) ≠ 0 := by simp
    apply mul_left_cancel₀ this
    linear_combination h
  · rw [h]; ring

/-- **A real phase shift is determined modulo `π`.** Two real phase shifts give the same amplitude
iff they differ by an integer multiple of `π`. -/
theorem phaseShiftAmplitude_ofReal_eq_ofReal_iff_exists_int {ρ : ℝ} (hρ : ρ ≠ 0) (δ δ' : ℝ) :
    phaseShiftAmplitude ρ δ = phaseShiftAmplitude ρ δ' ↔ ∃ k : ℤ, δ = δ' + k * Real.pi := by
  rw [phaseShiftAmplitude_eq_phaseShiftAmplitude_iff_exists_int hρ]
  exact exists_congr fun k ↦ by norm_cast

end EpsilonEridani.QFT.Scattering.Amplitude
