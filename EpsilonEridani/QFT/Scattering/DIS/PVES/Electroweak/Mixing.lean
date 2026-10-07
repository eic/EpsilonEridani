/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.DataStructures.Matrix.Rotation
public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.Parameters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Neutral-Gauge-Field Mixing and the Weak Mixing Angle

After electroweak symmetry breaking the two neutral gauge fields `W³` (of `SU(2)`, coupling `g`)
and `B` (of `U(1)`, coupling `g'`) acquire the mass-squared matrix `neutralMassMatrix g g' v`,
which in the basis `(W³, B)` is `(v²/4) u uᵀ` with `u = (g, -g')`. Here the Higgs doublet has
hypercharge `1` in the normalisation `Q = T³ + Y/2`, its vacuum expectation value is
`⟨φ⟩ = (0, v/√2)`, in the `T³ = -1/2` component, and the mass term is `½ Vᵀ M V`.

The plane rotation `Matrix.rotation θ` takes `(W³, B)` to `(Z, A)` with
`Z = cos θ W³ - sin θ B` and `A = sin θ W³ + cos θ B`. This module defines the weak mixing angle
`weakMixingAngle g g' = arctan (g'/g)` and proves that the two standard definitions of the
mixing angle agree: as the angle of the rotation that diagonalises the neutral mass matrix with
a massless photon, and as the angle whose tangent is the ratio `g'/g` of the gauge couplings.

## Main results

* `neutralMassMatrix_mulVec_eq_zero_iff`: for `v ≠ 0` and couplings not both zero there is
  exactly one massless combination of `W³` and `B`, the multiples of `g' W³ + g B`.
* `rotation_conj_neutralMassMatrix_eq_diagonal_iff_mul_sin_eq_mul_cos`: for `v ≠ 0`, the
  rotation by `θ` diagonalises the neutral mass matrix to `diag(v²(g² + g'²)/4, 0)`, with a
  massless photon, if and only if `g sin θ = g' cos θ`; the reverse direction,
  `rotation_conj_neutralMassMatrix_eq_diagonal_of_mul_sin_eq_mul_cos`, holds for every `v`.
* `mul_sin_eq_mul_cos_iff_eq_weakMixingAngle`: for `g ≠ 0` and `θ ∈ (-π/2, π/2)`,
  `g sin θ = g' cos θ` if and only if `θ = arctan (g'/g)`.
* `rotation_conj_neutralMassMatrix_eq_diagonal_iff`: the two characterisations combined.
* `tan_weakMixingAngle`: `tan θ_W = g'/g`; `sin_weakMixingAngle`, `cos_weakMixingAngle`: for
  `g > 0`, `sin θ_W = g'/√(g² + g'²)` and `cos θ_W = g/√(g² + g'²)`.
* `weakMixingConsistency_iff_sin2ThetaW_eq_sin_sq_weakMixingAngle`: for `gSU2 ≠ 0`, the
  tree-level weak-mixing contract `weakMixingConsistency` of `Parameters` says exactly that
  `sin2ThetaW` is `sin² θ_W`.

## References

* Particle Data Group, *Electroweak model and constraints on new physics*, §10.1.
* S. Weinberg, *A Model of Leptons*, Phys. Rev. Lett. 19 (1967) 1264.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace PVES
namespace Electroweak

open _root_.Matrix Real
open EpsilonEridani.Matrix (rotation rotation_def)

/-!
## The neutral mass matrix
-/

/-- The mass-squared matrix `(v²/4) u uᵀ`, `u = (g, -g')`, of the neutral gauge fields in the
basis `(W³, B)`, for `SU(2)` coupling `g`, hypercharge coupling `g'` and Higgs vacuum expectation
value `v`. -/
def neutralMassMatrix (g g' v : ℝ) : _root_.Matrix (Fin 2) (Fin 2) ℝ :=
  (v ^ 2 / 4) • vecMulVec ![g, -g'] ![g, -g']

/-- The neutral mass matrix is the rank-one matrix `(v²/4) u uᵀ` with `u = (g, -g')`. -/
theorem neutralMassMatrix_def (g g' v : ℝ) :
    neutralMassMatrix g g' v = (v ^ 2 / 4) • vecMulVec ![g, -g'] ![g, -g'] := by
  rw [neutralMassMatrix]

/-- The neutral mass matrix, entry by entry. -/
theorem neutralMassMatrix_eq_smul_fin_two (g g' v : ℝ) :
    neutralMassMatrix g g' v = (v ^ 2 / 4) • !![g ^ 2, -(g * g'); -(g * g'), g' ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neutralMassMatrix, sq, mul_comm]

/-- The neutral mass matrix applied to a field configuration `w = (w₀, w₁)` in the basis
`(W³, B)`. -/
@[simp]
theorem neutralMassMatrix_mulVec (g g' v : ℝ) (w : Fin 2 → ℝ) :
    neutralMassMatrix g g' v *ᵥ w = ((v ^ 2 / 4) * (g * w 0 - g' * w 1)) • ![g, -g'] := by
  ext i
  fin_cases i <;> simp [neutralMassMatrix_def, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Exactly one massless neutral combination.** For a nonzero vacuum expectation value and
couplings not both zero, a combination of `W³` and `B` is massless if and only if it is a
multiple of `g' W³ + g B`. -/
theorem neutralMassMatrix_mulVec_eq_zero_iff {g g' v : ℝ} (hv : v ≠ 0) (hg : g ≠ 0 ∨ g' ≠ 0)
    (w : Fin 2 → ℝ) :
    neutralMassMatrix g g' v *ᵥ w = 0 ↔ ∃ c : ℝ, w = c • ![g', g] := by
  have hu : ![g, -g'] ≠ 0 := by
    rw [cons_nonzero_iff, cons_nonzero_iff, neg_ne_zero]
    exact hg.imp_right Or.inl
  have hsq : g ^ 2 + g' ^ 2 ≠ 0 := by
    rcases hg with hg | hg <;> positivity
  rw [neutralMassMatrix_mulVec, smul_eq_zero, or_iff_left hu,
    mul_eq_zero, or_iff_right (by positivity)]
  constructor
  · intro h
    refine ⟨(g' * w 0 + g * w 1) / (g ^ 2 + g' ^ 2), ?_⟩
    ext i
    fin_cases i
    · simp only [Fin.zero_eta, Pi.smul_apply, cons_val_zero, smul_eq_mul]
      field_simp
      linear_combination g * h
    · simp only [Fin.mk_one, Pi.smul_apply, cons_val_one, cons_val_zero, smul_eq_mul]
      field_simp
      linear_combination -g' * h
  · rintro ⟨c, rfl⟩
    simp only [Pi.smul_apply, cons_val_zero, cons_val_one, smul_eq_mul]
    ring

/-!
## The mixing rotation
-/

/-- The neutral mass matrix in the basis rotated by `θ` is `(v²/4) w wᵀ`, where
`w = (g cos θ + g' sin θ, g sin θ - g' cos θ)` lists the couplings of the two rotated fields to
the Higgs vacuum. -/
theorem rotation_conj_neutralMassMatrix (g g' v θ : ℝ) :
    rotation θ * neutralMassMatrix g g' v * (rotation θ)ᵀ =
      (v ^ 2 / 4) • vecMulVec ![g * cos θ + g' * sin θ, g * sin θ - g' * cos θ]
        ![g * cos θ + g' * sin θ, g * sin θ - g' * cos θ] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [neutralMassMatrix_def, rotation_def, mul_apply, Fin.sum_univ_two, vecHead, vecTail] <;>
    ring

/-- The diagonal `(1,1)` entry of the neutral mass matrix in the basis rotated by `θ`, the
mass-squared coefficient of the second rotated field. It is the photon mass-squared exactly when
`g sin θ = g' cos θ`, where it vanishes. -/
theorem rotation_conj_neutralMassMatrix_one_one (g g' v θ : ℝ) :
    (rotation θ * neutralMassMatrix g g' v * (rotation θ)ᵀ) 1 1 =
      v ^ 2 / 4 * (g * sin θ - g' * cos θ) ^ 2 := by
  rw [rotation_conj_neutralMassMatrix]
  simp [sq]

/-- If `g sin θ = g' cos θ`, the rotation by `θ` brings the neutral mass matrix to
`diag(v²(g² + g'²)/4, 0)`, with the second rotated field massless. -/
theorem rotation_conj_neutralMassMatrix_eq_diagonal_of_mul_sin_eq_mul_cos {g g' v θ : ℝ}
    (h : g * sin θ = g' * cos θ) :
    rotation θ * neutralMassMatrix g g' v * (rotation θ)ᵀ =
      diagonal ![v ^ 2 * (g ^ 2 + g' ^ 2) / 4, 0] := by
  have hZ : (g * cos θ + g' * sin θ) * (g * cos θ + g' * sin θ) = g ^ 2 + g' ^ 2 := by
    linear_combination (g ^ 2 + g' ^ 2) * sin_sq_add_cos_sq θ - (g * sin θ - g' * cos θ) * h
  rw [rotation_conj_neutralMassMatrix, sub_eq_zero.mpr h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hZ, mul_div_right_comm]

/-- **The rotation that leaves the photon massless diagonalises the neutral mass matrix.** For a
nonzero vacuum expectation value, the rotation by `θ` brings the neutral mass matrix to
`diag(v²(g² + g'²)/4, 0)` if and only if `g sin θ = g' cos θ`. -/
theorem rotation_conj_neutralMassMatrix_eq_diagonal_iff_mul_sin_eq_mul_cos {g g' v θ : ℝ}
    (hv : v ≠ 0) :
    rotation θ * neutralMassMatrix g g' v * (rotation θ)ᵀ =
        diagonal ![v ^ 2 * (g ^ 2 + g' ^ 2) / 4, 0] ↔
      g * sin θ = g' * cos θ := by
  constructor
  · intro h
    have h11 := rotation_conj_neutralMassMatrix_one_one g g' v θ
    rw [h] at h11
    simp only [diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h11
    have : (g * sin θ - g' * cos θ) ^ 2 = 0 := by
      have hv4 : v ^ 2 / 4 ≠ 0 := by positivity
      exact (mul_eq_zero.mp h11.symm).resolve_left hv4
    linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this]
  · exact rotation_conj_neutralMassMatrix_eq_diagonal_of_mul_sin_eq_mul_cos

/-!
## The weak mixing angle
-/

/-- The weak mixing angle `θ_W = arctan (g'/g)`, determined at tree level by the ratio of the
hypercharge coupling `g'` to the `SU(2)` coupling `g`. The characterisation through the
diagonalising rotation holds for `g ≠ 0`, and the expressions `sin θ_W = g'/√(g² + g'²)`,
`cos θ_W = g/√(g² + g'²)` for `g > 0`; at `g = 0` the definition takes the junk value `0`. -/
def weakMixingAngle (g g' : ℝ) : ℝ := arctan (g' / g)

/-- The weak mixing angle is `arctan (g'/g)`. -/
theorem weakMixingAngle_def (g g' : ℝ) : weakMixingAngle g g' = arctan (g' / g) := by
  rw [weakMixingAngle]

/-- The weak mixing angle lies in `(-π/2, π/2)`. -/
theorem weakMixingAngle_mem_Ioo (g g' : ℝ) :
    weakMixingAngle g g' ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  rw [weakMixingAngle_def]
  exact arctan_mem_Ioo _

/-- `tan θ_W = g'/g`. -/
@[simp]
theorem tan_weakMixingAngle (g g' : ℝ) : tan (weakMixingAngle g g') = g' / g := by
  rw [weakMixingAngle_def, tan_arctan]

/-- `cos² θ_W = g²/(g² + g'²)` for a nonzero `SU(2)` coupling. -/
theorem cos_sq_weakMixingAngle {g : ℝ} (hg : g ≠ 0) (g' : ℝ) :
    cos (weakMixingAngle g g') ^ 2 = g ^ 2 / (g ^ 2 + g' ^ 2) := by
  rw [weakMixingAngle_def, cos_sq_arctan]
  field_simp

/-- `sin² θ_W = g'²/(g² + g'²)` for a nonzero `SU(2)` coupling. -/
theorem sin_sq_weakMixingAngle {g : ℝ} (hg : g ≠ 0) (g' : ℝ) :
    sin (weakMixingAngle g g') ^ 2 = g' ^ 2 / (g ^ 2 + g' ^ 2) := by
  rw [weakMixingAngle_def, sin_sq_arctan]
  field_simp

/-- `cos θ_W = g/√(g² + g'²)` for a positive `SU(2)` coupling. -/
theorem cos_weakMixingAngle {g : ℝ} (hg : 0 < g) (g' : ℝ) :
    cos (weakMixingAngle g g') = g / √(g ^ 2 + g' ^ 2) := by
  rw [← sqrt_sq (cos_pos_of_mem_Ioo (weakMixingAngle_mem_Ioo g g')).le,
    cos_sq_weakMixingAngle hg.ne', sqrt_div (sq_nonneg g), sqrt_sq hg.le]

/-- `sin θ_W = g'/√(g² + g'²)` for a positive `SU(2)` coupling. -/
theorem sin_weakMixingAngle {g : ℝ} (hg : 0 < g) (g' : ℝ) :
    sin (weakMixingAngle g g') = g' / √(g ^ 2 + g' ^ 2) := by
  have hs : 0 < √(g ^ 2 + g' ^ 2) := by positivity
  have ht := tan_weakMixingAngle g g'
  rw [tan_eq_sin_div_cos, cos_weakMixingAngle hg] at ht
  field_simp at ht ⊢
  linear_combination ht

/-- **From the couplings to the angle.** For `g ≠ 0` and `θ ∈ (-π/2, π/2)`, the relation
`g sin θ = g' cos θ` holds exactly at `θ = θ_W = arctan (g'/g)`. -/
theorem mul_sin_eq_mul_cos_iff_eq_weakMixingAngle {g g' θ : ℝ} (hg : g ≠ 0)
    (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    g * sin θ = g' * cos θ ↔ θ = weakMixingAngle g g' := by
  constructor
  · intro h
    rw [weakMixingAngle_def]
    refine (arctan_eq_of_tan_eq ?_ hθ).symm
    rw [tan_eq_sin_div_cos, div_eq_div_iff (cos_pos_of_mem_Ioo hθ).ne' hg]
    linear_combination h
  · rintro rfl
    have ht := tan_weakMixingAngle g g'
    rw [tan_eq_sin_div_cos,
      div_eq_div_iff (cos_pos_of_mem_Ioo (weakMixingAngle_mem_Ioo g g')).ne' hg] at ht
    linear_combination ht

/-- **The two definitions of the weak mixing angle agree.** For a nonzero vacuum expectation
value, a nonzero `SU(2)` coupling and `θ ∈ (-π/2, π/2)`, the rotation by `θ` diagonalises the
neutral mass matrix to `diag(v²(g² + g'²)/4, 0)`, with a massless photon, if and only if
`θ = arctan (g'/g)`. -/
theorem rotation_conj_neutralMassMatrix_eq_diagonal_iff {g g' v θ : ℝ} (hv : v ≠ 0)
    (hg : g ≠ 0) (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    rotation θ * neutralMassMatrix g g' v * (rotation θ)ᵀ =
        diagonal ![v ^ 2 * (g ^ 2 + g' ^ 2) / 4, 0] ↔
      θ = weakMixingAngle g g' := by
  rw [rotation_conj_neutralMassMatrix_eq_diagonal_iff_mul_sin_eq_mul_cos hv,
    mul_sin_eq_mul_cos_iff_eq_weakMixingAngle hg hθ]

/-- For a nonzero `SU(2)` coupling, the rotation by the weak mixing angle diagonalises the
neutral mass matrix, leaving the `Z` with mass-squared `v²(g² + g'²)/4` and the photon
massless. -/
theorem rotation_weakMixingAngle_conj_neutralMassMatrix_eq_diagonal {g : ℝ} (hg : g ≠ 0)
    (g' v : ℝ) :
    rotation (weakMixingAngle g g') * neutralMassMatrix g g' v *
        (rotation (weakMixingAngle g g'))ᵀ =
      diagonal ![v ^ 2 * (g ^ 2 + g' ^ 2) / 4, 0] :=
  rotation_conj_neutralMassMatrix_eq_diagonal_of_mul_sin_eq_mul_cos
    ((mul_sin_eq_mul_cos_iff_eq_weakMixingAngle hg (weakMixingAngle_mem_Ioo g g')).mpr rfl)

/-- **The tree-level weak-mixing contract is `sin2ThetaW = sin² θ_W`.** For a parameter record
with nonzero `SU(2)` coupling, `weakMixingConsistency` holds if and only if its `sin2ThetaW` is
the squared sine of the weak mixing angle of its couplings. -/
theorem weakMixingConsistency_iff_sin2ThetaW_eq_sin_sq_weakMixingAngle (P : Parameters)
    (hg : P.gSU2 ≠ 0) :
    weakMixingConsistency P ↔ P.sin2ThetaW = sin (weakMixingAngle P.gSU2 P.gU1) ^ 2 := by
  rw [weakMixingConsistency, sin_sq_weakMixingAngle hg, eq_div_iff (by positivity)]

end Electroweak
end PVES
end DIS
end Scattering
end QFT
end EpsilonEridani

end

end
