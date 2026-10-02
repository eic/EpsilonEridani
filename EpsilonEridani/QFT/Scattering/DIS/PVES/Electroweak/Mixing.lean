/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak.Parameters
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Neutral-Gauge-Field Mixing and the Weak Mixing Angle

After electroweak symmetry breaking the two neutral gauge fields `W³` (of `SU(2)`, coupling `g`)
and `B` (of `U(1)`, coupling `g'`) acquire the mass-squared matrix `neutralMassMatrix g g' v`,
which in the basis `(W³, B)` is `(v²/4) u uᵀ` with `u = (g, -g')`. Here the Higgs doublet has
hypercharge `1` in the normalisation `Q = T³ + Y/2`, its vacuum expectation value is
`⟨φ⟩ = (0, v/√2)`, in the `T³ = -1/2` component, and the mass term is `½ Vᵀ M V`.

This module defines the rotation `mixingRotation θ` taking `(W³, B)` to `(Z, A)` with
`Z = cos θ W³ - sin θ B` and `A = sin θ W³ + cos θ B`, and the weak mixing angle
`weakMixingAngle g g' = arctan (g'/g)`. It proves that the two standard definitions of the
mixing angle agree: as the angle of the rotation that diagonalises the neutral mass matrix with
a massless photon, and as the angle whose tangent is the ratio `g'/g` of the gauge couplings.

## Main results

* `neutralMassMatrix_mulVec_eq_zero_iff`: for `v ≠ 0` and couplings not both zero there is
  exactly one massless combination of `W³` and `B`, the multiples of `g' W³ + g B`.
* `mixingRotation_conj_neutralMassMatrix_eq_diagonal_iff_mul_sin_eq`: the rotation by `θ`
  diagonalises the neutral mass matrix to `diag(v²(g² + g'²)/4, 0)`, with a massless photon, if
  and only if `g sin θ = g' cos θ`.
* `mul_sin_eq_mul_cos_iff_eq_weakMixingAngle`: for `g > 0` and `θ ∈ (-π/2, π/2)`,
  `g sin θ = g' cos θ` if and only if `θ = arctan (g'/g)`.
* `mixingRotation_conj_neutralMassMatrix_eq_diagonal_iff`: the two characterisations combined.
* `sin_weakMixingAngle`, `cos_weakMixingAngle`, `tan_weakMixingAngle`: the angle through the
  couplings, `sin θ_W = g'/√(g² + g'²)`, `cos θ_W = g/√(g² + g'²)`, `tan θ_W = g'/g`.
* `weakMixingConsistency_iff_sin2ThetaW_eq_sin_sq`: the tree-level weak-mixing contract
  `weakMixingConsistency` of `Parameters` says exactly that `sin2ThetaW` is `sin² θ_W`.

## References

* Particle Data Group, *Electroweak model and constraints on new physics*, §10.1.
* S. Weinberg, *A Model of Leptons*, Phys. Rev. Lett. 19 (1967) 1264.
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

open Matrix Real

/-!
## The neutral mass matrix
-/

/-- The mass-squared matrix `(v²/4) u uᵀ`, `u = (g, -g')`, of the neutral gauge fields in the
basis `(W³, B)`, for `SU(2)` coupling `g`, hypercharge coupling `g'` and Higgs vacuum expectation
value `v`. -/
def neutralMassMatrix (g g' v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (v ^ 2 / 4) • vecMulVec ![g, -g'] ![g, -g']

/-- The neutral mass matrix, entry by entry. -/
theorem neutralMassMatrix_eq (g g' v : ℝ) :
    neutralMassMatrix g g' v = (v ^ 2 / 4) • !![g ^ 2, -(g * g'); -(g * g'), g' ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [neutralMassMatrix, sq, mul_comm]

/-- The neutral mass matrix applied to a field configuration `w = (w₀, w₁)` in the basis
`(W³, B)`. -/
theorem neutralMassMatrix_mulVec (g g' v : ℝ) (w : Fin 2 → ℝ) :
    neutralMassMatrix g g' v *ᵥ w = ((v ^ 2 / 4) * (g * w 0 - g' * w 1)) • ![g, -g'] := by
  ext i
  fin_cases i <;> simp [neutralMassMatrix, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

/-- **Exactly one massless neutral combination.** For a nonzero vacuum expectation value and
couplings not both zero, a combination of `W³` and `B` is massless if and only if it is a
multiple of `g' W³ + g B`. -/
theorem neutralMassMatrix_mulVec_eq_zero_iff {g g' v : ℝ} (hv : v ≠ 0) (hg : g ≠ 0 ∨ g' ≠ 0)
    (w : Fin 2 → ℝ) :
    neutralMassMatrix g g' v *ᵥ w = 0 ↔ ∃ c : ℝ, w = c • ![g', g] := by
  have hu : ![g, -g'] ≠ 0 := by
    intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
      neg_eq_zero] at h0 h1
    tauto
  have hsq : g ^ 2 + g' ^ 2 ≠ 0 := by
    rcases hg with hg | hg <;> positivity
  rw [neutralMassMatrix_mulVec, smul_eq_zero, or_iff_left hu,
    mul_eq_zero, or_iff_right (by positivity)]
  constructor
  · intro h
    refine ⟨(g' * w 0 + g * w 1) / (g ^ 2 + g' ^ 2), ?_⟩
    ext i
    fin_cases i
    · simp
      field_simp
      linear_combination g * h
    · simp
      field_simp
      linear_combination -g' * h
  · rintro ⟨c, rfl⟩
    simp
    ring

/-!
## The mixing rotation
-/

/-- The rotation by `θ` from the gauge basis `(W³, B)` to the mass basis `(Z, A)`, with
`Z = cos θ W³ - sin θ B` and `A = sin θ W³ + cos θ B`. -/
def mixingRotation (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos θ, -sin θ; sin θ, cos θ]

/-- The mixing rotation, entry by entry. -/
theorem mixingRotation_eq (θ : ℝ) : mixingRotation θ = !![cos θ, -sin θ; sin θ, cos θ] := by
  rw [mixingRotation]

/-- The mixing rotation is a rotation: it is orthogonal and has determinant `1`. -/
theorem mixingRotation_mem_specialOrthogonalGroup (θ : ℝ) :
    mixingRotation θ ∈ specialOrthogonalGroup (Fin 2) ℝ := by
  rw [mem_specialOrthogonalGroup_iff, mem_orthogonalGroup_iff, mixingRotation_eq]
  refine ⟨?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;>
      nlinarith [sin_sq_add_cos_sq θ]
  · simp [det_fin_two]
    nlinarith [sin_sq_add_cos_sq θ]

/-- The neutral mass matrix in the basis rotated by `θ` is `(v²/4) w wᵀ`, where
`w = (g cos θ + g' sin θ, g sin θ - g' cos θ)` lists the couplings of the two rotated fields to
the Higgs vacuum. -/
theorem mixingRotation_conj_neutralMassMatrix (g g' v θ : ℝ) :
    mixingRotation θ * neutralMassMatrix g g' v * (mixingRotation θ)ᵀ =
      (v ^ 2 / 4) • vecMulVec ![g * cos θ + g' * sin θ, g * sin θ - g' * cos θ]
        ![g * cos θ + g' * sin θ, g * sin θ - g' * cos θ] := by
  rw [neutralMassMatrix_eq, mixingRotation_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring

/-- The photon mass-squared in the basis rotated by `θ`. -/
theorem mixingRotation_conj_neutralMassMatrix_one_one (g g' v θ : ℝ) :
    (mixingRotation θ * neutralMassMatrix g g' v * (mixingRotation θ)ᵀ) 1 1 =
      v ^ 2 / 4 * (g * sin θ - g' * cos θ) ^ 2 := by
  simp [mixingRotation_conj_neutralMassMatrix, sq]

/-- **The rotation that leaves the photon massless diagonalises the neutral mass matrix.** For a
nonzero vacuum expectation value, the rotation by `θ` brings the neutral mass matrix to
`diag(v²(g² + g'²)/4, 0)` if and only if `g sin θ = g' cos θ`. -/
theorem mixingRotation_conj_neutralMassMatrix_eq_diagonal_iff_mul_sin_eq {g g' v θ : ℝ}
    (hv : v ≠ 0) :
    mixingRotation θ * neutralMassMatrix g g' v * (mixingRotation θ)ᵀ =
        diagonal ![v ^ 2 * (g ^ 2 + g' ^ 2) / 4, 0] ↔
      g * sin θ = g' * cos θ := by
  constructor
  · intro h
    have h11 := mixingRotation_conj_neutralMassMatrix_one_one g g' v θ
    rw [h] at h11
    simp only [diagonal_apply_eq, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h11
    have : (g * sin θ - g' * cos θ) ^ 2 = 0 := by
      have hv4 : v ^ 2 / 4 ≠ 0 := by positivity
      exact (mul_eq_zero.mp h11.symm).resolve_left hv4
    linarith [pow_eq_zero_iff (n := 2) two_ne_zero |>.mp this]
  · intro h
    have hZ : (g * cos θ + g' * sin θ) ^ 2 = g ^ 2 + g' ^ 2 := by
      linear_combination (g ^ 2 + g' ^ 2) * sin_sq_add_cos_sq θ - (g * sin θ - g' * cos θ) * h
    rw [mixingRotation_conj_neutralMassMatrix]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h, ← sq, hZ]
    ring

/-!
## The weak mixing angle
-/

/-- The weak mixing angle `θ_W = arctan (g'/g)`, determined at tree level by the ratio of the
hypercharge coupling `g'` to the `SU(2)` coupling `g`. -/
def weakMixingAngle (g g' : ℝ) : ℝ := arctan (g' / g)

/-- The weak mixing angle is `arctan (g'/g)`. -/
theorem weakMixingAngle_eq (g g' : ℝ) : weakMixingAngle g g' = arctan (g' / g) := by
  rw [weakMixingAngle]

/-- The weak mixing angle lies in `(-π/2, π/2)`. -/
theorem weakMixingAngle_mem_Ioo (g g' : ℝ) :
    weakMixingAngle g g' ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  rw [weakMixingAngle_eq]
  exact ⟨neg_pi_div_two_lt_arctan _, arctan_lt_pi_div_two _⟩

/-- `tan θ_W = g'/g`. -/
theorem tan_weakMixingAngle (g g' : ℝ) : tan (weakMixingAngle g g') = g' / g := by
  rw [weakMixingAngle_eq, tan_arctan]

/-- `cos θ_W = g/√(g² + g'²)` for a positive `SU(2)` coupling. -/
theorem cos_weakMixingAngle {g : ℝ} (hg : 0 < g) (g' : ℝ) :
    cos (weakMixingAngle g g') = g / √(g ^ 2 + g' ^ 2) := by
  have hsqrt : √(1 + (g' / g) ^ 2) = √(g ^ 2 + g' ^ 2) / g := by
    rw [eq_div_iff hg.ne', ← sqrt_sq hg.le, ← sqrt_mul (by positivity), sqrt_sq hg.le]
    congr 1
    field_simp
  rw [weakMixingAngle_eq, cos_arctan, hsqrt, one_div_div]

/-- `sin θ_W = g'/√(g² + g'²)` for a positive `SU(2)` coupling. -/
theorem sin_weakMixingAngle {g : ℝ} (hg : 0 < g) (g' : ℝ) :
    sin (weakMixingAngle g g') = g' / √(g ^ 2 + g' ^ 2) := by
  have hcos : cos (weakMixingAngle g g') ≠ 0 :=
    (cos_pos_of_mem_Ioo (weakMixingAngle_mem_Ioo g g')).ne'
  rw [← div_mul_cancel₀ (sin _) hcos, ← tan_eq_sin_div_cos, tan_weakMixingAngle,
    cos_weakMixingAngle hg]
  field_simp

/-- `cos² θ_W = g²/(g² + g'²)` for a positive `SU(2)` coupling. -/
theorem cos_sq_weakMixingAngle {g : ℝ} (hg : 0 < g) (g' : ℝ) :
    cos (weakMixingAngle g g') ^ 2 = g ^ 2 / (g ^ 2 + g' ^ 2) := by
  rw [cos_weakMixingAngle hg, div_pow, sq_sqrt (by positivity)]

/-- `sin² θ_W = g'²/(g² + g'²)` for a positive `SU(2)` coupling. -/
theorem sin_sq_weakMixingAngle {g : ℝ} (hg : 0 < g) (g' : ℝ) :
    sin (weakMixingAngle g g') ^ 2 = g' ^ 2 / (g ^ 2 + g' ^ 2) := by
  rw [sin_weakMixingAngle hg, div_pow, sq_sqrt (by positivity)]

/-- **From the couplings to the angle.** For `g > 0` and `θ ∈ (-π/2, π/2)`, the relation
`g sin θ = g' cos θ` holds exactly at `θ = θ_W = arctan (g'/g)`. -/
theorem mul_sin_eq_mul_cos_iff_eq_weakMixingAngle {g g' θ : ℝ} (hg : 0 < g)
    (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    g * sin θ = g' * cos θ ↔ θ = weakMixingAngle g g' := by
  have hcos : 0 < cos θ := cos_pos_of_mem_Ioo hθ
  constructor
  · intro h
    rw [weakMixingAngle_eq, ← arctan_tan hθ.1 hθ.2, tan_eq_sin_div_cos]
    congr 1
    field_simp
    linarith
  · rintro rfl
    rw [sin_weakMixingAngle hg, cos_weakMixingAngle hg]
    ring

/-- **The two definitions of the weak mixing angle agree.** For a nonzero vacuum expectation
value, a positive `SU(2)` coupling and `θ ∈ (-π/2, π/2)`, the rotation by `θ` diagonalises the
neutral mass matrix to `diag(v²(g² + g'²)/4, 0)`, with a massless photon, if and only if
`θ = arctan (g'/g)`. -/
theorem mixingRotation_conj_neutralMassMatrix_eq_diagonal_iff {g g' v θ : ℝ} (hv : v ≠ 0)
    (hg : 0 < g) (hθ : θ ∈ Set.Ioo (-(π / 2)) (π / 2)) :
    mixingRotation θ * neutralMassMatrix g g' v * (mixingRotation θ)ᵀ =
        diagonal ![v ^ 2 * (g ^ 2 + g' ^ 2) / 4, 0] ↔
      θ = weakMixingAngle g g' := by
  rw [mixingRotation_conj_neutralMassMatrix_eq_diagonal_iff_mul_sin_eq hv,
    mul_sin_eq_mul_cos_iff_eq_weakMixingAngle hg hθ]

/-- The rotation by the weak mixing angle diagonalises the neutral mass matrix, leaving the
`Z` with mass-squared `v²(g² + g'²)/4` and the photon massless. -/
theorem mixingRotation_weakMixingAngle_conj_neutralMassMatrix {g : ℝ} (hg : 0 < g) (g' v : ℝ) :
    mixingRotation (weakMixingAngle g g') * neutralMassMatrix g g' v *
        (mixingRotation (weakMixingAngle g g'))ᵀ =
      diagonal ![v ^ 2 * (g ^ 2 + g' ^ 2) / 4, 0] := by
  rcases eq_or_ne v 0 with rfl | hv
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [neutralMassMatrix]
  · exact (mixingRotation_conj_neutralMassMatrix_eq_diagonal_iff hv hg
      (weakMixingAngle_mem_Ioo g g')).mpr rfl

/-- **The tree-level weak-mixing contract is `sin2ThetaW = sin² θ_W`.** For a parameter record
with positive `SU(2)` coupling, `weakMixingConsistency` holds if and only if its `sin2ThetaW` is
the squared sine of the weak mixing angle of its couplings. -/
theorem weakMixingConsistency_iff_sin2ThetaW_eq_sin_sq (P : Parameters) (hg : 0 < P.gSU2) :
    weakMixingConsistency P ↔ P.sin2ThetaW = sin (weakMixingAngle P.gSU2 P.gU1) ^ 2 := by
  rw [weakMixingConsistency, sin_sq_weakMixingAngle hg, eq_div_iff (by positivity)]

end EpsilonEridani.QFT.Scattering.DIS.PVES.Electroweak

end

end
