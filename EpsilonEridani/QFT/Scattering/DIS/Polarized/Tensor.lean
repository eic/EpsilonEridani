/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Polarized.Basic
public import EpsilonEridani.QFT.Scattering.DIS.Polarized.Kinematics
public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.TargetMass
public import EpsilonEridani.Mathematics.LinearAlgebra.Alternating.BilinMap

/-!
# The antisymmetric hadronic tensor of polarised DIS

The spin-dependent part of the hadronic tensor is antisymmetric. With the factor `i` divided
out it is a real alternating bilinear form, decomposed on the two covariant structures

- `E₁(v, w) = ε(v, w, q, S)` (`spinStructureOne`),
- `E₂(v, w) = ε(v, w, q, (p·q) S − (S·q) p)` (`spinStructureTwo`),

built from an alternating four-form `ε`, the momentum transfer `q`, the hadron momentum `p` and
the spin vector `S` of `PolarizedKinematics`. Both are alternating, so they satisfy
`TensorAssumptions` by `tensorAssumptions_iff_isAlt`, and both are conserved: they vanish when
either argument is `q`.

`fromG1G2 ε K c₁ c₂ = c₁ • E₁ + c₂ • E₂` is the tensor with given coefficients, and
`IsG1G2Decomposition ε K G W` says that `W` is the tensor whose coefficients are
`(M / (p·q)) · g₁(x, Q²)` and `(1 / (M (p·q))) · g₂(x, Q²)` at the kinematic point of `K`, with
`M = √(p·p)` the target mass. These are the antisymmetric counterparts of
`Tensors.Hadronic.IsF1F2Decomposition` and `Tensors.Hadronic.fromF1F2`.
`exists_fromG1G2_ne_zero` exhibits Minkowski kinematics on `ℝ⁴` on which `E₁` and `E₂` are
linearly independent, so neither structure is identically zero.

## Orientation

An abstract `V` carrying only a bilinear form has no volume form, so the four-form `ε` is
explicit data, as for `Tensors.Leptonic.lMuNuOdd`. Both structures are linear in `ε`:
replacing `ε` by `-ε` flips the sign of both coefficients, and of every asymmetry built from
them, so these signs are meaningful only once `ε` is fixed.

## Not included

On a four-dimensional `V` with `p`, `q`, `S` linearly independent and `Q² ≠ 0`, the alternating
forms that are conserved in both slots *and linear in `S`* form a two-dimensional space spanned
by `E₁` and `E₂`; the alternating, `S`-linear candidate `ε(v, w, p, S)` is excluded because it is
not conserved. Neither this uniqueness statement nor the resulting uniqueness of the
coefficients `g₁`, `g₂` is proved here. Without the restriction to `S`-linear forms the count is
wrong: the alternating forms vanishing on `q` already form a three-dimensional space.

## References

* M. Anselmino, A. Efremov and E. Leader, *The theory and phenomenology of polarized deep
  inelastic scattering*, Phys. Rept. **261** (1995) 1; arXiv:hep-ph/9501369, §§2–3.
* A. V. Manohar, *An introduction to spin dependent deep inelastic scattering*,
  arXiv:hep-ph/9204208, §§2–3.
* M. Lampe and E. Reya, *Spin physics and polarized structure functions*, Phys. Rept. **332**
  (2000) 1; arXiv:hep-ph/9810270, §2.
-/

@[expose] public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Polarized

open EpsilonEridani.QFT.Scattering.DIS.Kinematics (Bilin DisKinematics)

variable {V : Type} [AddCommGroup V] [Module ℝ V] {g : Bilin V}

/-! ### The two covariant structures -/

/-- The first covariant structure of the antisymmetric hadronic tensor,
`E₁(v, w) = ε(v, w, q, S)`. -/
def spinStructureOne (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) : Bilin V :=
  ε.bilinMap ![K.q, K.S]

/-- Pointwise value of `E₁`. -/
lemma spinStructureOne_apply (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (v w : V) :
    spinStructureOne ε K v w = ε ![v, w, K.q, K.S] :=
  ε.bilinMap_apply _ _ _

/-- The second covariant structure of the antisymmetric hadronic tensor,
`E₂(v, w) = ε(v, w, q, (p·q) S − (S·q) p)`. -/
def spinStructureTwo (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) : Bilin V :=
  ε.bilinMap ![K.q, g K.p K.q • K.S - g K.S K.q • K.p]

/-- Pointwise value of `E₂`. -/
lemma spinStructureTwo_apply (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (v w : V) :
    spinStructureTwo ε K v w = ε ![v, w, K.q, g K.p K.q • K.S - g K.S K.q • K.p] :=
  ε.bilinMap_apply _ _ _

/-! ### Alternation and conservation -/

/-- The first covariant structure is alternating. -/
theorem spinStructureOne_isAlt (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) :
    (spinStructureOne ε K).IsAlt :=
  ε.isAlt_bilinMap _

/-- The second covariant structure is alternating. -/
theorem spinStructureTwo_isAlt (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) :
    (spinStructureTwo ε K).IsAlt :=
  ε.isAlt_bilinMap _

/-- `E₁` is conserved in its first slot. -/
@[simp] theorem spinStructureOne_conserved_left (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) (w : V) : spinStructureOne ε K K.q w = 0 := by
  simpa only [spinStructureOne, Matrix.cons_val_zero] using
    ε.bilinMap_apply_left_eq_zero ![K.q, K.S] 0 w

/-- `E₁` is conserved in its second slot. -/
@[simp] theorem spinStructureOne_conserved_right (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) (v : V) : spinStructureOne ε K v K.q = 0 := by
  simpa only [spinStructureOne, Matrix.cons_val_zero] using
    ε.bilinMap_apply_right_eq_zero ![K.q, K.S] 0 v

/-- `E₂` is conserved in its first slot. -/
@[simp] theorem spinStructureTwo_conserved_left (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) (w : V) : spinStructureTwo ε K K.q w = 0 := by
  simpa only [spinStructureTwo, Matrix.cons_val_zero] using
    ε.bilinMap_apply_left_eq_zero ![K.q, g K.p K.q • K.S - g K.S K.q • K.p] 0 w

/-- `E₂` is conserved in its second slot. -/
@[simp] theorem spinStructureTwo_conserved_right (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) (v : V) : spinStructureTwo ε K v K.q = 0 := by
  simpa only [spinStructureTwo, Matrix.cons_val_zero] using
    ε.bilinMap_apply_right_eq_zero ![K.q, g K.p K.q • K.S - g K.S K.q • K.p] 0 v

/-! ### The tensor with given coefficients -/

/-- The antisymmetric tensor `c₁ • E₁ + c₂ • E₂` with real coefficients `c₁`, `c₂`. -/
def fromG1G2 (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (c₁ c₂ : ℝ) : Bilin V :=
  c₁ • spinStructureOne ε K + c₂ • spinStructureTwo ε K

/-- Pointwise value of `fromG1G2`. -/
lemma fromG1G2_apply (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (c₁ c₂ : ℝ)
    (v w : V) :
    fromG1G2 ε K c₁ c₂ v w = c₁ * spinStructureOne ε K v w + c₂ * spinStructureTwo ε K v w := by
  simp only [fromG1G2, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-- `fromG1G2` is alternating. -/
theorem fromG1G2_isAlt (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (c₁ c₂ : ℝ) :
    (fromG1G2 ε K c₁ c₂).IsAlt := fun v => by
  rw [fromG1G2_apply, spinStructureOne_isAlt ε K v, spinStructureTwo_isAlt ε K v,
    mul_zero, mul_zero, add_zero]

/-- `fromG1G2` satisfies the antisymmetry interface `TensorAssumptions`. -/
theorem tensorAssumptions_fromG1G2 (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (c₁ c₂ : ℝ) : TensorAssumptions V (fromG1G2 ε K c₁ c₂) :=
  tensorAssumptions_iff_isAlt.mpr (fromG1G2_isAlt ε K c₁ c₂)

/-- `fromG1G2` is conserved in its first slot. -/
@[simp] theorem fromG1G2_conserved_left (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (c₁ c₂ : ℝ) (w : V) : fromG1G2 ε K c₁ c₂ K.q w = 0 := by
  simp [fromG1G2_apply]

/-- `fromG1G2` is conserved in its second slot. -/
@[simp] theorem fromG1G2_conserved_right (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (c₁ c₂ : ℝ) (v : V) : fromG1G2 ε K c₁ c₂ v K.q = 0 := by
  simp [fromG1G2_apply]

/-! ### The decomposition predicate -/

/-- The antisymmetric hadronic tensor `W` decomposes on `E₁`, `E₂` with the structure functions
of `G`:
```text
W = (M / (p·q)) · g₁(x, Q²) · E₁ + (1 / (M (p·q))) · g₂(x, Q²) · E₂
```
at the kinematic point `(x, Q²) = (x_B, -q²)` of `K`, where `M = √(p·p)` is the target mass.
This is the antisymmetric counterpart of `Tensors.Hadronic.IsF1F2Decomposition`. -/
def IsG1G2Decomposition (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (G : StructureFunctions) (W : Bilin V) : Prop :=
  W = fromG1G2 ε K (√(K.M2 g) / g K.p K.q * G.g1 (K.xBj g) (K.Q2 g))
    ((√(K.M2 g))⁻¹ / g K.p K.q * G.g2 (K.xBj g) (K.Q2 g))

/-- `fromG1G2` with the coefficients read off from `g₁`, `g₂` at the kinematic point
decomposes with those structure functions. -/
theorem fromG1G2_isDecomposition (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (G : StructureFunctions) :
    IsG1G2Decomposition ε K G
      (fromG1G2 ε K (√(K.M2 g) / g K.p K.q * G.g1 (K.xBj g) (K.Q2 g))
        ((√(K.M2 g))⁻¹ / g K.p K.q * G.g2 (K.xBj g) (K.Q2 g))) :=
  (rfl)

namespace IsG1G2Decomposition

variable {ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ} {K : PolarizedKinematics g} {G : StructureFunctions}
  {W : Bilin V}

/-- A tensor decomposing on `E₁`, `E₂` is alternating. -/
theorem isAlt (h : IsG1G2Decomposition ε K G W) : W.IsAlt :=
  h ▸ fromG1G2_isAlt ε K _ _

/-- A tensor decomposing on `E₁`, `E₂` is conserved in its first slot. -/
theorem conserved_left (h : IsG1G2Decomposition ε K G W) (w : V) : W K.q w = 0 :=
  h ▸ fromG1G2_conserved_left ε K _ _ w

/-- A tensor decomposing on `E₁`, `E₂` is conserved in its second slot. -/
theorem conserved_right (h : IsG1G2Decomposition ε K G W) (v : V) : W v K.q = 0 :=
  h ▸ fromG1G2_conserved_right ε K _ _ v

end IsG1G2Decomposition

/-! ### Non-degeneracy -/

/-- `E₁` and `E₂` can be linearly independent: on `ℝ⁴` with the Minkowski metric
`diag(1, -1, -1, -1)`, the determinant as the four-form, `p = (1, 0, 0, 0)`, `q = (1, 0, 1, 1)`
and `S = (0, 0, 0, 1)` (so `S·q ≠ 0`), `fromG1G2` is non-zero unless both coefficients vanish. -/
theorem exists_fromG1G2_ne_zero :
    ∃ (g : Bilin (Fin 4 → ℝ)) (ε : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g),
      ∀ c₁ c₂ : ℝ, (c₁ ≠ 0 ∨ c₂ ≠ 0) → fromG1G2 ε K c₁ c₂ ≠ 0 := by
  let η : Bilin (Fin 4 → ℝ) := Matrix.toBilin' (Matrix.diagonal ![1, -1, -1, -1])
  have hd : ∀ M : Fin 4 → Fin 4 → ℝ, Matrix.detRowAlternating M = (Matrix.of M).det :=
    fun _ => rfl
  refine ⟨η, Matrix.detRowAlternating,
    { p := ![1, 0, 0, 0], pPrime := 0, k := ![1, 0, 1, 1], kPrime := 0, q := ![1, 0, 1, 1],
      hq := (sub_zero _).symm, S := ![0, 0, 0, 1],
      spin_orthogonal := by
        simp [η, Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_succ, Matrix.mulVec,
          Matrix.diagonal]
      spin_normalized := by
        simp [η, Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_succ, Matrix.mulVec,
          Matrix.diagonal] }, fun c₁ c₂ h hz => ?_⟩
  have h01 : c₁ + c₂ = 0 := by
    simpa [fromG1G2_apply, spinStructureOne_apply, spinStructureTwo_apply, hd, η,
      Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Matrix.toBilin'_apply',
      dotProduct, Matrix.mulVec, Matrix.diagonal] using
      LinearMap.congr_fun₂ hz ![1, 0, 0, 0] ![0, 1, 0, 0]
  have h13 : c₂ = 0 := by
    simpa [fromG1G2_apply, spinStructureOne_apply, spinStructureTwo_apply, hd, η,
      Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove, Matrix.toBilin'_apply',
      dotProduct, Matrix.mulVec, Matrix.diagonal] using
      LinearMap.congr_fun₂ hz ![0, 1, 0, 0] ![0, 0, 0, 1]
  rcases h with h | h
  · exact h (by linarith)
  · exact h h13

end Polarized
end DIS
end Scattering
end QFT
end EpsilonEridani
