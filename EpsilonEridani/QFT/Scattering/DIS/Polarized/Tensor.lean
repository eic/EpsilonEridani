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
either argument is `q`. Both are odd under spin reversal `PolarizedKinematics.reverse`.

`fromG1G2 ε K g₁ g₂` is the tensor with structure-function values `g₁`, `g₂`, that is
```text
(M / (p·q)) · g₁ · E₁ + (M / (p·q)²) · g₂ · E₂ = (M / (p·q)) · ε(·, ·, q, g₁ S + g₂ S_⊥),
```
with `M = √(p·p)` the target mass and `S_⊥ = S − ((S·q)/(p·q)) p`. `IsG1G2Decomposition ε K G W`
says that `W` is `fromG1G2` at the values of `G` at the kinematic point of `K`. These are the
antisymmetric counterparts of `Tensors.Hadronic.IsF1F2Decomposition` and
`Tensors.Hadronic.fromF1F2`.

`SpinUniquenessAssumptions` collects two probe pairs separating `E₁` from `E₂`; under it the
two structures are linearly independent (`linearIndependent_spinStructure`) and `fromG1G2` is
non-zero unless both structure-function values vanish (`fromG1G2_ne_zero`). `Witness.kWit4`
gives Minkowski kinematics on `ℝ⁴` where such probes exist (`Witness.spinUniquenessWit`).

## Orientation

An abstract `V` carrying only a bilinear form has no volume form, so the four-form `ε` is
explicit data, as for `Tensors.Leptonic.lMuNuOdd`. Both structures are linear in `ε`:
replacing `ε` by `-ε` flips the sign of both (`spinStructureOne_neg`, `spinStructureTwo_neg`),
and of every asymmetry built from them, so these signs are meaningful only once `ε` is fixed.

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

/-- `E₁` vanishes on the diagonal. -/
@[simp] theorem spinStructureOne_apply_self (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) (v : V) : spinStructureOne ε K v v = 0 :=
  ε.bilinMap_apply_self _ v

/-- `E₂` vanishes on the diagonal. -/
@[simp] theorem spinStructureTwo_apply_self (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) (v : V) : spinStructureTwo ε K v v = 0 :=
  ε.bilinMap_apply_self _ v

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

/-! ### Spin reversal and orientation -/

/-- `E₁` is odd under spin reversal `S ↦ -S`. -/
@[simp] theorem spinStructureOne_reverse (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) : spinStructureOne ε K.reverse = -spinStructureOne ε K := by
  ext v w
  have h : ![v, w, K.q, -K.S] =
      Function.update ![v, w, K.q, K.S] 3 (-(![v, w, K.q, K.S] 3)) := by
    ext i; fin_cases i <;> rfl
  simp only [LinearMap.neg_apply, spinStructureOne_apply, PolarizedKinematics.reverse_S,
    PolarizedKinematics.reverse_toDisKinematics]
  rw [h, ε.map_update_neg, Function.update_eq_self]

/-- `E₂` is odd under spin reversal `S ↦ -S`. -/
@[simp] theorem spinStructureTwo_reverse (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (K : PolarizedKinematics g) : spinStructureTwo ε K.reverse = -spinStructureTwo ε K := by
  ext v w
  set u := g K.p K.q • K.S - g K.S K.q • K.p
  have h : ![v, w, K.q, g K.p K.q • -K.S - g (-K.S) K.q • K.p] =
      Function.update ![v, w, K.q, u] 3 (-(![v, w, K.q, u] 3)) := by
    ext i; fin_cases i
    · rfl
    · rfl
    · rfl
    · simp [u, sub_eq_add_neg, add_comm]
  simp only [LinearMap.neg_apply, spinStructureTwo_apply, PolarizedKinematics.reverse_S,
    PolarizedKinematics.reverse_toDisKinematics]
  rw [h, ε.map_update_neg, Function.update_eq_self]

/-- `E₁` is linear in the orientation: `-ε` gives `-E₁`. -/
theorem spinStructureOne_neg (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) :
    spinStructureOne (-ε) K = -spinStructureOne ε K := by
  ext v w
  simp [spinStructureOne_apply]

/-- `E₂` is linear in the orientation: `-ε` gives `-E₂`. -/
theorem spinStructureTwo_neg (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) :
    spinStructureTwo (-ε) K = -spinStructureTwo ε K := by
  ext v w
  simp [spinStructureTwo_apply]

/-! ### The tensor built from `g₁`, `g₂` -/

/-- The antisymmetric tensor with structure-function values `g₁`, `g₂`,
```text
(M / (p·q)) · g₁ · E₁ + (M / (p·q)²) · g₂ · E₂,
```
where `M = √(p·p)` is the target mass. Equivalently it is
`(M / (p·q)) · ε(·, ·, q, g₁ S + g₂ (S − ((S·q)/(p·q)) p))`, the standard form of the
spin-dependent hadronic tensor for a spin vector normalised to `S·S = -1`. -/
def fromG1G2 (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (g₁ g₂ : ℝ) : Bilin V :=
  (√(K.M2 g) / g K.p K.q * g₁) • spinStructureOne ε K
    + (√(K.M2 g) / g K.p K.q ^ 2 * g₂) • spinStructureTwo ε K

/-- Pointwise value of `fromG1G2`. -/
lemma fromG1G2_apply (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (g₁ g₂ : ℝ)
    (v w : V) :
    fromG1G2 ε K g₁ g₂ v w = √(K.M2 g) / g K.p K.q * g₁ * spinStructureOne ε K v w
      + √(K.M2 g) / g K.p K.q ^ 2 * g₂ * spinStructureTwo ε K v w := by
  simp only [fromG1G2, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]

/-- `fromG1G2` is alternating. -/
theorem fromG1G2_isAlt (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (g₁ g₂ : ℝ) :
    (fromG1G2 ε K g₁ g₂).IsAlt :=
  ((spinStructureOne_isAlt ε K).smul _).add ((spinStructureTwo_isAlt ε K).smul _)

/-- `fromG1G2` vanishes on the diagonal. -/
@[simp] theorem fromG1G2_apply_self (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (g₁ g₂ : ℝ) (v : V) : fromG1G2 ε K g₁ g₂ v v = 0 :=
  fromG1G2_isAlt ε K g₁ g₂ v

/-- `fromG1G2` satisfies the antisymmetry interface `TensorAssumptions`. -/
theorem tensorAssumptions_fromG1G2 (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (g₁ g₂ : ℝ) : TensorAssumptions V (fromG1G2 ε K g₁ g₂) :=
  tensorAssumptions_iff_isAlt.mpr (fromG1G2_isAlt ε K g₁ g₂)

/-- `fromG1G2` is conserved in its first slot. -/
@[simp] theorem fromG1G2_conserved_left (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (g₁ g₂ : ℝ) (w : V) : fromG1G2 ε K g₁ g₂ K.q w = 0 := by
  simp [fromG1G2_apply]

/-- `fromG1G2` is conserved in its second slot. -/
@[simp] theorem fromG1G2_conserved_right (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (g₁ g₂ : ℝ) (v : V) : fromG1G2 ε K g₁ g₂ v K.q = 0 := by
  simp [fromG1G2_apply]

/-- `fromG1G2` is odd under spin reversal `S ↦ -S`. -/
@[simp] theorem fromG1G2_reverse (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (g₁ g₂ : ℝ) : fromG1G2 ε K.reverse g₁ g₂ = -fromG1G2 ε K g₁ g₂ := by
  ext v w
  simp only [fromG1G2_apply, LinearMap.neg_apply, spinStructureOne_reverse,
    spinStructureTwo_reverse, PolarizedKinematics.reverse_toDisKinematics]
  ring

/-- `fromG1G2` is linear in the orientation: `-ε` gives `-fromG1G2`. -/
theorem fromG1G2_neg (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (g₁ g₂ : ℝ) :
    fromG1G2 (-ε) K g₁ g₂ = -fromG1G2 ε K g₁ g₂ := by
  ext v w
  simp only [fromG1G2_apply, LinearMap.neg_apply, spinStructureOne_neg, spinStructureTwo_neg]
  ring

/-! ### The decomposition predicate -/

/-- The antisymmetric hadronic tensor `W` decomposes on `E₁`, `E₂` with the structure functions
of `G`:
```text
W = (M / (p·q)) · g₁(x, Q²) · E₁ + (M / (p·q)²) · g₂(x, Q²) · E₂
```
at the kinematic point `(x, Q²) = (x_B, -q²)` of `K`, where `M = √(p·p)` is the target mass.
This is the antisymmetric counterpart of `Tensors.Hadronic.IsF1F2Decomposition`. -/
def IsG1G2Decomposition (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (G : StructureFunctions) (W : Bilin V) : Prop :=
  W = fromG1G2 ε K (G.g1 (K.xBj g) (K.Q2 g)) (G.g2 (K.xBj g) (K.Q2 g))

/-- `fromG1G2` at the values of `g₁`, `g₂` at the kinematic point decomposes with those
structure functions. -/
theorem fromG1G2_isDecomposition (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (G : StructureFunctions) :
    IsG1G2Decomposition ε K G (fromG1G2 ε K (G.g1 (K.xBj g) (K.Q2 g)) (G.g2 (K.xBj g) (K.Q2 g))) :=
  (rfl)

namespace IsG1G2Decomposition

variable {ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ} {K : PolarizedKinematics g} {G : StructureFunctions}
  {W : Bilin V}

/-- A tensor decomposing on `E₁`, `E₂` is `fromG1G2` at the values of `G`. -/
theorem eq (h : IsG1G2Decomposition ε K G W) :
    W = fromG1G2 ε K (G.g1 (K.xBj g) (K.Q2 g)) (G.g2 (K.xBj g) (K.Q2 g)) :=
  h

/-- Pointwise value of a tensor decomposing on `E₁`, `E₂`. -/
theorem apply (h : IsG1G2Decomposition ε K G W) (v w : V) :
    W v w = √(K.M2 g) / g K.p K.q * G.g1 (K.xBj g) (K.Q2 g) * spinStructureOne ε K v w
      + √(K.M2 g) / g K.p K.q ^ 2 * G.g2 (K.xBj g) (K.Q2 g) * spinStructureTwo ε K v w := by
  rw [h.eq, fromG1G2_apply]

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

/-- Probe vectors separating the two covariant structures: one pair sees `E₁` but not `E₂`,
and one pair does the reverse. This is the antisymmetric counterpart of
`Tensors.Hadronic.UniquenessAssumptions`. -/
structure SpinUniquenessAssumptions (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) :
    Type where
  /-- First slot of the probe pair isolating `E₁`. -/
  vOne : V
  /-- Second slot of the probe pair isolating `E₁`. -/
  wOne : V
  /-- The `E₁` probe pair sees `E₁`. -/
  structureOne_ne_zero : spinStructureOne ε K vOne wOne ≠ 0
  /-- The `E₁` probe pair does not see `E₂`. -/
  structureTwo_eq_zero : spinStructureTwo ε K vOne wOne = 0
  /-- First slot of the probe pair isolating `E₂`. -/
  vTwo : V
  /-- Second slot of the probe pair isolating `E₂`. -/
  wTwo : V
  /-- The `E₂` probe pair does not see `E₁`. -/
  structureOne_eq_zero : spinStructureOne ε K vTwo wTwo = 0
  /-- The `E₂` probe pair sees `E₂`. -/
  structureTwo_ne_zero : spinStructureTwo ε K vTwo wTwo ≠ 0

/-- With probe vectors separating them, `E₁` and `E₂` are linearly independent. -/
theorem linearIndependent_spinStructure (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g)
    (hU : SpinUniquenessAssumptions ε K) :
    LinearIndependent ℝ ![spinStructureOne ε K, spinStructureTwo ε K] := by
  refine (LinearIndependent.pair_iff (R := ℝ) (M := Bilin V)).mpr fun s t hst => ⟨?_, ?_⟩
  · have h := LinearMap.congr_fun₂ hst hU.vOne hU.wOne
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hU.structureTwo_eq_zero,
      mul_zero, add_zero, LinearMap.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right hU.structureOne_ne_zero
  · have h := LinearMap.congr_fun₂ hst hU.vTwo hU.wTwo
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hU.structureOne_eq_zero,
      mul_zero, zero_add, LinearMap.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right hU.structureTwo_ne_zero

/-- With probe vectors separating `E₁` and `E₂`, a positive target mass and `p·q ≠ 0`, the
tensor `fromG1G2` with `(g₁, g₂) ≠ (0, 0)` is non-zero. -/
theorem fromG1G2_ne_zero (ε : V [⋀^Fin 4]→ₗ[ℝ] ℝ) (K : PolarizedKinematics g) (g₁ g₂ : ℝ)
    (hU : SpinUniquenessAssumptions ε K) (hM : 0 < K.M2 g) (hpq : g K.p K.q ≠ 0)
    (h : g₁ ≠ 0 ∨ g₂ ≠ 0) : fromG1G2 ε K g₁ g₂ ≠ 0 := by
  intro h0
  obtain ⟨h1, h2⟩ := (LinearIndependent.pair_iff (R := ℝ) (M := Bilin V)).mp
    (linearIndependent_spinStructure ε K hU) _ _ h0
  have hs : √(K.M2 g) ≠ 0 := (Real.sqrt_pos.mpr hM).ne'
  rcases h with h | h
  · exact h (by simpa [hs, hpq] using h1)
  · exact h (by simpa [hs, hpq] using h2)

/-! ### A witness in four-dimensional Minkowski space -/

namespace Witness

/-- The Minkowski metric `diag(1, -1, -1, -1)` on `ℝ⁴`. -/
def ηWit : Bilin (Fin 4 → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal ![1, -1, -1, -1])

@[simp] lemma ηWit_apply (v w : Fin 4 → ℝ) :
    ηWit v w = v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := by
  simp [ηWit, Matrix.toBilin'_apply', dotProduct, Fin.sum_univ_succ, Matrix.mulVec,
    Matrix.diagonal]
  ring

/-- The determinant of the four rows, as the orientation four-form on `ℝ⁴`. -/
def εWit : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ :=
  Matrix.detRowAlternating

/-- Mathlib has no `detRowAlternating_apply`: `Matrix.det` is defined as
`detRowAlternating`, so this holds by unfolding that definition. -/
lemma εWit_apply (M : Fin 4 → Fin 4 → ℝ) : εWit M = (Matrix.of M).det :=
  rfl

/-- Witness kinematics on `ℝ⁴` with the metric `ηWit`: a target of unit mass at rest,
`p = (1, 0, 0, 0)`, momentum transfer `q = (1, 0, 1, 1)` (so `p·q = 1`, `Q² = 1`) and spin
`S = (0, 0, 0, 1)`, which has `S·q = -1 ≠ 0`. -/
def kWit4 : PolarizedKinematics ηWit where
  p := ![1, 0, 0, 0]
  pPrime := 0
  k := ![1, 0, 1, 1]
  kPrime := 0
  q := ![1, 0, 1, 1]
  hq := (sub_zero _).symm
  S := ![0, 0, 0, 1]
  spin_orthogonal := by simp
  spin_normalized := by simp

@[simp] lemma kWit4_p : kWit4.p = ![1, 0, 0, 0] := rfl

@[simp] lemma kWit4_q : kWit4.q = ![1, 0, 1, 1] := rfl

@[simp] lemma kWit4_S : kWit4.S = ![0, 0, 0, 1] := rfl

lemma kWit4_M2 : kWit4.M2 ηWit = 1 := by simp [DisKinematics.M2_def]

lemma kWit4_p_q : ηWit kWit4.p kWit4.q = 1 := by simp

/-- `E₁(p + S, e₁) = 1` on the witness. -/
lemma spinStructureOne_kWit4_one :
    spinStructureOne εWit kWit4 ![1, 0, 0, 1] ![0, 1, 0, 0] = 1 := by
  rw [spinStructureOne_apply, εWit_apply, Matrix.det_succ_row_zero]
  simp (disch := decide) [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove_of_castSucc_lt,
    Fin.succAbove_of_le_castSucc]

/-- `E₂(p + S, e₁) = 0` on the witness, since `(p·q) S − (S·q) p = p + S` there. -/
lemma spinStructureTwo_kWit4_one :
    spinStructureTwo εWit kWit4 ![1, 0, 0, 1] ![0, 1, 0, 0] = 0 := by
  rw [spinStructureTwo_apply, εWit_apply, Matrix.det_succ_row_zero]
  simp (disch := decide) [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove_of_castSucc_lt,
    Fin.succAbove_of_le_castSucc]

/-- `E₁(e₁, S) = 0` on the witness. -/
lemma spinStructureOne_kWit4_two :
    spinStructureOne εWit kWit4 ![0, 1, 0, 0] ![0, 0, 0, 1] = 0 := by
  rw [spinStructureOne_apply, εWit_apply, Matrix.det_succ_row_zero]
  simp (disch := decide) [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove_of_castSucc_lt,
    Fin.succAbove_of_le_castSucc]

/-- `E₂(e₁, S) = 1` on the witness. -/
lemma spinStructureTwo_kWit4_two :
    spinStructureTwo εWit kWit4 ![0, 1, 0, 0] ![0, 0, 0, 1] = 1 := by
  rw [spinStructureTwo_apply, εWit_apply, Matrix.det_succ_row_zero]
  simp (disch := decide) [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove_of_castSucc_lt,
    Fin.succAbove_of_le_castSucc]

/-- **`SpinUniquenessAssumptions` is satisfiable.** The pair `(p + S, e₁)` sees only `E₁` and
the pair `(e₁, S)` sees only `E₂`. -/
def spinUniquenessWit : SpinUniquenessAssumptions εWit kWit4 where
  vOne := ![1, 0, 0, 1]
  wOne := ![0, 1, 0, 0]
  structureOne_ne_zero := by rw [spinStructureOne_kWit4_one]; exact one_ne_zero
  structureTwo_eq_zero := spinStructureTwo_kWit4_one
  vTwo := ![0, 1, 0, 0]
  wTwo := ![0, 0, 0, 1]
  structureOne_eq_zero := spinStructureOne_kWit4_two
  structureTwo_ne_zero := by rw [spinStructureTwo_kWit4_two]; exact one_ne_zero

/-- On the witness, `E₁` and `E₂` are linearly independent. -/
theorem linearIndependent_spinStructure_kWit4 :
    LinearIndependent ℝ ![spinStructureOne εWit kWit4, spinStructureTwo εWit kWit4] :=
  linearIndependent_spinStructure εWit kWit4 spinUniquenessWit

/-- On the witness, `fromG1G2` is non-zero unless both structure-function values vanish. -/
theorem fromG1G2_kWit4_ne_zero (g₁ g₂ : ℝ) (h : g₁ ≠ 0 ∨ g₂ ≠ 0) :
    fromG1G2 εWit kWit4 g₁ g₂ ≠ 0 :=
  fromG1G2_ne_zero εWit kWit4 g₁ g₂ spinUniquenessWit (by rw [kWit4_M2]; exact one_pos)
    (by rw [kWit4_p_q]; exact one_ne_zero) h

end Witness

end Polarized
end DIS
end Scattering
end QFT
end EpsilonEridani
