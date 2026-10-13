/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.LieAlgebra.Casimir
public import EpsilonEridani.QFT.QCD.SUNStructureConstants
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Idempotents

/-!
# The colour singlet and octet channels of a heavy quark-antiquark pair

A quark-antiquark pair carries colour in `N ⊗ N*`: the quark index transforms in the fundamental
representation of `SU(N)` and the antiquark index in its conjugate. Writing the pair's colour
wave function as a matrix `ψ_{i j}`, with `i` the quark index and `j` the antiquark index, the
conjugate generators `-(Tᵃ)ᵀ` act on `j` from the right, and the generator `Tᵃ` of the pair acts by
the commutator `ψ ↦ Tᵃ ψ - ψ Tᵃ`.

This module decomposes `N ⊗ N* = 1 ⊕ (N² - 1)` into the colour-singlet and colour-octet channels
(the octet being the adjoint representation, of dimension `8` at `N = 3`). Both projectors are
built from the generalized Gell-Mann generators `Tᵃ = SUNGen.genM N a` of `su(N)`, and every
property below is proved from the trace and completeness identities of
`EpsilonEridani.QFT.QCD.SUNGenerators` and `EpsilonEridani.QFT.QCD.SUNStructureConstants`, never
entered as a numeral:

* the singlet projector `ψ ↦ (Tr ψ / N) · 1` is the projection onto the normalised singlet state
  `δ_{ij} / √N`, which is where its factor `1 / N` comes from;
* the octet projector `ψ ↦ 2 Σₐ Tr(ψ Tᵃ) Tᵃ` is the complement of the singlet projector, by the
  Fierz completeness relation;
* the two are complete orthogonal idempotents, both commute with the colour action, and their
  traces are `1` and `N² - 1`;
* the quadratic Casimir `Σₐ (Tᵃ)²` of the pair is `N` times the octet projector, so it takes the
  value `0` on the singlet channel and `N = C_A` on the octet channel.

## Main definitions

* `colorSingletProj N`, `colorOctetProj N`: the projectors onto the two colour channels.
* `colorSingletState N`: the unit-normalised colour-singlet state `δ_{ij} / √N`.

The colour action of `Tᵃ` on the pair is the adjoint action `LieAlgebra.ad ℂ _ (genM N a)`, and
its quadratic Casimir is `LieModule.casimir ℂ _ _ (genM N) (genM N)`.

## Main results

* `colorOctetProj_eq`: the octet projector built from the generators is `1 - colorSingletProj N`.
* `completeOrthogonalIdempotents_colorSingletProj_colorOctetProj`: the two projectors are
  complete orthogonal idempotents.
* `colorSingletProj_apply_eq_colorSingletState` and
  `trace_conjTranspose_colorSingletState_mul_self`: the singlet projector projects onto a
  unit-norm state.
* `trace_colorSingletProj`, `trace_colorOctetProj`: the traces `1` and `N² - 1`.
* `commute_ad_colorSingletProj`, `commute_ad_colorOctetProj`: both channels are invariant under
  the colour action.
* `casimir_genM_eq`, `casimir_genM_mul_colorSingletProj`, `casimir_genM_mul_colorOctetProj`: the
  Casimir is `0` on the singlet channel and `N` on the octet channel.

## References

* G. T. Bodwin, E. Braaten and G. P. Lepage, *Rigorous QCD analysis of inclusive annihilation and
  production of heavy quarkonium*, Phys. Rev. D 51 (1995) 1125, Appendix A.
* N. Brambilla, A. Pineda, J. Soto and A. Vairo, *Effective field theories for heavy quarkonium*,
  Rev. Mod. Phys. 77 (2005) 1423, Section IV.
-/

public section

noncomputable section

namespace EpsilonEridani.QFT.Quarkonium

open Matrix EpsilonEridani.QFT.QCD.RepresentationColor.SUNGen

variable {N : ℕ}

/-! ### The two projectors -/

/-- The projector onto the colour-singlet channel of a quark-antiquark pair,
`ψ ↦ (Tr ψ / N) · 1`. -/
def colorSingletProj (N : ℕ) : Module.End ℂ (Matrix (Fin N) (Fin N) ℂ) :=
  ((N : ℂ)⁻¹ • traceLinearMap (Fin N) ℂ ℂ).smulRight 1

@[simp]
theorem colorSingletProj_apply (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorSingletProj N ψ = ((N : ℂ)⁻¹ * ψ.trace) • 1 := (rfl)

/-- The projector onto the colour-octet channel of a quark-antiquark pair, built from the
generators of `su(N)`: `ψ ↦ 2 Σₐ Tr(ψ Tᵃ) Tᵃ`. The factor `2` is `1 / T_F`. -/
def colorOctetProj (N : ℕ) : Module.End ℂ (Matrix (Fin N) (Fin N) ℂ) :=
  ∑ a : SUNIndex N,
    ((2 : ℂ) • (traceLinearMap (Fin N) ℂ ℂ ∘ₗ LinearMap.mulRight ℂ (genM N a))).smulRight
      (genM N a)

theorem colorOctetProj_apply (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorOctetProj N ψ = ∑ a : SUNIndex N, (2 * (ψ * genM N a).trace) • genM N a := by
  simp [colorOctetProj, LinearMap.sum_apply]

/-- The octet projector is the complement of the singlet projector: by the completeness relation
of the generators, `2 Σₐ Tr(ψ Tᵃ) Tᵃ = ψ - (Tr ψ / N) · 1`. -/
theorem colorOctetProj_eq : colorOctetProj N = 1 - colorSingletProj N := by
  ext ψ i l
  have h := sum_genM_proj_apply ψ i l
  rw [LinearMap.sub_apply, Module.End.one_apply, colorSingletProj_apply, colorOctetProj_apply,
    Matrix.sum_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply_kd]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, h]
  ring

/-- The two colour channels exhaust the pair's colour space. -/
@[simp]
theorem colorSingletProj_add_colorOctetProj : colorSingletProj N + colorOctetProj N = 1 := by
  rw [colorOctetProj_eq, add_sub_cancel]

/-- The singlet projector is idempotent. -/
theorem isIdempotentElem_colorSingletProj : IsIdempotentElem (colorSingletProj N) := by
  refine LinearMap.ext fun ψ ↦ ?_
  rcases eq_or_ne (N : ℂ) 0 with hN | hN
  · simp [hN]
  · simp only [Module.End.mul_apply, colorSingletProj_apply, trace_smul, trace_one,
      Fintype.card_fin, smul_eq_mul]
    field_simp

/-- The octet projector is idempotent. -/
theorem isIdempotentElem_colorOctetProj : IsIdempotentElem (colorOctetProj N) := by
  rw [colorOctetProj_eq]
  exact isIdempotentElem_colorSingletProj.one_sub

/-- The singlet and octet channels are orthogonal. -/
@[simp]
theorem colorSingletProj_mul_colorOctetProj : colorSingletProj N * colorOctetProj N = 0 := by
  rw [colorOctetProj_eq, isIdempotentElem_colorSingletProj.mul_one_sub_self]

/-- The octet and singlet channels are orthogonal. -/
@[simp]
theorem colorOctetProj_mul_colorSingletProj : colorOctetProj N * colorSingletProj N = 0 := by
  rw [colorOctetProj_eq, isIdempotentElem_colorSingletProj.one_sub_mul_self]

/-- The singlet and octet projectors are complete orthogonal idempotents: the colour space of a
quark-antiquark pair is the direct sum of the two channels. -/
theorem completeOrthogonalIdempotents_colorSingletProj_colorOctetProj :
    CompleteOrthogonalIdempotents ![colorSingletProj N, colorOctetProj N] := by
  rw [colorOctetProj_eq]
  exact .of_isIdempotentElem isIdempotentElem_colorSingletProj

/-! ### The normalised singlet state -/

/-- The colour-singlet state `δ_{ij} / √N` of a quark-antiquark pair, normalised to unit norm. -/
def colorSingletState (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := (((√N)⁻¹ : ℝ) : ℂ) • 1

/-- The colour-singlet state has unit norm: `Tr(ψ₁† ψ₁) = 1`, for `ψ₁ = δ_{ij} / √N`. -/
theorem trace_conjTranspose_colorSingletState_mul_self [NeZero N] :
    ((colorSingletState N)ᴴ * colorSingletState N).trace = 1 := by
  have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have h : (√N : ℝ) * √N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  simp only [colorSingletState, conjTranspose_smul, conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal, smul_mul_smul, mul_one, trace_smul, trace_one, Fintype.card_fin,
    smul_eq_mul]
  norm_cast
  rw [← mul_inv, h, inv_mul_cancel₀ hN]

/-- The singlet projector is the orthogonal projection onto the unit-norm singlet state:
`P₁ ψ = Tr(ψ₁† ψ) ψ₁`. Its factor `1 / N` is the square of the normalisation `1 / √N`. -/
theorem colorSingletProj_apply_eq_colorSingletState (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorSingletProj N ψ = ((colorSingletState N)ᴴ * ψ).trace • colorSingletState N := by
  have h : (√N : ℝ)⁻¹ * (√N)⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  simp only [colorSingletProj_apply, colorSingletState, conjTranspose_smul, conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal, smul_mul, one_mul, trace_smul, smul_eq_mul, smul_smul]
  congr 1
  rw [mul_right_comm, ← Complex.ofReal_mul, h, Complex.ofReal_inv, Complex.ofReal_natCast]

/-! ### Traces -/

/-- The singlet channel is one-dimensional: its projector has trace `1`. -/
theorem trace_colorSingletProj [NeZero N] :
    LinearMap.trace ℂ (Matrix (Fin N) (Fin N) ℂ) (colorSingletProj N) = 1 := by
  rw [colorSingletProj, LinearMap.trace_smulRight, LinearMap.smul_apply, traceLinearMap_apply,
    trace_one, Fintype.card_fin, smul_eq_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne N))]

/-- The octet channel has dimension `N² - 1`: its projector has trace `N² - 1`. -/
theorem trace_colorOctetProj [NeZero N] :
    LinearMap.trace ℂ (Matrix (Fin N) (Fin N) ℂ) (colorOctetProj N) = (N : ℂ) ^ 2 - 1 := by
  rw [colorOctetProj_eq, map_sub, trace_colorSingletProj, LinearMap.trace_one,
    Module.finrank_matrix, Module.finrank_self, Fintype.card_fin]
  push_cast
  ring

/-! ### The colour action on the pair -/

/-! The generator `Tᵃ` acts on the colour space of a quark-antiquark pair by the adjoint action
`LieAlgebra.ad ℂ _ (genM N a)`: the quark index of `ψ_{i j}` carries the fundamental
representation and the antiquark index the conjugate one, with generators `-(Tᵃ)ᵀ`, and together
they act by the commutator `ψ ↦ Tᵃ ψ - ψ Tᵃ`. The channel statements below hold for the adjoint
action of an arbitrary matrix. -/

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The adjoint action annihilates the singlet channel: `[X, P₁ ψ] = 0`. -/
@[simp]
theorem ad_mul_colorSingletProj (X : Matrix (Fin N) (Fin N) ℂ) :
    LieAlgebra.ad ℂ _ X * colorSingletProj N = 0 := by
  ext ψ : 1
  simp [LieRing.of_associative_ring_bracket]

/-- The adjoint action maps into the octet channel: `P₁ [X, ψ] = 0`, because a commutator is
traceless. -/
@[simp]
theorem colorSingletProj_mul_ad (X : Matrix (Fin N) (Fin N) ℂ) :
    colorSingletProj N * LieAlgebra.ad ℂ _ X = 0 := by
  ext ψ : 1
  simp [LieRing.of_associative_ring_bracket, trace_sub, trace_mul_comm X]

/-- The singlet channel is invariant under the colour action of the pair. -/
theorem commute_ad_colorSingletProj (X : Matrix (Fin N) (Fin N) ℂ) :
    Commute (LieAlgebra.ad ℂ _ X) (colorSingletProj N) := by
  rw [Commute, SemiconjBy, ad_mul_colorSingletProj, colorSingletProj_mul_ad]

/-- The octet channel is invariant under the colour action of the pair. -/
theorem commute_ad_colorOctetProj (X : Matrix (Fin N) (Fin N) ℂ) :
    Commute (LieAlgebra.ad ℂ _ X) (colorOctetProj N) := by
  rw [colorOctetProj_eq]
  exact (Commute.one_right _).sub_right (commute_ad_colorSingletProj X)

/-! ### The quadratic Casimir -/

/-- The quadratic Casimir `Σₐ (Tᵃ)²` of `su(N)` on the colour space of a quark-antiquark pair, in
closed form: `Σₐ [Tᵃ, [Tᵃ, ψ]] = N ψ - Tr ψ · 1`, from the fundamental Casimir and the sandwich
form of the completeness relation. -/
theorem casimir_genM_apply (ψ : Matrix (Fin N) (Fin N) ℂ) :
    LieModule.casimir ℂ _ _ (genM N) (genM N) ψ = (N : ℂ) • ψ - ψ.trace • 1 := by
  have h (a : SUNIndex N) : ⁅genM N a, ⁅genM N a, ψ⁆⁆ =
      genM N a * genM N a * ψ - (2 : ℂ) • (genM N a * ψ * genM N a) +
        ψ * (genM N a * genM N a) := by
    simp only [LieRing.of_associative_ring_bracket, two_smul]
    noncomm_ring
  simp only [LieModule.casimir_apply, h, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.smul_sum, sum_genM_sq, sum_genM_sandwich,
    smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

/-- The Casimir of the pair is `N` times the octet projector. -/
theorem casimir_genM_eq :
    LieModule.casimir ℂ _ _ (genM N) (genM N) = (N : ℂ) • colorOctetProj N := by
  ext ψ : 1
  rw [casimir_genM_apply, colorOctetProj_eq, LinearMap.smul_apply, LinearMap.sub_apply,
    Module.End.one_apply, colorSingletProj_apply]
  rcases eq_or_ne (N : ℂ) 0 with hN | hN
  · obtain rfl : N = 0 := Nat.cast_eq_zero.1 hN
    simp
  · rw [smul_sub, smul_smul, ← mul_assoc, mul_inv_cancel₀ hN, one_mul]

/-- The Casimir vanishes on the colour-singlet channel. -/
@[simp]
theorem casimir_genM_mul_colorSingletProj :
    LieModule.casimir ℂ _ _ (genM N) (genM N) * colorSingletProj N = 0 := by
  rw [casimir_genM_eq, smul_mul_assoc, colorOctetProj_mul_colorSingletProj, smul_zero]

/-- The Casimir takes the value `N = C_A` on the colour-octet channel. -/
@[simp]
theorem casimir_genM_mul_colorOctetProj :
    LieModule.casimir ℂ _ _ (genM N) (genM N) * colorOctetProj N = (N : ℂ) • colorOctetProj N := by
  rw [casimir_genM_eq, smul_mul_assoc, isIdempotentElem_colorOctetProj.eq]

end EpsilonEridani.QFT.Quarkonium
