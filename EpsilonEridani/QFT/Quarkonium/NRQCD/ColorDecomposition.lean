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
antiquark index `j` carries the conjugate generators `-(Tᵃ)ᵀ`, which on the matrix `ψ` is right
multiplication by `-Tᵃ`, and the generator `Tᵃ` of the pair acts by the commutator
`ψ ↦ Tᵃ ψ - ψ Tᵃ`.

This module decomposes `N ⊗ N* = 1 ⊕ (N² - 1)` into the colour-singlet and colour-octet channels
(the octet being the adjoint representation, of dimension `8` at `N = 3`). The octet projector is
built from the generalized Gell-Mann generators `Tᵃ = SUNGen.genM N a` of `su(N)` and the singlet
projector directly from the trace; that the two are complementary (`colorOctetProj_eq`) is what
the completeness relation of the generators supplies. Every property below is proved from the
trace and completeness identities of
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
* `colorSingletProj_apply_eq_self_iff`, `colorOctetProj_apply_eq_self_iff`: the singlet channel
  consists of the multiples of `1` and the octet channel of the traceless wave functions.
* `completeOrthogonalIdempotents_colorSingletProj_colorOctetProj`: the two projectors are
  complete orthogonal idempotents.
* `colorSingletProj_apply_eq_smul_colorSingletState` and
  `trace_conjTranspose_colorSingletState_mul_self`: the singlet projector projects onto a
  unit-norm state.
* `trace_colorSingletProj`, `trace_colorOctetProj`: the traces `1` and `N² - 1`.
* `commute_ad_colorSingletProj`, `commute_ad_colorOctetProj`: both channels are invariant under
  the colour action.
* `casimir_genM_eq`, `casimir_genM_mul_colorSingletProj`, `casimir_genM_mul_colorOctetProj`,
  `colorSingletProj_mul_casimir_genM`, `colorOctetProj_mul_casimir_genM`: the Casimir is `0` on
  the singlet channel and `N` on the octet channel, from either side.

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
    colorSingletProj N ψ = ((N : ℂ)⁻¹ * ψ.trace) • 1 := by
  rw [colorSingletProj, LinearMap.smulRight_apply, LinearMap.smul_apply, traceLinearMap_apply,
    smul_eq_mul]

/-- The projector onto the colour-octet channel of a quark-antiquark pair, built from the
generators of `su(N)`: `ψ ↦ 2 Σₐ Tr(ψ Tᵃ) Tᵃ`. The factor `2` is `1 / T_F`. -/
def colorOctetProj (N : ℕ) : Module.End ℂ (Matrix (Fin N) (Fin N) ℂ) :=
  ∑ a : SUNIndex N,
    ((2 : ℂ) • (traceLinearMap (Fin N) ℂ ℂ ∘ₗ LinearMap.mulRight ℂ (genM N a))).smulRight
      (genM N a)

/-- The octet projector in its defining generator form, `ψ ↦ 2 Σₐ Tr(ψ Tᵃ) Tᵃ`; the closed form
is `colorOctetProj_apply`. -/
theorem colorOctetProj_apply_eq_sum (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorOctetProj N ψ = ∑ a : SUNIndex N, (2 * (ψ * genM N a).trace) • genM N a := by
  simp [colorOctetProj, LinearMap.sum_apply]

/-- The octet projector is the complement of the singlet projector: by the completeness relation
of the generators, `2 Σₐ Tr(ψ Tᵃ) Tᵃ = ψ - (Tr ψ / N) · 1`. -/
theorem colorOctetProj_eq : colorOctetProj N = 1 - colorSingletProj N := by
  ext ψ : 1
  rw [colorOctetProj_apply_eq_sum]
  simp only [mul_smul, ← Finset.smul_sum]
  rw [sum_genM_proj, smul_smul, mul_one_div_cancel two_ne_zero, one_smul, LinearMap.sub_apply,
    Module.End.one_apply, colorSingletProj_apply]

/-- The octet projector in closed form: `P₈ ψ = ψ - (Tr ψ / N) · 1`. -/
@[simp]
theorem colorOctetProj_apply (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorOctetProj N ψ = ψ - ((N : ℂ)⁻¹ * ψ.trace) • 1 := by
  rw [colorOctetProj_eq, LinearMap.sub_apply, Module.End.one_apply, colorSingletProj_apply]

/-- The two colour channels exhaust the pair's colour space. -/
@[simp]
theorem colorSingletProj_add_colorOctetProj : colorSingletProj N + colorOctetProj N = 1 := by
  rw [colorOctetProj_eq, add_sub_cancel]

/-- The two colour channels exhaust the pair's colour space, in the reversed addition order. -/
@[simp]
theorem colorOctetProj_add_colorSingletProj : colorOctetProj N + colorSingletProj N = 1 := by
  rw [add_comm (colorOctetProj N) (colorSingletProj N), colorSingletProj_add_colorOctetProj]

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

/-- The singlet projector squares to itself: `P₁ P₁ = P₁`. -/
@[simp]
theorem colorSingletProj_mul_self :
    colorSingletProj N * colorSingletProj N = colorSingletProj N :=
  isIdempotentElem_colorSingletProj.eq

/-- The octet projector squares to itself: `P₈ P₈ = P₈`. -/
@[simp]
theorem colorOctetProj_mul_self :
    colorOctetProj N * colorOctetProj N = colorOctetProj N :=
  isIdempotentElem_colorOctetProj.eq

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

/-- A wave function lies in the singlet channel exactly when it is a multiple of `1`. -/
theorem colorSingletProj_apply_eq_self_iff (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorSingletProj N ψ = ψ ↔ ∃ c : ℂ, ψ = c • 1 := by
  refine ⟨fun h ↦ ⟨_, h.symm.trans (colorSingletProj_apply ψ)⟩, ?_⟩
  rintro ⟨c, rfl⟩
  rcases eq_or_ne (N : ℂ) 0 with hN | hN
  · obtain rfl : N = 0 := Nat.cast_eq_zero.1 hN
    exact Subsingleton.elim _ _
  · rw [colorSingletProj_apply, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul,
      mul_left_comm, inv_mul_cancel₀ hN, mul_one]

/-- A wave function lies in the octet channel exactly when it is traceless. -/
theorem colorOctetProj_apply_eq_self_iff (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorOctetProj N ψ = ψ ↔ ψ.trace = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [Subsingleton.elim (colorOctetProj 0 ψ) ψ]
  · have : NeZero N := ⟨hN.ne'⟩
    simp [sub_eq_self, Nat.pos_iff_ne_zero.1 hN]

/-! ### The normalised singlet state -/

/-- The colour-singlet state `δ_{ij} / √N` of a quark-antiquark pair, normalised to unit norm. -/
def colorSingletState (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := (((√N)⁻¹ : ℝ) : ℂ) • 1

/-- The defining formula of the colour-singlet state, `ψ₁ = (1 / √N) · 1`. -/
theorem colorSingletState_def :
    colorSingletState N = (((√N)⁻¹ : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) := (rfl)

/-- The entries of the colour-singlet state: `(ψ₁)_{ij} = δ_{ij} / √N`. -/
@[simp]
theorem colorSingletState_apply (i j : Fin N) :
    colorSingletState N i j = if i = j then (((√N)⁻¹ : ℝ) : ℂ) else 0 := by
  simp [colorSingletState, one_apply]

/-- The colour-singlet state is self-adjoint. -/
theorem conjTranspose_colorSingletState : (colorSingletState N)ᴴ = colorSingletState N := by
  simp [colorSingletState]

/-- The colour-singlet state has unit norm: `Tr(ψ₁† ψ₁) = 1`, for `ψ₁ = δ_{ij} / √N`. -/
@[simp]
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
theorem colorSingletProj_apply_eq_smul_colorSingletState (ψ : Matrix (Fin N) (Fin N) ℂ) :
    colorSingletProj N ψ = ((colorSingletState N)ᴴ * ψ).trace • colorSingletState N := by
  have h : (√N : ℝ)⁻¹ * (√N)⁻¹ = (N : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg N)]
  simp only [colorSingletProj_apply, colorSingletState, conjTranspose_smul, conjTranspose_one,
    Complex.star_def, Complex.conj_ofReal, smul_mul, one_mul, trace_smul, smul_eq_mul, smul_smul]
  congr 1
  rw [mul_right_comm, ← Complex.ofReal_mul, h, Complex.ofReal_inv, Complex.ofReal_natCast]

/-! ### Traces -/

/-- The singlet channel is one-dimensional: its projector has trace `1`. -/
@[simp]
theorem trace_colorSingletProj [NeZero N] :
    LinearMap.trace ℂ (Matrix (Fin N) (Fin N) ℂ) (colorSingletProj N) = 1 := by
  rw [colorSingletProj, LinearMap.trace_smulRight, LinearMap.smul_apply, traceLinearMap_apply,
    trace_one, Fintype.card_fin, smul_eq_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 (NeZero.ne N))]

/-- The octet channel has dimension `N² - 1`: its projector has trace `N² - 1`. -/
@[simp]
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
action of an arbitrary matrix.

The Lie bracket on matrices used here, and by the Casimir results below, is the commutator
bracket of `LieRing.ofAssociativeRing`, which Mathlib does not make a global instance; a file
that states or rewrites with these results must enable it as this one does, with
`attribute [local instance 100] LieRing.ofAssociativeRing`. -/

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
  rw [commute_iff_eq, ad_mul_colorSingletProj, colorSingletProj_mul_ad]

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

/-- The Casimir vanishes on the colour-singlet channel, multiplying from the right. -/
@[simp]
theorem colorSingletProj_mul_casimir_genM :
    colorSingletProj N * LieModule.casimir ℂ _ _ (genM N) (genM N) = 0 := by
  rw [casimir_genM_eq, mul_smul_comm, colorSingletProj_mul_colorOctetProj, smul_zero]

/-- The Casimir takes the value `N = C_A` on the colour-octet channel, multiplying from the
right. -/
@[simp]
theorem colorOctetProj_mul_casimir_genM :
    colorOctetProj N * LieModule.casimir ℂ _ _ (genM N) (genM N) = (N : ℂ) • colorOctetProj N := by
  rw [casimir_genM_eq, mul_smul_comm, colorOctetProj_mul_self]

end EpsilonEridani.QFT.Quarkonium
