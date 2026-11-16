/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.LinearAlgebra.BilinearForm.LightConeBasis
public import EpsilonEridani.Relativity.Tensors.RealTensor.Vector.MinkowskiProductExtensions
public import Mathlib.LinearAlgebra.Trace
public import Physlib.Relativity.Fermions.Dirac.GammaMatrices

/-!
# Good and bad light-cone components of Dirac spinors

Fix a light-cone basis `(n₊, n₋)` of four-dimensional Minkowski space, `n₊² = n₋² = 0`,
`n₊ · n₋ = 1`, so that `v⁺ = n₋ · v` and `v⁻ = n₊ · v`. Clifford multiplication by the two
light-like vectors gives `γ⁺ = /n₋` and `γ⁻ = /n₊` (here `/v` is Physlib's
`Fermion.Dirac.gammaMatrix v`), which square to zero and anticommute to `γ⁺γ⁻ + γ⁻γ⁺ = 2`. The
light-cone projectors

  `P₊ = ½ γ⁻ γ⁺`,  `P₋ = ½ γ⁺ γ⁻`

are complementary idempotents on the Dirac spinors, and split a quark spinor `ψ = ψ₊ + ψ₋` into
its *good* component `ψ₊ = P₊ ψ` and its *bad* component `ψ₋ = P₋ ψ`. The good components are
the spinors annihilated by `γ⁻`, the bad ones those annihilated by `γ⁺`; each space has complex
dimension two, and both projectors commute with `γ⁵` and with Clifford multiplication by
transverse vectors, so the good/bad label is compatible with chirality.

The bad component is not an independent degree of freedom. Writing
`/p = p⁺ γ⁻ + p⁻ γ⁺ + /p_T`, the Dirac equation `(/p - m) ψ = 0` for a momentum mode is
equivalent to the pair of projected equations

  `2 p⁺ ψ₋ = (/p_T + m) γ⁺ ψ₊`,  `2 p⁻ ψ₊ = (/p_T + m) γ⁻ ψ₋`.

The first contains no `p⁻`: it is the light-cone *constraint* equation, and for `p⁺ ≠ 0` it
determines `ψ₋` from `ψ₊`. On the mass shell `p² = m²` with `p⁺ ≠ 0` the projection `P₊` maps the
solution space of the Dirac equation isomorphically onto the good spinors, so the solutions are
parametrised by their two good components. For a quark field the factor `1/p⁺` becomes the
inverse light-cone derivative `1/∂⁺` of light-cone quantisation.

This is the origin of the counting of collinear twist: good components carry twist one, bad
components twist two, and the equation-of-motion relations among higher-twist correlators come
from eliminating the bad components through the constraint equation.

## Main definitions

* `LightConeBasis.goodProjector`, `LightConeBasis.badProjector`: the projectors `P₊ = ½ γ⁻γ⁺`
  and `P₋ = ½ γ⁺γ⁻` on Dirac spinors.

## Main statements

* `LightConeBasis.goodProjector_add_badProjector`, `LightConeBasis.goodProjector_mul_self`,
  `LightConeBasis.goodProjector_mul_badProjector`: `P₊`, `P₋` are complementary orthogonal
  idempotents.
* `LightConeBasis.ker_gammaMatrix_nPlus`, `LightConeBasis.ker_gammaMatrix_nMinus`: the good
  spinors are the kernel of `γ⁻`, the bad spinors the kernel of `γ⁺`.
* `LightConeBasis.finrank_range_goodProjector`, `LightConeBasis.finrank_range_badProjector`:
  the good and the bad spinors each form a two-dimensional space.
* `LightConeBasis.commute_goodProjector_gamma5`: the good/bad split commutes with chirality.
* `LightConeBasis.gammaMatrix_sub_smul_one_apply_eq_zero_iff`: the Dirac equation is equivalent
  to the constraint equation together with the dynamical equation.
* `LightConeBasis.badProjector_apply_eq_of_apply_eq_zero`: the constraint equation solved for
  the bad component, `ψ₋ = (2p⁺)⁻¹ (/p_T + m) γ⁺ ψ₊`.
* `LightConeBasis.finrank_ker_gammaMatrix_sub_smul_one`: on the mass shell with `p⁺ ≠ 0` the
  solutions of the Dirac equation form a two-dimensional space, mapped isomorphically onto the
  good spinors by `P₊`.

## References

* J. B. Kogut and D. E. Soper, *Quantum electrodynamics in the infinite-momentum frame*,
  Phys. Rev. D1 (1970) 2901.
* R. L. Jaffe, *Spin, twist and hadron structure in deep inelastic processes*, hep-ph/9602236.
* J. C. Collins, *Foundations of Perturbative QCD*, Cambridge University Press (2011), §6.
-/

public section

noncomputable section

namespace LinearMap.BilinForm.LightConeBasis

open Fermion Fermion.Dirac Module LinearMap
open Lorentz.Vector (minkowskiProduct)
open scoped Lorentz.Vector

variable (L : LightConeBasis (minkowskiProduct (d := 3)).toBilinForm)

/-! ### Clifford multiplication by the light-cone vectors -/

/-- `γ⁻ = /n₊` squares to zero. -/
@[simp]
theorem gammaMatrix_nPlus_mul_self : gammaMatrix L.nPlus * gammaMatrix L.nPlus = 0 := by
  rw [gammaMatrix_mul_self, ← ContinuousLinearMap.toBilinForm_apply, L.nPlus_nPlus_eq_zero,
    zero_smul]

/-- `γ⁺ = /n₋` squares to zero. -/
@[simp]
theorem gammaMatrix_nMinus_mul_self : gammaMatrix L.nMinus * gammaMatrix L.nMinus = 0 := by
  simpa only [swap_nPlus] using L.swap.gammaMatrix_nPlus_mul_self

/-- The anticommutator `γ⁻γ⁺ + γ⁺γ⁻ = 2`. -/
theorem gammaMatrix_nPlus_mul_gammaMatrix_nMinus_add :
    gammaMatrix L.nPlus * gammaMatrix L.nMinus + gammaMatrix L.nMinus * gammaMatrix L.nPlus =
      2 := by
  rw [gammaMatrix_anticomm, ← ContinuousLinearMap.toBilinForm_apply, L.nPlus_nMinus_eq_one,
    mul_one, two_smul, one_add_one_eq_two]

/-- Clifford multiplication by a transverse vector anticommutes with `γ⁻ = /n₊`. -/
theorem gammaMatrix_nPlus_mul_gammaMatrix_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) :
    gammaMatrix L.nPlus * gammaMatrix t = -(gammaMatrix t * gammaMatrix L.nPlus) := by
  have h := gammaMatrix_anticomm L.nPlus t
  rw [← ContinuousLinearMap.toBilinForm_apply, ← minus_apply, (L.mem_transverse_iff.1 ht).2,
    mul_zero, zero_smul] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Clifford multiplication by a transverse vector anticommutes with `γ⁺ = /n₋`. -/
theorem gammaMatrix_nMinus_mul_gammaMatrix_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) :
    gammaMatrix L.nMinus * gammaMatrix t = -(gammaMatrix t * gammaMatrix L.nMinus) := by
  simpa only [swap_nPlus] using
    L.swap.gammaMatrix_nPlus_mul_gammaMatrix_of_mem_transverse (by rwa [transverse_swap])

/-- The light-cone decomposition of Clifford multiplication, `/p = p⁺ γ⁻ + p⁻ γ⁺ + /p_T`. -/
theorem gammaMatrix_eq_plus_smul_add_minus_smul_add (p : Lorentz.Vector) :
    gammaMatrix p = L.plus p • gammaMatrix L.nPlus + L.minus p • gammaMatrix L.nMinus +
      gammaMatrix (L.transverseProj p) := by
  conv_lhs => rw [← L.plus_smul_add_minus_smul_add_transverseProj_eq p]
  simp only [map_add, map_smul]

/-! ### The good and bad projectors -/

/-- The good projector `P₊ = ½ γ⁻ γ⁺ = ½ /n₊ /n₋` on Dirac spinors. -/
def goodProjector : Module.End ℂ Dirac :=
  (2 : ℂ)⁻¹ • (gammaMatrix L.nPlus * gammaMatrix L.nMinus)

/-- The bad projector `P₋ = ½ γ⁺ γ⁻ = ½ /n₋ /n₊` on Dirac spinors. -/
def badProjector : Module.End ℂ Dirac :=
  (2 : ℂ)⁻¹ • (gammaMatrix L.nMinus * gammaMatrix L.nPlus)

theorem goodProjector_def :
    L.goodProjector = (2 : ℂ)⁻¹ • (gammaMatrix L.nPlus * gammaMatrix L.nMinus) :=
  (rfl)

theorem badProjector_def :
    L.badProjector = (2 : ℂ)⁻¹ • (gammaMatrix L.nMinus * gammaMatrix L.nPlus) :=
  (rfl)

/-- Exchanging `n₊` and `n₋` exchanges the good and the bad projector. -/
@[simp]
theorem goodProjector_swap : L.swap.goodProjector = L.badProjector := by
  rw [goodProjector_def, badProjector_def, swap_nPlus, swap_nMinus]

/-- Exchanging `n₊` and `n₋` exchanges the bad and the good projector. -/
@[simp]
theorem badProjector_swap : L.swap.badProjector = L.goodProjector := by
  rw [goodProjector_def, badProjector_def, swap_nPlus, swap_nMinus]

/-- `γ⁻γ⁺ = 2 P₊`. -/
theorem gammaMatrix_nPlus_mul_gammaMatrix_nMinus :
    gammaMatrix L.nPlus * gammaMatrix L.nMinus = (2 : ℂ) • L.goodProjector := by
  rw [goodProjector_def, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]

/-- `γ⁺γ⁻ = 2 P₋`. -/
theorem gammaMatrix_nMinus_mul_gammaMatrix_nPlus :
    gammaMatrix L.nMinus * gammaMatrix L.nPlus = (2 : ℂ) • L.badProjector := by
  rw [badProjector_def, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]

@[simp]
theorem goodProjector_add_badProjector : L.goodProjector + L.badProjector = 1 := by
  have two_eq_two_smul_one : (2 : Module.End ℂ Dirac) = (2 : ℂ) • 1 := by
    simp [ofNat_smul_eq_nsmul]
  rw [goodProjector_def, badProjector_def, ← smul_add,
    gammaMatrix_nPlus_mul_gammaMatrix_nMinus_add, two_eq_two_smul_one, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul]

@[simp]
theorem badProjector_add_goodProjector : L.badProjector + L.goodProjector = 1 := by
  rw [add_comm, goodProjector_add_badProjector]

@[simp]
theorem goodProjector_apply_add_badProjector_apply (ψ : Dirac) :
    L.goodProjector ψ + L.badProjector ψ = ψ := by
  rw [← LinearMap.add_apply, goodProjector_add_badProjector, Module.End.one_apply]

theorem badProjector_eq_one_sub : L.badProjector = 1 - L.goodProjector :=
  eq_sub_of_add_eq' L.goodProjector_add_badProjector

@[simp]
theorem goodProjector_mul_badProjector : L.goodProjector * L.badProjector = 0 := by
  rw [goodProjector_def, badProjector_def, smul_mul_smul_comm,
    mul_assoc (gammaMatrix L.nPlus), ← mul_assoc (gammaMatrix L.nMinus),
    gammaMatrix_nMinus_mul_self, zero_mul, mul_zero, smul_zero]

@[simp]
theorem badProjector_mul_goodProjector : L.badProjector * L.goodProjector = 0 := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.goodProjector_mul_badProjector

@[simp]
theorem goodProjector_mul_self : L.goodProjector * L.goodProjector = L.goodProjector := by
  calc L.goodProjector * L.goodProjector
      = L.goodProjector * (L.goodProjector + L.badProjector) := by
        rw [mul_add, goodProjector_mul_badProjector, add_zero]
    _ = L.goodProjector := by rw [goodProjector_add_badProjector, mul_one]

@[simp]
theorem badProjector_mul_self : L.badProjector * L.badProjector = L.badProjector := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.goodProjector_mul_self

/-- The good projector is idempotent. -/
theorem isIdempotentElem_goodProjector : IsIdempotentElem L.goodProjector :=
  L.goodProjector_mul_self

/-- The bad projector is idempotent. -/
theorem isIdempotentElem_badProjector : IsIdempotentElem L.badProjector :=
  L.badProjector_mul_self

/-- `γ⁻ ψ₊ = 0`. -/
@[simp]
theorem gammaMatrix_nPlus_mul_goodProjector : gammaMatrix L.nPlus * L.goodProjector = 0 := by
  rw [goodProjector_def, mul_smul_comm, ← mul_assoc, gammaMatrix_nPlus_mul_self, zero_mul,
    smul_zero]

/-- `γ⁺ ψ₋ = 0`. -/
@[simp]
theorem gammaMatrix_nMinus_mul_badProjector : gammaMatrix L.nMinus * L.badProjector = 0 := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.gammaMatrix_nPlus_mul_goodProjector

/-- `γ⁺ ψ₊ = γ⁺ ψ`. -/
@[simp]
theorem gammaMatrix_nMinus_mul_goodProjector :
    gammaMatrix L.nMinus * L.goodProjector = gammaMatrix L.nMinus := by
  conv_rhs => rw [← mul_one (gammaMatrix L.nMinus), ← L.badProjector_add_goodProjector, mul_add,
    gammaMatrix_nMinus_mul_badProjector, zero_add]

/-- `γ⁻ ψ₋ = γ⁻ ψ`. -/
@[simp]
theorem gammaMatrix_nPlus_mul_badProjector :
    gammaMatrix L.nPlus * L.badProjector = gammaMatrix L.nPlus := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.gammaMatrix_nMinus_mul_goodProjector

/-- `P₊ γ⁺ = 0`: the image of `γ⁺` consists of bad spinors. -/
@[simp]
theorem goodProjector_mul_gammaMatrix_nMinus : L.goodProjector * gammaMatrix L.nMinus = 0 := by
  rw [goodProjector_def, smul_mul_assoc, mul_assoc, gammaMatrix_nMinus_mul_self, mul_zero,
    smul_zero]

/-- `P₋ γ⁻ = 0`: the image of `γ⁻` consists of good spinors. -/
@[simp]
theorem badProjector_mul_gammaMatrix_nPlus : L.badProjector * gammaMatrix L.nPlus = 0 := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.goodProjector_mul_gammaMatrix_nMinus

/-! ### The good and bad subspaces -/

/-- The good spinors are the kernel of `γ⁻ = /n₊`. -/
theorem ker_gammaMatrix_nPlus : ker (gammaMatrix L.nPlus) = range L.goodProjector := by
  ext ψ
  refine ⟨fun h => ⟨ψ, ?_⟩, ?_⟩
  · have hbad : L.badProjector ψ = 0 := by
      rw [mem_ker] at h
      rw [badProjector_def, smul_apply, Module.End.mul_apply, h, map_zero, smul_zero]
    rw [← add_zero (L.goodProjector ψ), ← hbad, ← LinearMap.add_apply,
      goodProjector_add_badProjector, Module.End.one_apply]
  · rintro ⟨χ, rfl⟩
    rw [mem_ker, ← Module.End.mul_apply, gammaMatrix_nPlus_mul_goodProjector,
      LinearMap.zero_apply]

/-- The bad spinors are the kernel of `γ⁺ = /n₋`. -/
theorem ker_gammaMatrix_nMinus : ker (gammaMatrix L.nMinus) = range L.badProjector := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.ker_gammaMatrix_nPlus

/-- The kernel of the good projector is the space of bad spinors. -/
theorem ker_goodProjector : ker L.goodProjector = range L.badProjector := by
  rw [L.isIdempotentElem_goodProjector.ker_eq_range_one_sub, badProjector_eq_one_sub]

/-- The kernel of the bad projector is the space of good spinors. -/
theorem ker_badProjector : ker L.badProjector = range L.goodProjector := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.ker_goodProjector

/-- The Dirac spinors are the direct sum of the good and the bad spinors. -/
theorem isCompl_range_goodProjector_range_badProjector :
    IsCompl (range L.goodProjector) (range L.badProjector) := by
  rw [← ker_goodProjector]
  exact L.isIdempotentElem_goodProjector.isProj_range.isCompl

/-- The trace of the good projector is two. -/
@[simp]
theorem trace_goodProjector : trace ℂ Dirac L.goodProjector = 2 := by
  have : Module.Finite ℂ Dirac := .of_basis chiralBasis
  have hsymm : trace ℂ Dirac L.badProjector = trace ℂ Dirac L.goodProjector := by
    rw [goodProjector_def, badProjector_def, map_smul, map_smul, trace_mul_comm]
  have h := congrArg (trace ℂ Dirac) L.goodProjector_add_badProjector
  rw [map_add, hsymm, trace_one, finrank_eq_card_basis chiralBasis] at h
  norm_num at h
  linear_combination h / 2

@[simp]
theorem trace_badProjector : trace ℂ Dirac L.badProjector = 2 := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.trace_goodProjector

/-- The good spinors form a two-dimensional space. -/
@[simp]
theorem finrank_range_goodProjector : finrank ℂ (range L.goodProjector) = 2 := by
  have : Module.Finite ℂ Dirac := .of_basis chiralBasis
  have h := L.isIdempotentElem_goodProjector.isProj_range.trace
  rw [trace_goodProjector] at h
  exact_mod_cast h.symm

/-- The bad spinors form a two-dimensional space. -/
@[simp]
theorem finrank_range_badProjector : finrank ℂ (range L.badProjector) = 2 := by
  rw [← goodProjector_swap]
  exact L.swap.finrank_range_goodProjector

/-! ### Compatibility with chirality and with transverse Clifford multiplication -/

/-- The good projector commutes with the chirality `γ⁵`. -/
theorem commute_goodProjector_gamma5 : Commute L.goodProjector gamma5 := by
  rw [goodProjector_def, commute_iff_eq, smul_mul_assoc, mul_smul_comm, ← mul_assoc gamma5,
    gamma5_mul_gammaMatrix, neg_mul, mul_assoc (gammaMatrix L.nPlus) gamma5,
    gamma5_mul_gammaMatrix, mul_neg, neg_neg, mul_assoc]

/-- The bad projector commutes with the chirality `γ⁵`. -/
theorem commute_badProjector_gamma5 : Commute L.badProjector gamma5 := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.commute_goodProjector_gamma5

/-- The good projector commutes with Clifford multiplication by a transverse vector. -/
theorem commute_goodProjector_gammaMatrix_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) : Commute L.goodProjector (gammaMatrix t) := by
  rw [goodProjector_def, commute_iff_eq, smul_mul_assoc, mul_smul_comm,
    mul_assoc (gammaMatrix L.nPlus), L.gammaMatrix_nMinus_mul_gammaMatrix_of_mem_transverse ht,
    mul_neg, ← mul_assoc (gammaMatrix L.nPlus),
    L.gammaMatrix_nPlus_mul_gammaMatrix_of_mem_transverse ht, neg_mul, neg_neg, mul_assoc]

/-- The bad projector commutes with Clifford multiplication by a transverse vector. -/
theorem commute_badProjector_gammaMatrix_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) : Commute L.badProjector (gammaMatrix t) := by
  simpa only [goodProjector_swap, badProjector_swap, swap_nPlus, swap_nMinus] using
    L.swap.commute_goodProjector_gammaMatrix_of_mem_transverse
      (by rwa [transverse_swap])

/-! ### The Dirac equation in light-cone components -/

section DiracEquation

variable (p : Lorentz.Vector) (m : ℝ)

/-- The Dirac operator of a momentum mode projected with `γ⁺`,
`γ⁺ (/p - m) = 2 p⁺ P₋ - (/p_T + m) γ⁺ P₊`. -/
theorem gammaMatrix_nMinus_mul_gammaMatrix_sub_smul_one :
    gammaMatrix L.nMinus * (gammaMatrix p - m • 1) =
      (2 * L.plus p) • L.badProjector -
        (gammaMatrix (L.transverseProj p) + m • 1) * (gammaMatrix L.nMinus * L.goodProjector) := by
  have ht := L.isProj_transverseProj.map_mem p
  rw [gammaMatrix_nMinus_mul_goodProjector, L.gammaMatrix_eq_plus_smul_add_minus_smul_add p,
    mul_sub, mul_add, mul_add, mul_smul_comm, mul_smul_comm, gammaMatrix_nMinus_mul_self,
    smul_zero, add_zero, L.gammaMatrix_nMinus_mul_gammaMatrix_of_mem_transverse ht,
    gammaMatrix_nMinus_mul_gammaMatrix_nPlus, mul_smul_comm, mul_one, add_mul, smul_mul_assoc,
    one_mul]
  module

/-- The Dirac operator of a momentum mode projected with `γ⁻`,
`γ⁻ (/p - m) = 2 p⁻ P₊ - (/p_T + m) γ⁻ P₋`. -/
theorem gammaMatrix_nPlus_mul_gammaMatrix_sub_smul_one :
    gammaMatrix L.nPlus * (gammaMatrix p - m • 1) =
      (2 * L.minus p) • L.goodProjector -
        (gammaMatrix (L.transverseProj p) + m • 1) * (gammaMatrix L.nPlus * L.badProjector) := by
  simpa only [swap_nMinus, plus_swap, badProjector_swap, goodProjector_swap,
    transverseProj_swap] using L.swap.gammaMatrix_nMinus_mul_gammaMatrix_sub_smul_one p m

/-- The Dirac equation `(/p - m) ψ = 0` in light-cone components: it holds iff both the
constraint equation `2 p⁺ ψ₋ = (/p_T + m) γ⁺ ψ₊` and the dynamical equation
`2 p⁻ ψ₊ = (/p_T + m) γ⁻ ψ₋` hold. -/
theorem gammaMatrix_sub_smul_one_apply_eq_zero_iff (ψ : Dirac) :
    (gammaMatrix p - m • 1) ψ = 0 ↔
      (2 * L.plus p) • L.badProjector ψ =
          (gammaMatrix (L.transverseProj p) + m • 1) (gammaMatrix L.nMinus (L.goodProjector ψ)) ∧
      (2 * L.minus p) • L.goodProjector ψ =
          (gammaMatrix (L.transverseProj p) + m • 1) (gammaMatrix L.nPlus (L.badProjector ψ)) := by
  have hminus := LinearMap.congr_fun (L.gammaMatrix_nMinus_mul_gammaMatrix_sub_smul_one p m) ψ
  have hplus := LinearMap.congr_fun (L.gammaMatrix_nPlus_mul_gammaMatrix_sub_smul_one p m) ψ
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at hminus hplus ⊢
  rw [← sub_eq_zero (a := (2 * L.plus p) • _), ← hminus,
    ← sub_eq_zero (a := (2 * L.minus p) • _), ← hplus]
  refine ⟨fun h => by simp [h], fun ⟨h₁, h₂⟩ => ?_⟩
  have hmem : gammaMatrix p ψ - m • ψ ∈
      ker (gammaMatrix L.nPlus) ⊓ ker (gammaMatrix L.nMinus) :=
    Submodule.mem_inf.2 ⟨mem_ker.2 h₂, mem_ker.2 h₁⟩
  rwa [ker_gammaMatrix_nPlus, ker_gammaMatrix_nMinus,
    L.isCompl_range_goodProjector_range_badProjector.inf_eq_bot, Submodule.mem_bot] at hmem

variable {p m}

/-- The constraint equation solved for the bad component: for `p⁺ ≠ 0` a solution of the Dirac
equation has `ψ₋ = (2 p⁺)⁻¹ (/p_T + m) γ⁺ ψ₊`. -/
theorem badProjector_apply_eq_of_apply_eq_zero (hp : L.plus p ≠ 0) {ψ : Dirac}
    (h : (gammaMatrix p - m • 1) ψ = 0) :
    L.badProjector ψ = (2 * L.plus p)⁻¹ •
      (gammaMatrix (L.transverseProj p) + m • 1) (gammaMatrix L.nMinus (L.goodProjector ψ)) := by
  rw [eq_inv_smul_iff₀ (mul_ne_zero two_ne_zero hp)]
  exact ((L.gammaMatrix_sub_smul_one_apply_eq_zero_iff p m ψ).1 h).1

/-- For `p⁺ ≠ 0` a solution of the Dirac equation is determined by its good component. -/
theorem injOn_goodProjector (hp : L.plus p ≠ 0) :
    Set.InjOn L.goodProjector (ker (gammaMatrix p - m • 1)) := by
  intro ψ₁ h₁ ψ₂ h₂ h
  have e := L.badProjector_apply_eq_of_apply_eq_zero hp (mem_ker.1 h₁)
  rw [h, ← L.badProjector_apply_eq_of_apply_eq_zero hp (mem_ker.1 h₂)] at e
  rw [← L.goodProjector_apply_add_badProjector_apply ψ₁, h, e,
    goodProjector_apply_add_badProjector_apply]

/-- `(/t + m) γ⁻ (/t + m) γ⁺ = 2 (m² - t²) P₊` for a transverse vector `t`. -/
private theorem mul_gammaMatrix_nPlus_mul_mul_gammaMatrix_nMinus {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) (m : ℝ) :
    (gammaMatrix t + m • 1) * gammaMatrix L.nPlus *
        ((gammaMatrix t + m • 1) * gammaMatrix L.nMinus) =
      (2 * (m ^ 2 - ⟪t, t⟫ₘ)) • L.goodProjector := by
  have haT : gammaMatrix L.nPlus * (gammaMatrix t + m • 1) =
      (m • 1 - gammaMatrix t) * gammaMatrix L.nPlus := by
    rw [mul_add, L.gammaMatrix_nPlus_mul_gammaMatrix_of_mem_transverse ht, mul_smul_comm, mul_one,
      sub_mul, smul_mul_assoc, one_mul]
    abel
  have hTT : (gammaMatrix t + m • 1) * (m • 1 - gammaMatrix t) = (m ^ 2 - ⟪t, t⟫ₘ) • 1 := by
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      gammaMatrix_mul_self]
    module
  calc (gammaMatrix t + m • 1) * gammaMatrix L.nPlus *
        ((gammaMatrix t + m • 1) * gammaMatrix L.nMinus)
      = (gammaMatrix t + m • 1) * (gammaMatrix L.nPlus * (gammaMatrix t + m • 1)) *
          gammaMatrix L.nMinus := by simp only [mul_assoc]
    _ = (gammaMatrix t + m • 1) * (m • 1 - gammaMatrix t) *
          (gammaMatrix L.nPlus * gammaMatrix L.nMinus) := by rw [haT]; simp only [mul_assoc]
    _ = (2 * (m ^ 2 - ⟪t, t⟫ₘ)) • L.goodProjector := by
      rw [hTT, gammaMatrix_nPlus_mul_gammaMatrix_nMinus, smul_mul_assoc, one_mul]
      module

/-- On the mass shell `p² = m²` with `p⁺ ≠ 0`, every good spinor `χ` is the good component of a
solution of the Dirac equation, namely of `χ + (2 p⁺)⁻¹ (/p_T + m) γ⁺ χ`. -/
theorem exists_apply_eq_zero_and_goodProjector_apply_eq (hshell : ⟪p, p⟫ₘ = m ^ 2)
    (hp : L.plus p ≠ 0) {χ : Dirac} (hχ : χ ∈ range L.goodProjector) :
    ∃ ψ, (gammaMatrix p - m • 1) ψ = 0 ∧ L.goodProjector ψ = χ := by
  have ht := L.isProj_transverseProj.map_mem p
  have hχ' : L.goodProjector χ = χ := by
    obtain ⟨φ, rfl⟩ := hχ
    rw [← Module.End.mul_apply, goodProjector_mul_self]
  let T := gammaMatrix (L.transverseProj p) + m • 1
  -- the bad component prescribed by the constraint equation
  let η := (2 * L.plus p)⁻¹ • T (gammaMatrix L.nMinus χ)
  have hη : L.goodProjector η = 0 := by
    have hc : Commute L.goodProjector T :=
      (L.commute_goodProjector_gammaMatrix_of_mem_transverse ht).add_right
        ((Commute.one_right _).smul_right m)
    have h0 : L.goodProjector * T * gammaMatrix L.nMinus = 0 := by
      rw [hc.eq, mul_assoc, goodProjector_mul_gammaMatrix_nMinus, mul_zero]
    rw [LinearMap.map_smul_of_tower, ← Module.End.mul_apply, ← Module.End.mul_apply, h0,
      LinearMap.zero_apply, smul_zero]
  have hg : L.goodProjector (χ + η) = χ := by rw [map_add, hχ', hη, add_zero]
  have hb : L.badProjector (χ + η) = η := by
    rw [badProjector_eq_one_sub, LinearMap.sub_apply, Module.End.one_apply, hg,
      add_sub_cancel_left]
  refine ⟨χ + η, ?_, hg⟩
  rw [L.gammaMatrix_sub_smul_one_apply_eq_zero_iff, hg, hb]
  refine ⟨by rw [smul_inv_smul₀ (mul_ne_zero two_ne_zero hp)], ?_⟩
  -- the dynamical equation holds because `m² - p_T² = 2 p⁺ p⁻` on the mass shell
  have hshell' : m ^ 2 - ⟪L.transverseProj p, L.transverseProj p⟫ₘ =
      2 * (L.plus p * L.minus p) := by
    have := L.bilinForm_eq_plus_mul_minus_add
      EpsilonEridani.isSymm_toBilinForm_minkowskiProduct.isRefl p p
    simp only [ContinuousLinearMap.toBilinForm_apply] at this
    rw [← hshell, this]
    ring
  have key := LinearMap.congr_fun (L.mul_gammaMatrix_nPlus_mul_mul_gammaMatrix_nMinus ht m) χ
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hχ', hshell'] at key
  simp only [η, T, LinearMap.map_smul_of_tower]
  rw [key, smul_smul]
  congr 1
  field_simp

/-- On the mass shell `p² = m²` with `p⁺ ≠ 0`, the solutions of the Dirac equation
`(/p - m) ψ = 0` form a two-dimensional space: `P₊` maps it isomorphically onto the good
spinors. -/
theorem finrank_ker_gammaMatrix_sub_smul_one (hshell : ⟪p, p⟫ₘ = m ^ 2) (hp : L.plus p ≠ 0) :
    finrank ℂ (ker (gammaMatrix p - m • 1)) = 2 := by
  let f : ker (gammaMatrix p - m • 1) →ₗ[ℂ] range L.goodProjector :=
    L.goodProjector.restrict fun ψ _ => mem_range_self _ ψ
  have hf : Function.Bijective f := by
    refine ⟨fun ψ₁ ψ₂ h => Subtype.ext (L.injOn_goodProjector hp ψ₁.2 ψ₂.2 ?_), ?_⟩
    · simpa only [f, coe_restrict_apply] using congr_arg Subtype.val h
    · rintro ⟨χ, hχ⟩
      obtain ⟨ψ, hψ, rfl⟩ := L.exists_apply_eq_zero_and_goodProjector_apply_eq hshell hp hχ
      exact ⟨⟨ψ, mem_ker.2 hψ⟩, Subtype.ext (coe_restrict_apply _ _)⟩
  rw [(LinearEquiv.ofBijective f hf).finrank_eq, finrank_range_goodProjector]

end DiracEquation

end LightConeBasis

end LinearMap.BilinForm
