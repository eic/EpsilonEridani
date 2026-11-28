/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Relativity.Fermions.Dirac.BasicExtensions
public import EpsilonEridani.Relativity.Fermions.Dirac.GammaMatricesExtensions
public import EpsilonEridani.Relativity.LightConeBasis
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
* `LightConeBasis.goodProjectorEquiv`: on the mass shell with `p⁺ ≠ 0`, the restriction of `P₊`
  to a linear equivalence from the solutions of the Dirac equation onto the good spinors.

## Main statements

* `LightConeBasis.goodProjector_add_badProjector`, `LightConeBasis.goodProjector_mul_self`,
  `LightConeBasis.goodProjector_mul_badProjector_eq_zero`: `P₊`, `P₋` are complementary
  orthogonal idempotents.
* `LightConeBasis.ker_gammaMatrix_nPlus_eq_range_goodProjector`,
  `LightConeBasis.ker_gammaMatrix_nMinus_eq_range_badProjector`: the good spinors are the kernel
  of `γ⁻`, the bad spinors the kernel of `γ⁺`; pointwise,
  `LightConeBasis.mem_range_goodProjector_iff` and `LightConeBasis.mem_range_badProjector_iff`.
* `LightConeBasis.finrank_range_goodProjector_eq_two`,
  `LightConeBasis.finrank_range_badProjector_eq_two`:
  the good and the bad spinors each form a two-dimensional space.
* `LightConeBasis.commute_goodProjector_of_anticomm`: an endomorphism anticommuting with `γ⁻` and
  `γ⁺` commutes with `P₊`; in particular (`LightConeBasis.commute_goodProjector_gamma5`) the
  good/bad split commutes with chirality; `γ⁵` and transverse Clifford multiplication preserve the
  good and the bad spinors (`LightConeBasis.gamma5_apply_mem_range_goodProjector`,
  `LightConeBasis.gammaMatrix_apply_mem_range_goodProjector_of_mem_transverse`, and duals), as
  do the chiral projectors (`LightConeBasis.leftChiralProjector_apply_mem_range_goodProjector`,
  and duals).
* `LightConeBasis.gammaMatrix_sub_smul_one_apply_eq_zero_iff`: the Dirac equation is equivalent
  to the constraint equation together with the dynamical equation.
* `LightConeBasis.badProjector_apply_eq_of_gammaMatrix_sub_smul_one_apply_eq_zero`: the
  constraint equation solved for the bad component, `ψ₋ = (2p⁺)⁻¹ (/p_T + m) γ⁺ ψ₊`.
* `LightConeBasis.gammaMatrix_sub_smul_one_apply_add_inv_smul_eq_zero`,
  `LightConeBasis.coe_goodProjectorEquiv_symm_apply`: conversely, on the mass shell with
  `p⁺ ≠ 0` every good spinor `χ` is the good component of the solution
  `χ + (2p⁺)⁻¹ (/p_T + m) γ⁺ χ`.
* `Fermion.Dirac.finrank_ker_gammaMatrix_sub_smul_one_eq_two`: on the mass shell with `p ≠ 0`
  the solutions of the Dirac equation form a two-dimensional space.

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
theorem gammaMatrix_nPlus_mul_self_eq_zero :
    gammaMatrix L.nPlus * gammaMatrix L.nPlus = 0 :=
  gammaMatrix_mul_self_eq_zero_of_minkowskiProduct_self_eq_zero (by simp)

/-- `γ⁺ = /n₋` squares to zero. -/
@[simp]
theorem gammaMatrix_nMinus_mul_self_eq_zero :
    gammaMatrix L.nMinus * gammaMatrix L.nMinus = 0 :=
  gammaMatrix_mul_self_eq_zero_of_minkowskiProduct_self_eq_zero (by simp)

/-- `γ⁻ γ⁻ ψ = 0`. -/
@[simp]
theorem gammaMatrix_nPlus_gammaMatrix_nPlus_apply_eq_zero (ψ : Dirac) :
    gammaMatrix L.nPlus (gammaMatrix L.nPlus ψ) = 0 := by
  simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun L.gammaMatrix_nPlus_mul_self_eq_zero ψ

/-- `γ⁺ γ⁺ ψ = 0`. -/
@[simp]
theorem gammaMatrix_nMinus_gammaMatrix_nMinus_apply_eq_zero (ψ : Dirac) :
    gammaMatrix L.nMinus (gammaMatrix L.nMinus ψ) = 0 := by
  simpa only [Module.End.mul_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun L.gammaMatrix_nMinus_mul_self_eq_zero ψ

/-- The anticommutator `γ⁻γ⁺ + γ⁺γ⁻ = 2`. -/
theorem gammaMatrix_nPlus_anticomm_nMinus :
    gammaMatrix L.nPlus * gammaMatrix L.nMinus + gammaMatrix L.nMinus * gammaMatrix L.nPlus =
      2 := by
  rw [gammaMatrix_anticomm]
  simp [ofNat_smul_eq_nsmul]

/-- Clifford multiplication by a vector with vanishing minus component `t⁻ = n₊ · t`
anticommutes with `γ⁻ = /n₊`. -/
theorem gammaMatrix_nPlus_mul_gammaMatrix_eq_neg_mul_of_minus_eq_zero {t : Lorentz.Vector}
    (ht : L.minus t = 0) :
    gammaMatrix L.nPlus * gammaMatrix t = -(gammaMatrix t * gammaMatrix L.nPlus) :=
  gammaMatrix_mul_gammaMatrix_eq_neg_mul_of_minkowskiProduct_eq_zero (by simp [ht])

/-- Clifford multiplication by a vector with vanishing plus component `t⁺ = n₋ · t`
anticommutes with `γ⁺ = /n₋`. -/
theorem gammaMatrix_nMinus_mul_gammaMatrix_eq_neg_mul_of_plus_eq_zero {t : Lorentz.Vector}
    (ht : L.plus t = 0) :
    gammaMatrix L.nMinus * gammaMatrix t = -(gammaMatrix t * gammaMatrix L.nMinus) :=
  gammaMatrix_mul_gammaMatrix_eq_neg_mul_of_minkowskiProduct_eq_zero (by simp [ht])

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

/-- `P₊ = ½ γ⁻ γ⁺`. -/
theorem goodProjector_def :
    L.goodProjector = (2 : ℂ)⁻¹ • (gammaMatrix L.nPlus * gammaMatrix L.nMinus) :=
  (rfl)

/-- `P₋ = ½ γ⁺ γ⁻`. -/
theorem badProjector_def :
    L.badProjector = (2 : ℂ)⁻¹ • (gammaMatrix L.nMinus * gammaMatrix L.nPlus) :=
  (rfl)

/-- `P₊ ψ = ½ γ⁻ γ⁺ ψ`. -/
theorem goodProjector_apply (ψ : Dirac) :
    L.goodProjector ψ = (2 : ℂ)⁻¹ • gammaMatrix L.nPlus (gammaMatrix L.nMinus ψ) :=
  (rfl)

/-- `P₋ ψ = ½ γ⁺ γ⁻ ψ`. -/
theorem badProjector_apply (ψ : Dirac) :
    L.badProjector ψ = (2 : ℂ)⁻¹ • gammaMatrix L.nMinus (gammaMatrix L.nPlus ψ) :=
  (rfl)

/-- Exchanging `n₊` and `n₋` exchanges the good and the bad projector. -/
@[simp]
theorem goodProjector_swap : L.swap.goodProjector = L.badProjector := by
  rw [goodProjector_def, badProjector_def, nPlus_swap, nMinus_swap]

/-- Exchanging `n₊` and `n₋` exchanges the bad and the good projector. -/
@[simp]
theorem badProjector_swap : L.swap.badProjector = L.goodProjector := by
  rw [goodProjector_def, badProjector_def, nPlus_swap, nMinus_swap]

/-- `γ⁻γ⁺ = 2 P₊`. -/
theorem gammaMatrix_nPlus_mul_gammaMatrix_nMinus_eq_two_smul_goodProjector :
    gammaMatrix L.nPlus * gammaMatrix L.nMinus = (2 : ℂ) • L.goodProjector := by
  rw [goodProjector_def, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]

/-- `γ⁺γ⁻ = 2 P₋`. -/
theorem gammaMatrix_nMinus_mul_gammaMatrix_nPlus_eq_two_smul_badProjector :
    gammaMatrix L.nMinus * gammaMatrix L.nPlus = (2 : ℂ) • L.badProjector := by
  rw [badProjector_def, smul_smul, mul_inv_cancel₀ two_ne_zero, one_smul]

/-- The projectors are complementary, `P₊ + P₋ = 1`. -/
@[simp]
theorem goodProjector_add_badProjector : L.goodProjector + L.badProjector = 1 := by
  rw [goodProjector_def, badProjector_def, ← smul_add, gammaMatrix_nPlus_anticomm_nMinus,
    inv_smul_eq_iff₀ two_ne_zero]
  simp [ofNat_smul_eq_nsmul]

/-- The projectors are complementary, `P₋ + P₊ = 1`. -/
@[simp]
theorem badProjector_add_goodProjector : L.badProjector + L.goodProjector = 1 := by
  rw [add_comm, goodProjector_add_badProjector]

/-- Every Dirac spinor is the sum of its good and bad components, `ψ₊ + ψ₋ = ψ`. -/
@[simp]
theorem goodProjector_apply_add_badProjector_apply (ψ : Dirac) :
    L.goodProjector ψ + L.badProjector ψ = ψ := by
  rw [← LinearMap.add_apply, goodProjector_add_badProjector, Module.End.one_apply]

/-- `P₊ = 1 - P₋`. -/
theorem goodProjector_eq_one_sub : L.goodProjector = 1 - L.badProjector :=
  eq_sub_of_add_eq L.goodProjector_add_badProjector

/-- `P₋ = 1 - P₊`. -/
theorem badProjector_eq_one_sub : L.badProjector = 1 - L.goodProjector :=
  eq_sub_of_add_eq' L.goodProjector_add_badProjector

/-- `P₊ P₋ ψ = 0`. -/
@[simp]
theorem goodProjector_badProjector_apply_eq_zero (ψ : Dirac) :
    L.goodProjector (L.badProjector ψ) = 0 := by
  simp [goodProjector_apply, badProjector_apply]

/-- `P₋ P₊ ψ = 0`. -/
@[simp]
theorem badProjector_goodProjector_apply_eq_zero (ψ : Dirac) :
    L.badProjector (L.goodProjector ψ) = 0 := by
  simp [goodProjector_apply, badProjector_apply]

/-- The projectors are orthogonal, `P₊ P₋ = 0`. -/
@[simp]
theorem goodProjector_mul_badProjector_eq_zero : L.goodProjector * L.badProjector = 0 :=
  LinearMap.ext fun ψ => by simp

/-- The projectors are orthogonal, `P₋ P₊ = 0`. -/
@[simp]
theorem badProjector_mul_goodProjector_eq_zero : L.badProjector * L.goodProjector = 0 :=
  LinearMap.ext fun ψ => by simp

/-- The good projector is idempotent, `P₊² = P₊`. -/
@[simp]
theorem goodProjector_mul_self : L.goodProjector * L.goodProjector = L.goodProjector := by
  calc L.goodProjector * L.goodProjector
      = L.goodProjector * (L.goodProjector + L.badProjector) := by
        rw [mul_add, goodProjector_mul_badProjector_eq_zero, add_zero]
    _ = L.goodProjector := by rw [goodProjector_add_badProjector, mul_one]

/-- The bad projector is idempotent, `P₋² = P₋`. -/
@[simp]
theorem badProjector_mul_self : L.badProjector * L.badProjector = L.badProjector := by
  simpa only [goodProjector_swap, badProjector_swap, nPlus_swap, nMinus_swap] using
    L.swap.goodProjector_mul_self

/-- `P₊ P₊ ψ = P₊ ψ`. -/
@[simp]
theorem goodProjector_goodProjector_apply (ψ : Dirac) :
    L.goodProjector (L.goodProjector ψ) = L.goodProjector ψ := by
  simpa only [Module.End.mul_apply] using LinearMap.congr_fun L.goodProjector_mul_self ψ

/-- `P₋ P₋ ψ = P₋ ψ`. -/
@[simp]
theorem badProjector_badProjector_apply (ψ : Dirac) :
    L.badProjector (L.badProjector ψ) = L.badProjector ψ := by
  simpa only [Module.End.mul_apply] using LinearMap.congr_fun L.badProjector_mul_self ψ

/-- The good projector is idempotent. -/
theorem isIdempotentElem_goodProjector : IsIdempotentElem L.goodProjector :=
  L.goodProjector_mul_self

/-- The bad projector is idempotent. -/
theorem isIdempotentElem_badProjector : IsIdempotentElem L.badProjector :=
  L.badProjector_mul_self

/-- `γ⁻ P₊ = 0`. -/
@[simp]
theorem gammaMatrix_nPlus_mul_goodProjector_eq_zero :
    gammaMatrix L.nPlus * L.goodProjector = 0 := by
  simp [goodProjector_def, ← mul_assoc]

/-- `γ⁺ P₋ = 0`. -/
@[simp]
theorem gammaMatrix_nMinus_mul_badProjector_eq_zero :
    gammaMatrix L.nMinus * L.badProjector = 0 := by
  simp [badProjector_def, ← mul_assoc]

/-- `γ⁻ ψ₊ = 0`. -/
@[simp]
theorem gammaMatrix_nPlus_goodProjector_apply_eq_zero (ψ : Dirac) :
    gammaMatrix L.nPlus (L.goodProjector ψ) = 0 := by
  simp [goodProjector_apply]

/-- `γ⁺ ψ₋ = 0`. -/
@[simp]
theorem gammaMatrix_nMinus_badProjector_apply_eq_zero (ψ : Dirac) :
    gammaMatrix L.nMinus (L.badProjector ψ) = 0 := by
  simp [badProjector_apply]

/-- `γ⁺ P₊ = γ⁺`. -/
@[simp]
theorem gammaMatrix_nMinus_mul_goodProjector :
    gammaMatrix L.nMinus * L.goodProjector = gammaMatrix L.nMinus := by
  conv_rhs => rw [← mul_one (gammaMatrix L.nMinus), ← L.badProjector_add_goodProjector, mul_add,
    gammaMatrix_nMinus_mul_badProjector_eq_zero, zero_add]

/-- `γ⁻ P₋ = γ⁻`. -/
@[simp]
theorem gammaMatrix_nPlus_mul_badProjector :
    gammaMatrix L.nPlus * L.badProjector = gammaMatrix L.nPlus := by
  simpa only [goodProjector_swap, badProjector_swap, nPlus_swap, nMinus_swap] using
    L.swap.gammaMatrix_nMinus_mul_goodProjector

/-- `γ⁺ ψ₊ = γ⁺ ψ`. -/
@[simp]
theorem gammaMatrix_nMinus_goodProjector_apply (ψ : Dirac) :
    gammaMatrix L.nMinus (L.goodProjector ψ) = gammaMatrix L.nMinus ψ := by
  simpa only [Module.End.mul_apply] using
    LinearMap.congr_fun L.gammaMatrix_nMinus_mul_goodProjector ψ

/-- `γ⁻ ψ₋ = γ⁻ ψ`. -/
@[simp]
theorem gammaMatrix_nPlus_badProjector_apply (ψ : Dirac) :
    gammaMatrix L.nPlus (L.badProjector ψ) = gammaMatrix L.nPlus ψ := by
  simpa only [Module.End.mul_apply] using
    LinearMap.congr_fun L.gammaMatrix_nPlus_mul_badProjector ψ

/-- `P₊ γ⁺ = 0`: the image of `γ⁺` consists of bad spinors. -/
@[simp]
theorem goodProjector_mul_gammaMatrix_nMinus_eq_zero :
    L.goodProjector * gammaMatrix L.nMinus = 0 := by
  simp [goodProjector_def, mul_assoc]

/-- `P₋ γ⁻ = 0`: the image of `γ⁻` consists of good spinors. -/
@[simp]
theorem badProjector_mul_gammaMatrix_nPlus_eq_zero :
    L.badProjector * gammaMatrix L.nPlus = 0 := by
  simp [badProjector_def, mul_assoc]

/-- `P₊ γ⁺ ψ = 0`. -/
@[simp]
theorem goodProjector_gammaMatrix_nMinus_apply_eq_zero (ψ : Dirac) :
    L.goodProjector (gammaMatrix L.nMinus ψ) = 0 := by
  simp [goodProjector_apply]

/-- `P₋ γ⁻ ψ = 0`. -/
@[simp]
theorem badProjector_gammaMatrix_nPlus_apply_eq_zero (ψ : Dirac) :
    L.badProjector (gammaMatrix L.nPlus ψ) = 0 := by
  simp [badProjector_apply]

/-- `P₋ γ⁺ = γ⁺`: the image of `γ⁺` consists of bad spinors. -/
@[simp]
theorem badProjector_mul_gammaMatrix_nMinus :
    L.badProjector * gammaMatrix L.nMinus = gammaMatrix L.nMinus := by
  rw [badProjector_eq_one_sub, sub_mul, goodProjector_mul_gammaMatrix_nMinus_eq_zero, one_mul,
    sub_zero]

/-- `P₊ γ⁻ = γ⁻`: the image of `γ⁻` consists of good spinors. -/
@[simp]
theorem goodProjector_mul_gammaMatrix_nPlus :
    L.goodProjector * gammaMatrix L.nPlus = gammaMatrix L.nPlus := by
  simpa only [goodProjector_swap, badProjector_swap, nPlus_swap, nMinus_swap] using
    L.swap.badProjector_mul_gammaMatrix_nMinus

/-- `P₋ γ⁺ ψ = γ⁺ ψ`. -/
@[simp]
theorem badProjector_gammaMatrix_nMinus_apply (ψ : Dirac) :
    L.badProjector (gammaMatrix L.nMinus ψ) = gammaMatrix L.nMinus ψ := by
  simpa only [Module.End.mul_apply] using
    LinearMap.congr_fun L.badProjector_mul_gammaMatrix_nMinus ψ

/-- `P₊ γ⁻ ψ = γ⁻ ψ`. -/
@[simp]
theorem goodProjector_gammaMatrix_nPlus_apply (ψ : Dirac) :
    L.goodProjector (gammaMatrix L.nPlus ψ) = gammaMatrix L.nPlus ψ := by
  simpa only [Module.End.mul_apply] using
    LinearMap.congr_fun L.goodProjector_mul_gammaMatrix_nPlus ψ

/-! ### The good and bad subspaces -/

/-- The good spinors are the kernel of `γ⁻ = /n₊`. -/
theorem ker_gammaMatrix_nPlus_eq_range_goodProjector :
    ker (gammaMatrix L.nPlus) = range L.goodProjector := by
  ext ψ
  refine ⟨fun h => ⟨ψ, ?_⟩, ?_⟩
  · have hbad : L.badProjector ψ = 0 := by simp [badProjector_apply, mem_ker.1 h]
    simpa only [hbad, add_zero] using L.goodProjector_apply_add_badProjector_apply ψ
  · rintro ⟨χ, rfl⟩
    exact mem_ker.2 (L.gammaMatrix_nPlus_goodProjector_apply_eq_zero χ)

/-- The bad spinors are the kernel of `γ⁺ = /n₋`. -/
theorem ker_gammaMatrix_nMinus_eq_range_badProjector :
    ker (gammaMatrix L.nMinus) = range L.badProjector := by
  simpa only [goodProjector_swap, badProjector_swap, nPlus_swap, nMinus_swap] using
    L.swap.ker_gammaMatrix_nPlus_eq_range_goodProjector

/-- A spinor is good iff it is annihilated by `γ⁻ = /n₊`. -/
@[simp high]
theorem mem_range_goodProjector_iff {ψ : Dirac} :
    ψ ∈ range L.goodProjector ↔ gammaMatrix L.nPlus ψ = 0 := by
  rw [← ker_gammaMatrix_nPlus_eq_range_goodProjector, mem_ker]

/-- A spinor is bad iff it is annihilated by `γ⁺ = /n₋`. -/
@[simp high]
theorem mem_range_badProjector_iff {ψ : Dirac} :
    ψ ∈ range L.badProjector ↔ gammaMatrix L.nMinus ψ = 0 := by
  rw [← ker_gammaMatrix_nMinus_eq_range_badProjector, mem_ker]

/-- A spinor is fixed by the good projector iff it is good. -/
@[simp]
theorem goodProjector_apply_eq_self_iff {ψ : Dirac} :
    L.goodProjector ψ = ψ ↔ ψ ∈ range L.goodProjector :=
  L.isIdempotentElem_goodProjector.mem_range_iff.symm

/-- A spinor is fixed by the bad projector iff it is bad. -/
@[simp]
theorem badProjector_apply_eq_self_iff {ψ : Dirac} :
    L.badProjector ψ = ψ ↔ ψ ∈ range L.badProjector :=
  L.isIdempotentElem_badProjector.mem_range_iff.symm

/-- The kernel of the good projector is the space of bad spinors. -/
theorem ker_goodProjector_eq_range_badProjector : ker L.goodProjector = range L.badProjector := by
  rw [L.isIdempotentElem_goodProjector.ker_eq_range_one_sub, badProjector_eq_one_sub]

/-- The kernel of the bad projector is the space of good spinors. -/
theorem ker_badProjector_eq_range_goodProjector : ker L.badProjector = range L.goodProjector := by
  simpa only [goodProjector_swap, badProjector_swap, nPlus_swap, nMinus_swap] using
    L.swap.ker_goodProjector_eq_range_badProjector

/-- The Dirac spinors are the direct sum of the good and the bad spinors. -/
theorem isCompl_range_goodProjector_range_badProjector :
    IsCompl (range L.goodProjector) (range L.badProjector) := by
  rw [← ker_goodProjector_eq_range_badProjector]
  exact L.isIdempotentElem_goodProjector.isProj_range.isCompl

/-- The trace of the good projector is two. -/
@[simp]
theorem trace_goodProjector_eq_two : trace ℂ Dirac L.goodProjector = 2 := by
  have hsymm : trace ℂ Dirac L.badProjector = trace ℂ Dirac L.goodProjector := by
    rw [goodProjector_def, badProjector_def, map_smul, map_smul, trace_mul_comm]
  have h := congrArg (trace ℂ Dirac) L.goodProjector_add_badProjector
  rw [map_add, hsymm, trace_one, finrank_eq_four] at h
  push_cast at h
  linear_combination h / 2

/-- The trace of the bad projector is two. -/
@[simp]
theorem trace_badProjector_eq_two : trace ℂ Dirac L.badProjector = 2 := by
  simpa only [goodProjector_swap, badProjector_swap, nPlus_swap, nMinus_swap] using
    L.swap.trace_goodProjector_eq_two

/-- The good spinors form a two-dimensional space. -/
@[simp]
theorem finrank_range_goodProjector_eq_two : finrank ℂ (range L.goodProjector) = 2 := by
  have h := L.isIdempotentElem_goodProjector.isProj_range.trace
  rw [trace_goodProjector_eq_two] at h
  exact_mod_cast h.symm

/-- The bad spinors form a two-dimensional space. -/
@[simp]
theorem finrank_range_badProjector_eq_two : finrank ℂ (range L.badProjector) = 2 := by
  rw [← goodProjector_swap]
  exact L.swap.finrank_range_goodProjector_eq_two

/-! ### Compatibility with chirality and with transverse Clifford multiplication -/

/-- An endomorphism anticommuting with `γ⁻` and with `γ⁺` commutes with the good projector
`P₊ = ½ γ⁻ γ⁺`. -/
theorem commute_goodProjector_of_anticomm {a : Module.End ℂ Dirac}
    (hPlus : a * gammaMatrix L.nPlus = -(gammaMatrix L.nPlus * a))
    (hMinus : a * gammaMatrix L.nMinus = -(gammaMatrix L.nMinus * a)) :
    Commute L.goodProjector a := by
  have h : SemiconjBy a (gammaMatrix L.nPlus * gammaMatrix L.nMinus)
      (-gammaMatrix L.nPlus * -gammaMatrix L.nMinus) :=
    SemiconjBy.mul_right (hPlus.trans (neg_mul _ _).symm) (hMinus.trans (neg_mul _ _).symm)
  rw [neg_mul_neg] at h
  exact (Commute.symm h).smul_left _

/-- An endomorphism anticommuting with `γ⁻` and with `γ⁺` commutes with the bad projector
`P₋ = ½ γ⁺ γ⁻`. -/
theorem commute_badProjector_of_anticomm {a : Module.End ℂ Dirac}
    (hPlus : a * gammaMatrix L.nPlus = -(gammaMatrix L.nPlus * a))
    (hMinus : a * gammaMatrix L.nMinus = -(gammaMatrix L.nMinus * a)) :
    Commute L.badProjector a := by
  rw [← goodProjector_swap]
  exact L.swap.commute_goodProjector_of_anticomm (by rw [nPlus_swap]; exact hMinus)
    (by rw [nMinus_swap]; exact hPlus)

/-- The good projector commutes with the chirality `γ⁵`. -/
theorem commute_goodProjector_gamma5 : Commute L.goodProjector gamma5 :=
  L.commute_goodProjector_of_anticomm (gamma5_mul_gammaMatrix _) (gamma5_mul_gammaMatrix _)

/-- The bad projector commutes with the chirality `γ⁵`. -/
theorem commute_badProjector_gamma5 : Commute L.badProjector gamma5 :=
  L.commute_badProjector_of_anticomm (gamma5_mul_gammaMatrix _) (gamma5_mul_gammaMatrix _)

/-- The good projector commutes with Clifford multiplication by a transverse vector. -/
theorem commute_goodProjector_gammaMatrix_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) : Commute L.goodProjector (gammaMatrix t) := by
  obtain ⟨hplus, hminus⟩ := L.mem_transverse_iff.1 ht
  refine L.commute_goodProjector_of_anticomm ?_ ?_
  · rw [L.gammaMatrix_nPlus_mul_gammaMatrix_eq_neg_mul_of_minus_eq_zero hminus, neg_neg]
  · rw [L.gammaMatrix_nMinus_mul_gammaMatrix_eq_neg_mul_of_plus_eq_zero hplus, neg_neg]

/-- The bad projector commutes with Clifford multiplication by a transverse vector. -/
theorem commute_badProjector_gammaMatrix_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) : Commute L.badProjector (gammaMatrix t) := by
  rw [← goodProjector_swap]
  exact L.swap.commute_goodProjector_gammaMatrix_of_mem_transverse (by rwa [transverse_swap])

/-- The good projector commutes with the left chiral projector `(1 - γ⁵) / 2`. -/
theorem commute_goodProjector_leftChiralProjector :
    Commute L.goodProjector leftChiralProjector := by
  rw [leftChiralProjector]
  exact ((Commute.one_right _).sub_right L.commute_goodProjector_gamma5).smul_right _

/-- The good projector commutes with the right chiral projector `(1 + γ⁵) / 2`. -/
theorem commute_goodProjector_rightChiralProjector :
    Commute L.goodProjector rightChiralProjector := by
  rw [rightChiralProjector]
  exact ((Commute.one_right _).add_right L.commute_goodProjector_gamma5).smul_right _

/-- The bad projector commutes with the left chiral projector `(1 - γ⁵) / 2`. -/
theorem commute_badProjector_leftChiralProjector :
    Commute L.badProjector leftChiralProjector := by
  rw [← goodProjector_swap]
  exact L.swap.commute_goodProjector_leftChiralProjector

/-- The bad projector commutes with the right chiral projector `(1 + γ⁵) / 2`. -/
theorem commute_badProjector_rightChiralProjector :
    Commute L.badProjector rightChiralProjector := by
  rw [← goodProjector_swap]
  exact L.swap.commute_goodProjector_rightChiralProjector

/-- `P₊ γ⁵ ψ = γ⁵ P₊ ψ`. -/
theorem goodProjector_gamma5_apply (ψ : Dirac) :
    L.goodProjector (gamma5 ψ) = gamma5 (L.goodProjector ψ) := by
  simpa only [Module.End.mul_apply] using LinearMap.congr_fun L.commute_goodProjector_gamma5.eq ψ

/-- `P₋ γ⁵ ψ = γ⁵ P₋ ψ`. -/
theorem badProjector_gamma5_apply (ψ : Dirac) :
    L.badProjector (gamma5 ψ) = gamma5 (L.badProjector ψ) := by
  simpa only [Module.End.mul_apply] using LinearMap.congr_fun L.commute_badProjector_gamma5.eq ψ

/-- `P₊ /t ψ = /t P₊ ψ` for a transverse vector `t`. -/
theorem goodProjector_gammaMatrix_apply_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) (ψ : Dirac) :
    L.goodProjector (gammaMatrix t ψ) = gammaMatrix t (L.goodProjector ψ) := by
  simpa only [Module.End.mul_apply] using
    LinearMap.congr_fun (L.commute_goodProjector_gammaMatrix_of_mem_transverse ht).eq ψ

/-- `P₋ /t ψ = /t P₋ ψ` for a transverse vector `t`. -/
theorem badProjector_gammaMatrix_apply_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) (ψ : Dirac) :
    L.badProjector (gammaMatrix t ψ) = gammaMatrix t (L.badProjector ψ) := by
  simpa only [Module.End.mul_apply] using
    LinearMap.congr_fun (L.commute_badProjector_gammaMatrix_of_mem_transverse ht).eq ψ

/-- Chirality preserves the good spinors. -/
theorem gamma5_apply_mem_range_goodProjector {χ : Dirac} (hχ : χ ∈ range L.goodProjector) :
    gamma5 χ ∈ range L.goodProjector :=
  L.goodProjector_apply_eq_self_iff.1 <| by
    rw [goodProjector_gamma5_apply, L.goodProjector_apply_eq_self_iff.2 hχ]

/-- Chirality preserves the bad spinors. -/
theorem gamma5_apply_mem_range_badProjector {χ : Dirac} (hχ : χ ∈ range L.badProjector) :
    gamma5 χ ∈ range L.badProjector :=
  L.badProjector_apply_eq_self_iff.1 <| by
    rw [badProjector_gamma5_apply, L.badProjector_apply_eq_self_iff.2 hχ]

/-- Clifford multiplication by a transverse vector preserves the good spinors. -/
theorem gammaMatrix_apply_mem_range_goodProjector_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) {χ : Dirac} (hχ : χ ∈ range L.goodProjector) :
    gammaMatrix t χ ∈ range L.goodProjector :=
  L.goodProjector_apply_eq_self_iff.1 <| by
    rw [L.goodProjector_gammaMatrix_apply_of_mem_transverse ht,
      L.goodProjector_apply_eq_self_iff.2 hχ]

/-- Clifford multiplication by a transverse vector preserves the bad spinors. -/
theorem gammaMatrix_apply_mem_range_badProjector_of_mem_transverse {t : Lorentz.Vector}
    (ht : t ∈ L.transverse) {χ : Dirac} (hχ : χ ∈ range L.badProjector) :
    gammaMatrix t χ ∈ range L.badProjector :=
  L.badProjector_apply_eq_self_iff.1 <| by
    rw [L.badProjector_gammaMatrix_apply_of_mem_transverse ht,
      L.badProjector_apply_eq_self_iff.2 hχ]

/-- The left chiral projector preserves the good spinors. -/
theorem leftChiralProjector_apply_mem_range_goodProjector {χ : Dirac}
    (hχ : χ ∈ range L.goodProjector) : leftChiralProjector χ ∈ range L.goodProjector :=
  L.goodProjector_apply_eq_self_iff.1 <| by
    rw [← Module.End.mul_apply, L.commute_goodProjector_leftChiralProjector.eq,
      Module.End.mul_apply, L.goodProjector_apply_eq_self_iff.2 hχ]

/-- The right chiral projector preserves the good spinors. -/
theorem rightChiralProjector_apply_mem_range_goodProjector {χ : Dirac}
    (hχ : χ ∈ range L.goodProjector) : rightChiralProjector χ ∈ range L.goodProjector :=
  L.goodProjector_apply_eq_self_iff.1 <| by
    rw [← Module.End.mul_apply, L.commute_goodProjector_rightChiralProjector.eq,
      Module.End.mul_apply, L.goodProjector_apply_eq_self_iff.2 hχ]

/-- The left chiral projector preserves the bad spinors. -/
theorem leftChiralProjector_apply_mem_range_badProjector {χ : Dirac}
    (hχ : χ ∈ range L.badProjector) : leftChiralProjector χ ∈ range L.badProjector :=
  L.badProjector_apply_eq_self_iff.1 <| by
    rw [← Module.End.mul_apply, L.commute_badProjector_leftChiralProjector.eq,
      Module.End.mul_apply, L.badProjector_apply_eq_self_iff.2 hχ]

/-- The right chiral projector preserves the bad spinors. -/
theorem rightChiralProjector_apply_mem_range_badProjector {χ : Dirac}
    (hχ : χ ∈ range L.badProjector) : rightChiralProjector χ ∈ range L.badProjector :=
  L.badProjector_apply_eq_self_iff.1 <| by
    rw [← Module.End.mul_apply, L.commute_badProjector_rightChiralProjector.eq,
      Module.End.mul_apply, L.badProjector_apply_eq_self_iff.2 hχ]

/-! ### The Dirac equation in light-cone components -/

section DiracEquation

variable (p : Lorentz.Vector) (m : ℝ)

/-- The Dirac operator of a momentum mode projected with `γ⁺`,
`γ⁺ (/p - m) = 2 p⁺ P₋ - (/p_T + m) γ⁺ P₊`. -/
theorem gammaMatrix_nMinus_mul_gammaMatrix_sub_smul_one :
    gammaMatrix L.nMinus * (gammaMatrix p - m • 1) =
      (2 * L.plus p) • L.badProjector -
        (gammaMatrix (L.transverseProj p) + m • 1) * (gammaMatrix L.nMinus * L.goodProjector) := by
  -- the content: `γ⁺ /p = 2 p⁺ P₋ - /p_T γ⁺`
  have hp : gammaMatrix L.nMinus * gammaMatrix p =
      (2 * L.plus p) • L.badProjector -
        gammaMatrix (L.transverseProj p) * gammaMatrix L.nMinus := by
    rw [L.gammaMatrix_eq_plus_smul_add_minus_smul_add p]
    simp only [mul_add, mul_smul_comm, gammaMatrix_nMinus_mul_self_eq_zero,
      gammaMatrix_nMinus_mul_gammaMatrix_nPlus_eq_two_smul_badProjector,
      L.gammaMatrix_nMinus_mul_gammaMatrix_eq_neg_mul_of_plus_eq_zero
        (L.plus_transverseProj_eq_zero p)]
    module
  simp only [mul_sub, hp, gammaMatrix_nMinus_mul_goodProjector, mul_smul_comm, add_mul,
    smul_mul_assoc, mul_one, one_mul]
  abel

/-- The Dirac operator of a momentum mode projected with `γ⁻`,
`γ⁻ (/p - m) = 2 p⁻ P₊ - (/p_T + m) γ⁻ P₋`. -/
theorem gammaMatrix_nPlus_mul_gammaMatrix_sub_smul_one :
    gammaMatrix L.nPlus * (gammaMatrix p - m • 1) =
      (2 * L.minus p) • L.goodProjector -
        (gammaMatrix (L.transverseProj p) + m • 1) * (gammaMatrix L.nPlus * L.badProjector) := by
  simpa only [nMinus_swap, plus_swap, badProjector_swap, goodProjector_swap,
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
  rwa [ker_gammaMatrix_nPlus_eq_range_goodProjector, ker_gammaMatrix_nMinus_eq_range_badProjector,
    L.isCompl_range_goodProjector_range_badProjector.inf_eq_bot, Submodule.mem_bot] at hmem

variable {p m}

/-- The constraint equation solved for the bad component: for `p⁺ ≠ 0` a solution of the Dirac
equation has `ψ₋ = (2 p⁺)⁻¹ (/p_T + m) γ⁺ ψ₊`. -/
theorem badProjector_apply_eq_of_gammaMatrix_sub_smul_one_apply_eq_zero (hp : L.plus p ≠ 0)
    {ψ : Dirac} (h : (gammaMatrix p - m • 1) ψ = 0) :
    L.badProjector ψ = (2 * L.plus p)⁻¹ •
      (gammaMatrix (L.transverseProj p) + m • 1) (gammaMatrix L.nMinus (L.goodProjector ψ)) := by
  rw [eq_inv_smul_iff₀ (mul_ne_zero two_ne_zero hp)]
  exact ((L.gammaMatrix_sub_smul_one_apply_eq_zero_iff p m ψ).1 h).1

/-- For `p⁺ ≠ 0` a solution of the Dirac equation is determined by its good component. -/
theorem injOn_goodProjector (hp : L.plus p ≠ 0) :
    Set.InjOn L.goodProjector (ker (gammaMatrix p - m • 1)) := by
  intro ψ₁ h₁ ψ₂ h₂ h
  have e := L.badProjector_apply_eq_of_gammaMatrix_sub_smul_one_apply_eq_zero hp (mem_ker.1 h₁)
  rw [h, ← L.badProjector_apply_eq_of_gammaMatrix_sub_smul_one_apply_eq_zero hp
    (mem_ker.1 h₂)] at e
  rw [← L.goodProjector_apply_add_badProjector_apply ψ₁, h, e,
    goodProjector_apply_add_badProjector_apply]

/-- `(/t + m) γ⁻ (/t + m) γ⁺ = 2 (m² - t²) P₊` for a vector `t` with `t⁻ = 0`. -/
private theorem mul_gammaMatrix_nPlus_mul_mul_gammaMatrix_nMinus_eq_smul_goodProjector
    {t : Lorentz.Vector} (ht : L.minus t = 0) (m : ℝ) :
    (gammaMatrix t + m • 1) * gammaMatrix L.nPlus *
        ((gammaMatrix t + m • 1) * gammaMatrix L.nMinus) =
      (2 * (m ^ 2 - ⟪t, t⟫ₘ)) • L.goodProjector := by
  have haT : gammaMatrix L.nPlus * (gammaMatrix t + m • 1) =
      (m • 1 - gammaMatrix t) * gammaMatrix L.nPlus := by
    simp only [mul_add, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul,
      L.gammaMatrix_nPlus_mul_gammaMatrix_eq_neg_mul_of_minus_eq_zero ht]
    abel
  have hTT : (gammaMatrix t + m • 1) * (m • 1 - gammaMatrix t) = (m ^ 2 - ⟪t, t⟫ₘ) • 1 := by
    rw [← neg_sub (gammaMatrix t), mul_neg, gammaMatrix_add_smul_one_mul_gammaMatrix_sub_smul_one,
      ← neg_smul, neg_sub]
  calc (gammaMatrix t + m • 1) * gammaMatrix L.nPlus *
        ((gammaMatrix t + m • 1) * gammaMatrix L.nMinus)
      = (gammaMatrix t + m • 1) * (gammaMatrix L.nPlus * (gammaMatrix t + m • 1)) *
          gammaMatrix L.nMinus := by simp only [mul_assoc]
    _ = (gammaMatrix t + m • 1) * (m • 1 - gammaMatrix t) *
          (gammaMatrix L.nPlus * gammaMatrix L.nMinus) := by rw [haT]; simp only [mul_assoc]
    _ = (2 * (m ^ 2 - ⟪t, t⟫ₘ)) • L.goodProjector := by
      rw [hTT, gammaMatrix_nPlus_mul_gammaMatrix_nMinus_eq_two_smul_goodProjector, smul_mul_assoc,
        one_mul]
      module

/-- For a good spinor `χ`, the spinor `χ + (2 p⁺)⁻¹ (/p_T + m) γ⁺ χ` has good component `χ`:
the added term is bad. -/
theorem goodProjector_apply_add_inv_smul_eq {χ : Dirac} (hχ : χ ∈ range L.goodProjector) :
    L.goodProjector (χ + (2 * L.plus p)⁻¹ •
      (gammaMatrix (L.transverseProj p) + m • 1) (gammaMatrix L.nMinus χ)) = χ := by
  have hc : Commute L.goodProjector (gammaMatrix (L.transverseProj p) + m • 1) :=
    (L.commute_goodProjector_gammaMatrix_of_mem_transverse
      (L.isProj_transverseProj.map_mem p)).add_right ((Commute.one_right _).smul_right m)
  have h0 := LinearMap.congr_fun hc.eq (gammaMatrix L.nMinus χ)
  simp only [Module.End.mul_apply, goodProjector_gammaMatrix_nMinus_apply_eq_zero,
    map_zero] at h0
  rw [map_add, LinearMap.map_smul_of_tower, h0, smul_zero, add_zero,
    L.goodProjector_apply_eq_self_iff.2 hχ]

/-- On the mass shell `p² = m²` with `p⁺ ≠ 0`, a good spinor `χ` is the good component of the
solution `ψ = χ + (2 p⁺)⁻¹ (/p_T + m) γ⁺ χ` of the Dirac equation `(/p - m) ψ = 0`: the bad
component prescribed by the constraint equation also satisfies the dynamical equation. -/
theorem gammaMatrix_sub_smul_one_apply_add_inv_smul_eq_zero (hshell : ⟪p, p⟫ₘ = m ^ 2)
    (hp : L.plus p ≠ 0) {χ : Dirac} (hχ : χ ∈ range L.goodProjector) :
    (gammaMatrix p - m • 1) (χ + (2 * L.plus p)⁻¹ •
      (gammaMatrix (L.transverseProj p) + m • 1) (gammaMatrix L.nMinus χ)) = 0 := by
  have hχ' : L.goodProjector χ = χ := L.goodProjector_apply_eq_self_iff.2 hχ
  let T := gammaMatrix (L.transverseProj p) + m • 1
  -- the bad component prescribed by the constraint equation
  let η := (2 * L.plus p)⁻¹ • T (gammaMatrix L.nMinus χ)
  have hg : L.goodProjector (χ + η) = χ := L.goodProjector_apply_add_inv_smul_eq hχ
  have hb : L.badProjector (χ + η) = η := by
    rw [badProjector_eq_one_sub, LinearMap.sub_apply, Module.End.one_apply, hg,
      add_sub_cancel_left]
  rw [L.gammaMatrix_sub_smul_one_apply_eq_zero_iff, hg, hb]
  refine ⟨by rw [smul_inv_smul₀ (mul_ne_zero two_ne_zero hp)], ?_⟩
  -- the dynamical equation holds because `m² - p_T² = 2 p⁺ p⁻` on the mass shell
  have hshell' : m ^ 2 - ⟪L.transverseProj p, L.transverseProj p⟫ₘ =
      2 * (L.plus p * L.minus p) := by
    rw [← hshell, L.minkowskiProduct_eq_plus_mul_minus_add p p]
    ring
  have key := LinearMap.congr_fun
    (L.mul_gammaMatrix_nPlus_mul_mul_gammaMatrix_nMinus_eq_smul_goodProjector
      (L.minus_transverseProj_eq_zero p) m) χ
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hχ', hshell'] at key
  simp only [η, T, LinearMap.map_smul_of_tower]
  rw [key, smul_smul]
  congr 1
  field_simp

/-- On the mass shell `p² = m²` with `p⁺ ≠ 0`, the good projector `P₊` restricts to a linear
equivalence from the solutions of the Dirac equation `(/p - m) ψ = 0` onto the good spinors:
a solution is parametrised by its good component. -/
def goodProjectorEquiv (hshell : ⟪p, p⟫ₘ = m ^ 2) (hp : L.plus p ≠ 0) :
    ker (gammaMatrix p - m • 1) ≃ₗ[ℂ] range L.goodProjector :=
  LinearEquiv.ofBijective (L.goodProjector.restrict fun ψ _ => mem_range_self _ ψ) <| by
    refine ⟨fun ψ₁ ψ₂ h => Subtype.ext (L.injOn_goodProjector hp ψ₁.2 ψ₂.2 ?_), ?_⟩
    · simpa only [coe_restrict_apply] using congr_arg Subtype.val h
    · rintro ⟨χ, hχ⟩
      refine ⟨⟨_, mem_ker.2 (L.gammaMatrix_sub_smul_one_apply_add_inv_smul_eq_zero hshell hp hχ)⟩,
        Subtype.ext ?_⟩
      rw [coe_restrict_apply]
      exact L.goodProjector_apply_add_inv_smul_eq hχ

/-- The equivalence `goodProjectorEquiv` sends a solution `ψ` to its good component `P₊ ψ`. -/
@[simp]
theorem coe_goodProjectorEquiv_apply (hshell : ⟪p, p⟫ₘ = m ^ 2) (hp : L.plus p ≠ 0)
    (ψ : ker (gammaMatrix p - m • 1)) :
    (L.goodProjectorEquiv hshell hp ψ : Dirac) = L.goodProjector ψ := by
  rw [goodProjectorEquiv]
  exact (congrArg Subtype.val (LinearEquiv.ofBijective_apply _ ψ)).trans (coe_restrict_apply _ _)

/-- The inverse of `goodProjectorEquiv` reconstructs the solution of the Dirac equation from its
good component `χ` through the constraint equation, `ψ = χ + (2 p⁺)⁻¹ (/p_T + m) γ⁺ χ`. -/
@[simp]
theorem coe_goodProjectorEquiv_symm_apply (hshell : ⟪p, p⟫ₘ = m ^ 2) (hp : L.plus p ≠ 0)
    (χ : range L.goodProjector) :
    ((L.goodProjectorEquiv hshell hp).symm χ : Dirac) = χ + (2 * L.plus p)⁻¹ •
      (gammaMatrix (L.transverseProj p) + m • 1) (gammaMatrix L.nMinus χ) := by
  let ψ : ker (gammaMatrix p - m • 1) :=
    ⟨_, mem_ker.2 (L.gammaMatrix_sub_smul_one_apply_add_inv_smul_eq_zero hshell hp χ.2)⟩
  have h : χ = L.goodProjectorEquiv hshell hp ψ := by
    refine Subtype.ext ?_
    rw [coe_goodProjectorEquiv_apply]
    exact (L.goodProjector_apply_add_inv_smul_eq χ.2).symm
  exact congrArg Subtype.val ((LinearEquiv.symm_apply_eq _).2 h)

/-- On the mass shell `p² = m²` with `p⁺ ≠ 0`, the solutions of the Dirac equation
`(/p - m) ψ = 0` form a two-dimensional space. -/
private theorem finrank_ker_gammaMatrix_sub_smul_one_eq_two (hshell : ⟪p, p⟫ₘ = m ^ 2)
    (hp : L.plus p ≠ 0) :
    finrank ℂ (ker (gammaMatrix p - m • 1)) = 2 := by
  rw [(L.goodProjectorEquiv hshell hp).finrank_eq, finrank_range_goodProjector_eq_two]

end DiracEquation

end LightConeBasis

end LinearMap.BilinForm

namespace Fermion.Dirac

open LinearMap.BilinForm Module LinearMap
open Lorentz.Vector (minkowskiProduct)
open scoped Lorentz.Vector

/-- On the mass shell `p² = m²` with `p ≠ 0`, the solutions of the Dirac equation
`(/p - m) ψ = 0` form a two-dimensional space. -/
theorem finrank_ker_gammaMatrix_sub_smul_one_eq_two {p : Lorentz.Vector} {m : ℝ}
    (hshell : ⟪p, p⟫ₘ = m ^ 2) (hp : p ≠ 0) :
    finrank ℂ (ker (gammaMatrix p - m • 1)) = 2 := by
  -- some standard light-cone basis has `p` outside its transverse space
  obtain ⟨i, hi⟩ : ∃ i : Fin 3, p ∉ (LightConeBasis.minkowskiAxis i).transverse := by
    by_contra! h
    refine hp (Lorentz.Vector.ext_of_apply fun μ => ?_)
    rcases μ with μ | i
    · rw [Fin.fin_one_eq_zero μ]
      exact ((LightConeBasis.mem_transverse_minkowskiAxis_iff 0 p).1 (h 0)).1
    · exact ((LightConeBasis.mem_transverse_minkowskiAxis_iff i p).1 (h i)).2
  -- so `p⁺ ≠ 0` in that basis or in its swap
  rw [LightConeBasis.mem_transverse_iff, not_and_or] at hi
  rcases hi with hplus | hminus
  · exact (LightConeBasis.minkowskiAxis i).finrank_ker_gammaMatrix_sub_smul_one_eq_two hshell hplus
  · exact (LightConeBasis.minkowskiAxis i).swap.finrank_ker_gammaMatrix_sub_smul_one_eq_two hshell
      (by rwa [LightConeBasis.plus_swap])

end Fermion.Dirac
