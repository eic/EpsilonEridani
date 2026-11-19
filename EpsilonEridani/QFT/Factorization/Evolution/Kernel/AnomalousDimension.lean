/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.HarmonicSum.Continuation
public import EpsilonEridani.Particles.Parton.SingletDecomposition
public import EpsilonEridani.QFT.Factorization.Evolution.Kernel.LeadingOrder

/-!
# The leading-order anomalous dimensions as meromorphic functions of `N`

The Mellin moments `γ_ab(N) = M[P_ab](N)` of the four leading-order splitting kernels are computed
in closed form in `EpsilonEridani.QFT.Factorization.Evolution.Kernel.LeadingOrder`: at real `N` for
`P_gq` and `P_qg`, and at natural indices for `P_qq` and `P_gg`. With the first harmonic sum
continued to complex argument as `S₁(s) = ψ(s + 1) + γ` (`EpsilonEridani.complexHarmonic`), the
closed forms

* `γ_qq(N) = C_F [3/2 - 2 S₁(N) + 1/(N (N+1))]`,
* `γ_gq(N) = C_F (N² + N + 2) / ((N-1) N (N+1))`,
* `γ_qg(N) = T_F (N² + N + 2) / (N (N+1) (N+2))` per flavour,
* `γ_gg(N) = 2 C_A [-S₁(N) + 1/(N-1) - 1/N + 1/(N+1) - 1/(N+2)] + (11/6) C_A - (2/3) n_f T_F`

are meromorphic functions on the whole complex `N`-plane. They are normalised to `α_s / (2π)`, as
the kernels are, and the inverse Mellin transform that reconstructs the densities integrates them
along a contour in the complex plane, to the right of their rightmost singularity.

The singlet anomalous-dimension matrix `γ^S(N)` acts on the pair `(Σ, g)` of the quark singlet
`Σ = ∑ᵢ (q_i + qbar_i)` and the gluon, with the row index the daughter and the column index the
parent:

  `γ^S(N) = !![γ_qq(N), 2 n_f γ_qg(N); γ_gq(N), γ_gg(N)]`.

It is defined as the matrix `Species.singletGluonMatrix` of
`EpsilonEridani.Particles.Parton.SingletDecomposition`, through which a flavour-blind kernel acts
on the singlet sector, evaluated at the four leading-order entries and the flavour number `n_f`.

The pole structure at `N = 1` is the moment-space form of the small-`x` behaviour: `γ_gq` and
`γ_gg` have simple poles there, with residues `2 C_F` and `2 C_A`, the colour charges of the
emitting parton, and `γ_qq` and `γ_qg` are analytic there. The pole of `γ_gq` is also visible on
the moments themselves: `(N - 1) M[P_gq](N) → 2 C_F` as the real index `N` decreases to `1`.

## Main definitions

* `gammaQQ`, `gammaGQ`, `gammaQG`, `gammaGG`: the four leading-order anomalous dimensions as
  functions of complex `N`, with `gammaQG` per flavour as `pqg` is.
* `gammaS`: the singlet anomalous-dimension matrix in the basis `(Σ, g)`.

## Main statements

* `gammaQQ_natCast_eq_moment`, `gammaGG_natCast_eq_moment`: the continuations agree with the
  kernel moments at the natural indices `N ≥ 1` and `N ≥ 2`.
* `gammaGQ_ofReal_eq_moment`, `gammaQG_ofReal_eq_moment`: the continuations agree with the
  kernel moments on the real half-lines `N > 1` and `N > 0`.
* `gammaS_natCast_eq_moment`: `γ^S(N)` is the matrix of the kernel moments at natural `N ≥ 2`.
* `meromorphic_gammaQQ`, `meromorphic_gammaGQ`, `meromorphic_gammaQG`, `meromorphic_gammaGG`:
  the entries of `γ^S` are meromorphic on `ℂ`.
* `analyticAt_gammaQQ`, `analyticAt_gammaQG`, `analyticAt_gammaGQ`, `analyticAt_gammaGG`: the
  regions of analyticity; in particular `γ_qq` and `γ_qg` are analytic at `N = 1`.
* `meromorphicOrderAt_gammaGQ_one`, `meromorphicOrderAt_gammaGG_one`: simple poles at `N = 1`.
* `meromorphicTrailingCoeffAt_gammaGQ_one`, `meromorphicTrailingCoeffAt_gammaGG_one`,
  `tendsto_sub_one_mul_gammaGQ`, `tendsto_sub_one_mul_gammaGG`: their residues `2 C_F` and
  `2 C_A`, and `tendsto_sub_one_mul_moment_pgq` for the moments of `P_gq`.
* `vecMul_gammaS_two_eq_zero`: `(1, 1)` is a left null vector of `γ^S(2)`, the momentum sum
  rule.

## References

* G. Altarelli and G. Parisi, *Asymptotic freedom in parton language*, Nucl. Phys. B 126 (1977)
  298.
* R. K. Ellis, W. J. Stirling and B. R. Webber, *QCD and Collider Physics*, Cambridge University
  Press (1996), §4.3.
* J. Blümlein, *Analytic continuation of Mellin transforms up to two-loop order*,
  Comput. Phys. Commun. 133 (2000) 76, arXiv:hep-ph/0003100.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

open Complex Filter Matrix Topology QCD

variable (c : ColorFactors)

/-! ### The four anomalous dimensions -/

/-- The leading-order quark-to-quark anomalous dimension
`γ_qq(N) = C_F [3/2 - 2 S₁(N) + 1/(N (N+1))]`, continued to complex `N` through
`complexHarmonic`. -/
noncomputable def gammaQQ (N : ℂ) : ℂ :=
  c.cF * (3 / 2 - 2 * complexHarmonic N + 1 / (N * (N + 1)))

/-- The leading-order gluon-in-quark anomalous dimension
`γ_gq(N) = C_F (N² + N + 2) / ((N-1) N (N+1))`. -/
noncomputable def gammaGQ (N : ℂ) : ℂ :=
  c.cF * (N ^ 2 + N + 2) / ((N - 1) * N * (N + 1))

/-- The leading-order quark-in-gluon anomalous dimension per flavour,
`T_F (N² + N + 2) / (N (N+1) (N+2))`. The singlet-normalised entry of `gammaS` is `2 n_f` times
this. -/
noncomputable def gammaQG (N : ℂ) : ℂ :=
  c.tF * (N ^ 2 + N + 2) / (N * (N + 1) * (N + 2))

/-- The leading-order gluon-to-gluon anomalous dimension
`γ_gg(N) = 2 C_A [-S₁(N) + 1/(N-1) - 1/N + 1/(N+1) - 1/(N+2)] + (11/6) C_A - (2/3) n_f T_F`,
continued to complex `N` through `complexHarmonic`. -/
noncomputable def gammaGG (N : ℂ) : ℂ :=
  2 * c.cA * (-complexHarmonic N + 1 / (N - 1) - 1 / N + 1 / (N + 1) - 1 / (N + 2)) +
    11 / 6 * c.cA - 2 / 3 * c.nF * c.tF

theorem gammaQQ_apply (N : ℂ) :
    gammaQQ c N = c.cF * (3 / 2 - 2 * complexHarmonic N + 1 / (N * (N + 1))) :=
  (rfl)

theorem gammaGQ_apply (N : ℂ) :
    gammaGQ c N = c.cF * (N ^ 2 + N + 2) / ((N - 1) * N * (N + 1)) :=
  (rfl)

theorem gammaQG_apply (N : ℂ) :
    gammaQG c N = c.tF * (N ^ 2 + N + 2) / (N * (N + 1) * (N + 2)) :=
  (rfl)

theorem gammaGG_apply (N : ℂ) :
    gammaGG c N =
      2 * c.cA * (-complexHarmonic N + 1 / (N - 1) - 1 / N + 1 / (N + 1) - 1 / (N + 2)) +
        11 / 6 * c.cA - 2 / 3 * c.nF * c.tF :=
  (rfl)

/-! ### Agreement with the kernel moments -/

/-- `γ_qq` continues the moments of `P_qq` from the natural indices `N ≥ 1`. -/
theorem gammaQQ_natCast_eq_moment {n : ℕ} (hn : n ≠ 0) : gammaQQ c n = (pqq c).moment n := by
  rw [moment_pqq c hn, gammaQQ_apply, complexHarmonic_natCast]
  push_cast
  ring

/-- `γ_gq` continues the moments of `P_gq` from the real half-line `N > 1`. -/
theorem gammaGQ_ofReal_eq_moment {N : ℝ} (hN : 1 < N) : gammaGQ c N = (pgq c).moment N := by
  rw [moment_pgq c hN, gammaGQ_apply]
  push_cast
  ring

/-- `γ_qg` continues the moments of the per-flavour kernel `P_qg` from the real half-line
`N > 0`. -/
theorem gammaQG_ofReal_eq_moment {N : ℝ} (hN : 0 < N) : gammaQG c N = (pqg c).moment N := by
  rw [moment_pqg c hN, gammaQG_apply]
  push_cast
  ring

/-- `γ_gg` continues the moments of `P_gg` from the natural indices `N ≥ 2`. -/
theorem gammaGG_natCast_eq_moment {n : ℕ} (hn : 2 ≤ n) : gammaGG c n = (pgg c).moment n := by
  rw [moment_pgg c hn, gammaGG_apply, complexHarmonic_natCast]
  push_cast
  ring

/-- **Quark-number conservation** in moment space: `γ_qq(1) = 0`. -/
@[simp]
theorem gammaQQ_one : gammaQQ c 1 = 0 := by
  simpa using gammaQQ_natCast_eq_moment c one_ne_zero

/-! ### Meromorphy and the regions of analyticity -/

/-- `γ_qq` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_gammaQQ : Meromorphic (gammaQQ c) := by
  have h := meromorphic_complexHarmonic
  unfold gammaQQ
  fun_prop

/-- `γ_gq` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_gammaGQ : Meromorphic (gammaGQ c) := by
  unfold gammaGQ
  fun_prop

/-- `γ_qg` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_gammaQG : Meromorphic (gammaQG c) := by
  unfold gammaQG
  fun_prop

/-- `γ_gg` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_gammaGG : Meromorphic (gammaGG c) := by
  have h := meromorphic_complexHarmonic
  unfold gammaGG
  fun_prop

/-- `γ_qq` is analytic away from the non-positive integers. -/
@[fun_prop]
theorem analyticAt_gammaQQ {N : ℂ} (hN : ∀ m : ℕ, N ≠ -m) : AnalyticAt ℂ (gammaQQ c) N := by
  have h0 : N ≠ 0 := by simpa using hN 0
  have h1 : N + 1 ≠ 0 := fun h => hN 1 (by push_cast; linear_combination h)
  have hd : N * (N + 1) ≠ 0 := mul_ne_zero h0 h1
  have hS : AnalyticAt ℂ complexHarmonic N :=
    analyticAt_complexHarmonic fun m h => hN (m + 1) (by push_cast; exact h)
  unfold gammaQQ
  fun_prop (disch := assumption)

/-- `γ_qg` is analytic away from `N = 0, -1, -2`. -/
@[fun_prop]
theorem analyticAt_gammaQG {N : ℂ} (h0 : N ≠ 0) (h1 : N ≠ -1) (h2 : N ≠ -2) :
    AnalyticAt ℂ (gammaQG c) N := by
  replace h1 : N + 1 ≠ 0 := fun h => h1 (eq_neg_of_add_eq_zero_left h)
  replace h2 : N + 2 ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
  unfold gammaQG
  fun_prop (disch := exact mul_ne_zero (mul_ne_zero h0 h1) h2)

/-- `γ_gq` is analytic away from `N = 1, 0, -1`. -/
@[fun_prop]
theorem analyticAt_gammaGQ {N : ℂ} (h : N ≠ 1) (h0 : N ≠ 0) (h1 : N ≠ -1) :
    AnalyticAt ℂ (gammaGQ c) N := by
  replace h : N - 1 ≠ 0 := sub_ne_zero.2 h
  replace h1 : N + 1 ≠ 0 := fun h' => h1 (eq_neg_of_add_eq_zero_left h')
  unfold gammaGQ
  fun_prop (disch := exact mul_ne_zero (mul_ne_zero h h0) h1)

/-- `γ_gg` is analytic away from `N = 1` and the non-positive integers. -/
@[fun_prop]
theorem analyticAt_gammaGG {N : ℂ} (h : N ≠ 1) (hN : ∀ m : ℕ, N ≠ -m) :
    AnalyticAt ℂ (gammaGG c) N := by
  replace h : N - 1 ≠ 0 := sub_ne_zero.2 h
  have h0 : N ≠ 0 := by simpa using hN 0
  have h1 : N + 1 ≠ 0 := fun h => hN 1 (by push_cast; linear_combination h)
  have h2 : N + 2 ≠ 0 := fun h => hN 2 (by push_cast; linear_combination h)
  have hS : AnalyticAt ℂ complexHarmonic N :=
    analyticAt_complexHarmonic fun m h => hN (m + 1) (by push_cast; exact h)
  unfold gammaGG
  fun_prop (disch := assumption)

private theorem one_ne_neg_natCast (m : ℕ) : (1 : ℂ) ≠ -(m : ℂ) := fun h =>
  Nat.cast_add_one_ne_zero (R := ℂ) m (by linear_combination h)

/-- `γ_qq` is analytic at `N = 1`. -/
@[fun_prop]
theorem analyticAt_gammaQQ_one : AnalyticAt ℂ (gammaQQ c) 1 :=
  analyticAt_gammaQQ c one_ne_neg_natCast

/-- `γ_qg` is analytic at `N = 1`. -/
@[fun_prop]
theorem analyticAt_gammaQG_one : AnalyticAt ℂ (gammaQG c) 1 :=
  analyticAt_gammaQG c one_ne_zero (by norm_num) (by norm_num)

/-! ### The poles at `N = 1` -/

section SimplePole

variable {f g : ℂ → ℂ} {z : ℂ}

/-- Near a simple pole `f = (w - z)⁻¹ g` with `g` analytic, `(w - z) f(w) → g(z)`. -/
private theorem tendsto_sub_mul_of_eq_inv_mul (hg : AnalyticAt ℂ g z)
    (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ * g w) :
    Tendsto (fun w => (w - z) * f w) (𝓝[≠] z) (𝓝 (g z)) := by
  refine hg.continuousAt.continuousWithinAt.tendsto.congr' ?_
  filter_upwards [h, self_mem_nhdsWithin] with w hw hne
  rw [hw, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hne), one_mul]

private theorem eventuallyEq_zpow_neg_one_smul (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ * g w) :
    f =ᶠ[𝓝[≠] z] fun w => (w - z) ^ (-1 : ℤ) • g w :=
  h.mono fun w hw => by simp only [hw, _root_.zpow_neg_one, smul_eq_mul]

/-- A function `f = (w - z)⁻¹ g` with `g` analytic and `g z ≠ 0` has a simple pole at `z`. -/
private theorem meromorphicOrderAt_eq_neg_one_of_eq_inv_mul (hf : MeromorphicAt f z)
    (hg : AnalyticAt ℂ g z) (hgz : g z ≠ 0) (h : ∀ᶠ w in 𝓝[≠] z, f w = (w - z)⁻¹ * g w) :
    meromorphicOrderAt f z = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast, meromorphicOrderAt_eq_int_iff hf]
  exact ⟨g, hg, hgz, eventuallyEq_zpow_neg_one_smul h⟩

end SimplePole

/-- The analytic factor `(N - 1) γ_gq(N)` of `γ_gq` at its pole at `N = 1`. -/
private noncomputable def gammaGQRegularPart (N : ℂ) : ℂ :=
  c.cF * (N ^ 2 + N + 2) / (N * (N + 1))

private theorem gammaGQ_eq_inv_mul (N : ℂ) :
    gammaGQ c N = (N - 1)⁻¹ * gammaGQRegularPart c N := by
  simp only [gammaGQ_apply, gammaGQRegularPart, div_eq_mul_inv, mul_inv]
  ring

private theorem analyticAt_gammaGQRegularPart : AnalyticAt ℂ (gammaGQRegularPart c) 1 := by
  unfold gammaGQRegularPart
  fun_prop (disch := norm_num)

private theorem gammaGQRegularPart_one : gammaGQRegularPart c 1 = 2 * c.cF := by
  rw [gammaGQRegularPart]
  ring

/-- **The residue of `γ_gq` at `N = 1`** is `2 C_F`. -/
theorem tendsto_sub_one_mul_gammaGQ :
    Tendsto (fun N => (N - 1) * gammaGQ c N) (𝓝[≠] 1) (𝓝 (2 * c.cF)) := by
  rw [← gammaGQRegularPart_one]
  exact tendsto_sub_mul_of_eq_inv_mul (analyticAt_gammaGQRegularPart c)
    (Eventually.of_forall (gammaGQ_eq_inv_mul c))

/-- **`γ_gq` has a simple pole at `N = 1`** whenever `C_F ≠ 0`. -/
theorem meromorphicOrderAt_gammaGQ_one (hc : c.cF ≠ 0) :
    meromorphicOrderAt (gammaGQ c) 1 = -1 :=
  meromorphicOrderAt_eq_neg_one_of_eq_inv_mul (meromorphic_gammaGQ c 1)
    (analyticAt_gammaGQRegularPart c) (by simp [gammaGQRegularPart_one, hc])
    (Eventually.of_forall (gammaGQ_eq_inv_mul c))

/-- **The residue of `γ_gq` at `N = 1`** as its trailing Laurent coefficient: `2 C_F`. -/
theorem meromorphicTrailingCoeffAt_gammaGQ_one (hc : c.cF ≠ 0) :
    meromorphicTrailingCoeffAt (gammaGQ c) 1 = 2 * c.cF := by
  rw [← gammaGQRegularPart_one]
  exact (analyticAt_gammaGQRegularPart c).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (by simp [gammaGQRegularPart_one, hc])
    (eventuallyEq_zpow_neg_one_smul (Eventually.of_forall (gammaGQ_eq_inv_mul c)))

/-- The moments of `P_gq` themselves have the pole: `(N - 1) M[P_gq](N) → 2 C_F` as the real
index `N` decreases to `1`, where the integral defining them stops converging. -/
theorem tendsto_sub_one_mul_moment_pgq :
    Tendsto (fun N : ℝ => (N - 1) * (pgq c).moment N) (𝓝[>] 1) (𝓝 (2 * c.cF)) := by
  have hg : ContinuousAt (fun N : ℝ => c.cF * (N ^ 2 + N + 2) / (N * (N + 1))) 1 := by
    fun_prop (disch := norm_num)
  have ht := (hg.continuousWithinAt (s := Set.Ioi 1)).tendsto
  rw [show c.cF * (1 ^ 2 + 1 + 2) / (1 * (1 + 1)) = 2 * c.cF by ring] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with N (hN : 1 < N)
  have h1 : N - 1 ≠ 0 := sub_ne_zero.2 hN.ne'
  rw [moment_pgq c hN]
  field_simp

/-- The analytic factor `(N - 1) γ_gg(N)` of `γ_gg` at its pole at `N = 1`. -/
private noncomputable def gammaGGRegularPart (N : ℂ) : ℂ :=
  (N - 1) * (2 * c.cA * (-complexHarmonic N - 1 / N + 1 / (N + 1) - 1 / (N + 2)) +
    11 / 6 * c.cA - 2 / 3 * c.nF * c.tF) + 2 * c.cA

private theorem gammaGG_eq_inv_mul : ∀ᶠ N in 𝓝[≠] (1 : ℂ),
    gammaGG c N = (N - 1)⁻¹ * gammaGGRegularPart c N := by
  filter_upwards [self_mem_nhdsWithin] with N hN
  have h : N - 1 ≠ 0 := sub_ne_zero.2 hN
  rw [gammaGG_apply, gammaGGRegularPart]
  field_simp
  ring

private theorem analyticAt_gammaGGRegularPart : AnalyticAt ℂ (gammaGGRegularPart c) 1 := by
  have hS : AnalyticAt ℂ complexHarmonic 1 :=
    analyticAt_complexHarmonic fun m => by exact_mod_cast one_ne_neg_natCast (m + 1)
  unfold gammaGGRegularPart
  fun_prop (disch := norm_num)

private theorem gammaGGRegularPart_one : gammaGGRegularPart c 1 = 2 * c.cA := by
  simp [gammaGGRegularPart]

/-- **The residue of `γ_gg` at `N = 1`** is `2 C_A`. -/
theorem tendsto_sub_one_mul_gammaGG :
    Tendsto (fun N => (N - 1) * gammaGG c N) (𝓝[≠] 1) (𝓝 (2 * c.cA)) := by
  rw [← gammaGGRegularPart_one]
  exact tendsto_sub_mul_of_eq_inv_mul (analyticAt_gammaGGRegularPart c) (gammaGG_eq_inv_mul c)

/-- **`γ_gg` has a simple pole at `N = 1`** whenever `C_A ≠ 0`. -/
theorem meromorphicOrderAt_gammaGG_one (hc : c.cA ≠ 0) :
    meromorphicOrderAt (gammaGG c) 1 = -1 :=
  meromorphicOrderAt_eq_neg_one_of_eq_inv_mul (meromorphic_gammaGG c 1)
    (analyticAt_gammaGGRegularPart c) (by simp [gammaGGRegularPart_one, hc])
    (gammaGG_eq_inv_mul c)

/-- **The residue of `γ_gg` at `N = 1`** as its trailing Laurent coefficient: `2 C_A`. -/
theorem meromorphicTrailingCoeffAt_gammaGG_one (hc : c.cA ≠ 0) :
    meromorphicTrailingCoeffAt (gammaGG c) 1 = 2 * c.cA := by
  rw [← gammaGGRegularPart_one]
  exact (analyticAt_gammaGGRegularPart c).meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE
    (by simp [gammaGGRegularPart_one, hc]) (eventuallyEq_zpow_neg_one_smul (gammaGG_eq_inv_mul c))

/-! ### The singlet matrix -/

/-- The leading-order singlet anomalous-dimension matrix in the basis `(Σ, g)` of the quark
singlet and the gluon, with the row index the daughter and the column index the parent:
`γ^S(N) = !![γ_qq(N), 2 n_f γ_qg(N); γ_gq(N), γ_gg(N)]`, the matrix
`Species.singletGluonMatrix` by which the flavour-blind matrix of the four anomalous dimensions
acts on `(Σ, g)` (`Species.singletGluon_flavorBlindMatrix_mulVec`). -/
noncomputable def gammaS (N : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Particles.Parton.Species.singletGluonMatrix (gammaQQ c N) (gammaQG c N) (gammaGQ c N)
    (gammaGG c N) c.nF

theorem gammaS_apply (N : ℂ) :
    gammaS c N =
      Particles.Parton.Species.singletGluonMatrix (gammaQQ c N) (gammaQG c N) (gammaGQ c N)
        (gammaGG c N) c.nF :=
  (rfl)

/-- At natural `N ≥ 2`, where all four kernel moments converge, `γ^S(N)` is the matrix of the
moments of the four kernels, with the singlet-normalised `2 n_f P_qg` in the quark-from-gluon
entry. -/
theorem gammaS_natCast_eq_moment {n : ℕ} (hn : 2 ≤ n) :
    gammaS c n =
      (!![(pqq c).moment n, (pqgSinglet c).moment n; (pgq c).moment n, (pgg c).moment n]).map
        ((↑) : ℝ → ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  rw [gammaS_apply, Particles.Parton.Species.singletGluonMatrix_def,
    gammaQQ_natCast_eq_moment c (by omega), gammaGG_natCast_eq_moment c hn,
    show ((n : ℂ)) = ((n : ℝ) : ℂ) by norm_cast, gammaQG_ofReal_eq_moment c hn0,
    gammaGQ_ofReal_eq_moment c hn1, pqgSinglet_def, KernelForm.moment_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The momentum sum rule in moment space.** `(1, 1)` is a left null vector of `γ^S(2)`: both
columns of the singlet matrix sum to zero at the momentum index `N = 2`. -/
theorem vecMul_gammaS_two_eq_zero : vecMul (fun _ => 1) (gammaS c 2) = 0 := by
  have h := gammaS_natCast_eq_moment c (le_refl 2)
  push_cast at h
  rw [h]
  ext j
  fin_cases j <;> simp [vecMul, dotProduct, Fin.sum_univ_two, ← ofReal_add,
    moment_pqq_two_add_moment_pgq_two_eq_zero, add_comm ((pqgSinglet c).moment 2),
    moment_pgg_two_add_moment_pqgSinglet_two_eq_zero,
    -moment_pqq_two, -moment_pgq_two, -moment_pgg_two, -moment_pqgSinglet_two]

end Evolution
end Factorization
end QFT
end EpsilonEridani
