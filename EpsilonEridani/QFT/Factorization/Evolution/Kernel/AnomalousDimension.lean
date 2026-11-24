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
`EpsilonEridani.Particles.Parton.SingletDecomposition` evaluated at the four leading-order entries
and the real flavour number `n_f`. When `n_f` is the number of quark flavours, this is the matrix
through which the flavour-blind kernel of the four entries acts on the singlet sector.

The pole structure at `N = 1` is the moment-space form of the small-`x` behaviour: for
non-vanishing colour factors `γ_gq` and `γ_gg` have simple poles there, with residues `2 C_F` and
`2 C_A`, the colour charges of the emitting parton, and `γ_qq` and `γ_qg` are analytic there.
The pole of `γ_gq` is also visible on the moments themselves: `(N - 1) M[P_gq](N) → 2 C_F` as
the real index `N` decreases to `1`.

## Main definitions

* `gammaQQ`, `gammaGQ`, `gammaQG`, `gammaGG`: the four leading-order anomalous dimensions as
  functions of complex `N`, with `gammaQG` per flavour as `pqg` is.
* `gammaQGSinglet`: the singlet-normalised `2 n_f γ_qg`, the quark-from-gluon entry of `γ^S`.
* `gammaS`: the singlet anomalous-dimension matrix in the basis `(Σ, g)`.

## Main statements

* `gammaQQ_natCast_eq_moment`, `gammaGG_natCast_eq_moment`: the continuations agree with the
  kernel moments at the natural indices `N ≥ 1` and `N ≥ 2`.
* `gammaGQ_ofReal_eq_moment`, `gammaQG_ofReal_eq_moment`, `gammaQGSinglet_ofReal_eq_moment`: the
  continuations agree with the kernel moments on the real half-lines `N > 1` and `N > 0`.
* `gammaS_zero_zero`, `gammaS_zero_one`, `gammaS_one_zero`, `gammaS_one_one`: the entries of
  `γ^S(N)`.
* `gammaS_natCast_eq_moment`: `γ^S(N)` is the matrix of the kernel moments at natural `N ≥ 2`.
* `gammaQQ_one`: quark-number conservation, `γ_qq(1) = 0`.
* `meromorphic_gammaQQ`, `meromorphic_gammaGQ`, `meromorphic_gammaQG`, `meromorphic_gammaGG`,
  `meromorphic_gammaQGSinglet`: the four anomalous dimensions and the singlet-normalised
  `2 n_f γ_qg` are meromorphic on `ℂ`.
* `analyticAt_gammaQQ`, `analyticAt_gammaQG`, `analyticAt_gammaQGSinglet`, `analyticAt_gammaGQ`,
  `analyticAt_gammaGG`: the regions of analyticity.
* `analyticAt_gammaQQ_one`, `analyticAt_gammaQG_one`, `analyticAt_gammaQGSinglet_one`: `γ_qq`,
  `γ_qg` and `2 n_f γ_qg` are analytic at `N = 1`.
* `meromorphicOrderAt_gammaGQ_one`, `meromorphicOrderAt_gammaGG_one`: simple poles at `N = 1`
  (for `C_F ≠ 0`, resp. `C_A ≠ 0`).
* `meromorphicTrailingCoeffAt_gammaGQ_one`, `meromorphicTrailingCoeffAt_gammaGG_one`,
  `tendsto_sub_one_mul_gammaGQ`, `tendsto_sub_one_mul_gammaGG`: their residues `2 C_F` and
  `2 C_A`, and `tendsto_sub_one_mul_moment_pgq` for the moments of `P_gq`. All hold without
  hypotheses except `meromorphicTrailingCoeffAt_gammaGG_one`, which needs `C_A ≠ 0`.
* `singletGluon_flavorBlindMatrix_mulVec_eq_gammaS_mulVec`: when `n_f` is the number of quark
  flavours, `γ^S` is the matrix by which the flavour-blind matrix of the four anomalous dimensions
  acts on `(Σ, g)`.
* `one_vecMul_gammaS_two_eq_zero`: `(1, 1)` is a left null vector of `γ^S(2)`, the momentum sum
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

/-- The singlet-normalised leading-order quark-in-gluon anomalous dimension
`2 n_f γ_qg(N) = 2 n_f T_F (N² + N + 2) / (N (N+1) (N+2))`, the quark-from-gluon entry of
`gammaS`, as `pqgSinglet` is of the kernels. -/
noncomputable def gammaQGSinglet (N : ℂ) : ℂ :=
  2 * c.nF * gammaQG c N

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

theorem gammaQGSinglet_apply (N : ℂ) : gammaQGSinglet c N = 2 * c.nF * gammaQG c N :=
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

/-- The singlet-normalised `2 n_f γ_qg` continues the moments of `pqgSinglet` from the real
half-line `N > 0`. -/
theorem gammaQGSinglet_ofReal_eq_moment {N : ℝ} (hN : 0 < N) :
    gammaQGSinglet c N = (pqgSinglet c).moment N := by
  rw [gammaQGSinglet_apply, gammaQG_apply, moment_pqgSinglet c hN]
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

/-- `2 n_f γ_qg` is meromorphic on the whole complex plane. -/
@[fun_prop]
theorem meromorphic_gammaQGSinglet : Meromorphic (gammaQGSinglet c) := by
  have h := meromorphic_gammaQG c
  unfold gammaQGSinglet
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
  have h1 : N + 1 ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hN 1
  have hd : N * (N + 1) ≠ 0 := mul_ne_zero h0 h1
  unfold gammaQQ
  fun_prop (disch := assumption)

/-- `γ_qg` is analytic away from `N = 0, -1, -2`. -/
@[fun_prop]
theorem analyticAt_gammaQG {N : ℂ} (h0 : N ≠ 0) (h1 : N ≠ -1) (h2 : N ≠ -2) :
    AnalyticAt ℂ (gammaQG c) N := by
  replace h1 : N + 1 ≠ 0 := fun h => h1 (eq_neg_of_add_eq_zero_left h)
  replace h2 : N + 2 ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
  have hd : N * (N + 1) * (N + 2) ≠ 0 := mul_ne_zero (mul_ne_zero h0 h1) h2
  unfold gammaQG
  fun_prop (disch := assumption)

/-- `2 n_f γ_qg` is analytic away from `N = 0, -1, -2`. -/
@[fun_prop]
theorem analyticAt_gammaQGSinglet {N : ℂ} (h0 : N ≠ 0) (h1 : N ≠ -1) (h2 : N ≠ -2) :
    AnalyticAt ℂ (gammaQGSinglet c) N := by
  have h := analyticAt_gammaQG c h0 h1 h2
  unfold gammaQGSinglet
  fun_prop

/-- `γ_gq` is analytic away from `N = 1, 0, -1`. -/
@[fun_prop]
theorem analyticAt_gammaGQ {N : ℂ} (h : N ≠ 1) (h0 : N ≠ 0) (h1 : N ≠ -1) :
    AnalyticAt ℂ (gammaGQ c) N := by
  replace h : N - 1 ≠ 0 := sub_ne_zero.2 h
  replace h1 : N + 1 ≠ 0 := fun h' => h1 (eq_neg_of_add_eq_zero_left h')
  have hd : (N - 1) * N * (N + 1) ≠ 0 := mul_ne_zero (mul_ne_zero h h0) h1
  unfold gammaGQ
  fun_prop (disch := assumption)

/-- `γ_gg` is analytic away from `N = 1` and the non-positive integers. -/
@[fun_prop]
theorem analyticAt_gammaGG {N : ℂ} (h : N ≠ 1) (hN : ∀ m : ℕ, N ≠ -m) :
    AnalyticAt ℂ (gammaGG c) N := by
  replace h : N - 1 ≠ 0 := sub_ne_zero.2 h
  have h0 : N ≠ 0 := by simpa using hN 0
  have h1 : N + 1 ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hN 1
  have h2 : N + 2 ≠ 0 := by simpa [add_eq_zero_iff_eq_neg] using hN 2
  unfold gammaGG
  fun_prop (disch := assumption)

/-- `γ_qq` is analytic at `N = 1`. -/
@[fun_prop]
theorem analyticAt_gammaQQ_one : AnalyticAt ℂ (gammaQQ c) 1 :=
  analyticAt_gammaQQ c fun m h => Nat.cast_add_one_ne_zero (R := ℂ) m (by linear_combination h)

/-- `γ_qg` is analytic at `N = 1`. -/
@[fun_prop]
theorem analyticAt_gammaQG_one : AnalyticAt ℂ (gammaQG c) 1 :=
  analyticAt_gammaQG c one_ne_zero (by norm_num) (by norm_num)

/-- `2 n_f γ_qg`, the quark-from-gluon entry of `γ^S`, is analytic at `N = 1`. -/
@[fun_prop]
theorem analyticAt_gammaQGSinglet_one : AnalyticAt ℂ (gammaQGSinglet c) 1 :=
  analyticAt_gammaQGSinglet c one_ne_zero (by norm_num) (by norm_num)

/-! ### The poles at `N = 1` -/

/-- The analytic factor `(N - 1) γ_gq(N)` of `γ_gq` at its pole at `N = 1`. -/
private noncomputable def gammaGQAnalyticFactor (N : ℂ) : ℂ :=
  c.cF * (N ^ 2 + N + 2) / (N * (N + 1))

private theorem gammaGQ_eq_inv_smul (N : ℂ) :
    gammaGQ c N = (N - 1)⁻¹ • gammaGQAnalyticFactor c N := by
  simp only [gammaGQ_apply, gammaGQAnalyticFactor, smul_eq_mul, div_eq_mul_inv, mul_inv]
  ring

private theorem analyticAt_gammaGQAnalyticFactor : AnalyticAt ℂ (gammaGQAnalyticFactor c) 1 := by
  unfold gammaGQAnalyticFactor
  fun_prop (disch := norm_num)

private theorem gammaGQAnalyticFactor_one : gammaGQAnalyticFactor c 1 = 2 * c.cF := by
  rw [gammaGQAnalyticFactor]
  ring

/-- **The residue of `γ_gq` at `N = 1`** is `2 C_F`. -/
theorem tendsto_sub_one_mul_gammaGQ :
    Tendsto (fun N => (N - 1) * gammaGQ c N) (𝓝[≠] 1) (𝓝 (2 * c.cF)) := by
  rw [← gammaGQAnalyticFactor_one]
  simpa only [smul_eq_mul] using
    (analyticAt_gammaGQAnalyticFactor c).continuousAt.tendsto_sub_smul_of_eventually_eq_inv_smul
      (Eventually.of_forall (gammaGQ_eq_inv_smul c))

/-- **`γ_gq` has a simple pole at `N = 1`** whenever `C_F ≠ 0`. -/
theorem meromorphicOrderAt_gammaGQ_one (hc : c.cF ≠ 0) :
    meromorphicOrderAt (gammaGQ c) 1 = -1 :=
  AnalyticAt.meromorphicOrderAt_eq_neg_one_of_ne_zero_of_eventually_eq_inv_smul
    (analyticAt_gammaGQAnalyticFactor c)
    (by simp [gammaGQAnalyticFactor_one, hc])
    (Eventually.of_forall (gammaGQ_eq_inv_smul c))

/-- **The residue of `γ_gq` at `N = 1`** as its trailing Laurent coefficient: `2 C_F`. -/
theorem meromorphicTrailingCoeffAt_gammaGQ_one :
    meromorphicTrailingCoeffAt (gammaGQ c) 1 = 2 * c.cF := by
  by_cases hc : c.cF = 0
  · have h0 : gammaGQ c = fun _ => 0 := funext fun N => by simp [gammaGQ_apply, hc]
    simp [h0, meromorphicTrailingCoeffAt_const, hc]
  rw [← gammaGQAnalyticFactor_one]
  exact AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eventually_eq_inv_smul
    (analyticAt_gammaGQAnalyticFactor c)
    (by simp [gammaGQAnalyticFactor_one, hc])
    (Eventually.of_forall (gammaGQ_eq_inv_smul c))

/-- The moments of `P_gq` themselves have the pole: `(N - 1) M[P_gq](N) → 2 C_F` as the real
index `N` decreases to `1`, where the integral defining them stops converging. -/
theorem tendsto_sub_one_mul_moment_pgq :
    Tendsto (fun N : ℝ => (N - 1) * (pgq c).moment N) (𝓝[>] 1) (𝓝 (2 * c.cF)) := by
  rw [← tendsto_ofReal_iff]
  have hmap : Tendsto (fun N : ℝ => (N : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) :=
    tendsto_nhdsWithin_iff.2
      ⟨by simpa using (continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall fun N (hN : 1 < N) => by simpa using hN.ne'⟩
  push_cast
  refine ((tendsto_sub_one_mul_gammaGQ c).comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with N (hN : 1 < N)
  simp [gammaGQ_ofReal_eq_moment c hN]

/-- The analytic factor `(N - 1) γ_gg(N)` of `γ_gg` at its pole at `N = 1`. -/
private noncomputable def gammaGGAnalyticFactor (N : ℂ) : ℂ :=
  (N - 1) * (2 * c.cA * (-complexHarmonic N - 1 / N + 1 / (N + 1) - 1 / (N + 2)) +
    11 / 6 * c.cA - 2 / 3 * c.nF * c.tF) + 2 * c.cA

private theorem gammaGG_eq_inv_smul : ∀ᶠ N in 𝓝[≠] (1 : ℂ),
    gammaGG c N = (N - 1)⁻¹ • gammaGGAnalyticFactor c N := by
  filter_upwards [self_mem_nhdsWithin] with N hN
  have h : N - 1 ≠ 0 := sub_ne_zero.2 hN
  rw [gammaGG_apply, gammaGGAnalyticFactor, smul_eq_mul]
  field_simp
  ring

private theorem analyticAt_gammaGGAnalyticFactor : AnalyticAt ℂ (gammaGGAnalyticFactor c) 1 := by
  have hS : AnalyticAt ℂ complexHarmonic 1 := analyticAt_complexHarmonic_one
  unfold gammaGGAnalyticFactor
  fun_prop (disch := norm_num)

private theorem gammaGGAnalyticFactor_one : gammaGGAnalyticFactor c 1 = 2 * c.cA := by
  simp [gammaGGAnalyticFactor]

/-- **The residue of `γ_gg` at `N = 1`** is `2 C_A`. -/
theorem tendsto_sub_one_mul_gammaGG :
    Tendsto (fun N => (N - 1) * gammaGG c N) (𝓝[≠] 1) (𝓝 (2 * c.cA)) := by
  rw [← gammaGGAnalyticFactor_one]
  simpa only [smul_eq_mul] using
    (analyticAt_gammaGGAnalyticFactor c).continuousAt.tendsto_sub_smul_of_eventually_eq_inv_smul
      (gammaGG_eq_inv_smul c)

/-- **`γ_gg` has a simple pole at `N = 1`** whenever `C_A ≠ 0`. -/
theorem meromorphicOrderAt_gammaGG_one (hc : c.cA ≠ 0) :
    meromorphicOrderAt (gammaGG c) 1 = -1 :=
  AnalyticAt.meromorphicOrderAt_eq_neg_one_of_ne_zero_of_eventually_eq_inv_smul
    (analyticAt_gammaGGAnalyticFactor c)
    (by simp [gammaGGAnalyticFactor_one, hc])
    (gammaGG_eq_inv_smul c)

/-- **The residue of `γ_gg` at `N = 1`** as its trailing Laurent coefficient: `2 C_A`. -/
theorem meromorphicTrailingCoeffAt_gammaGG_one (hc : c.cA ≠ 0) :
    meromorphicTrailingCoeffAt (gammaGG c) 1 = 2 * c.cA := by
  rw [← gammaGGAnalyticFactor_one]
  exact AnalyticAt.meromorphicTrailingCoeffAt_of_ne_zero_of_eventually_eq_inv_smul
    (analyticAt_gammaGGAnalyticFactor c)
    (by simp [gammaGGAnalyticFactor_one, hc])
    (gammaGG_eq_inv_smul c)

/-! ### The singlet matrix -/

/-- The leading-order singlet anomalous-dimension matrix in the basis `(Σ, g)` of the quark
singlet and the gluon, with the row index the daughter and the column index the parent:
`γ^S(N) = !![γ_qq(N), 2 n_f γ_qg(N); γ_gq(N), γ_gg(N)]`, the matrix `Species.singletGluonMatrix`
of the four anomalous dimensions at the real flavour number `n_f`. -/
noncomputable def gammaS (N : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Particles.Parton.Species.singletGluonMatrix (gammaQQ c N) (gammaQG c N) (gammaGQ c N)
    (gammaGG c N) c.nF

theorem gammaS_apply (N : ℂ) :
    gammaS c N = Particles.Parton.Species.singletGluonMatrix (gammaQQ c N) (gammaQG c N)
      (gammaGQ c N) (gammaGG c N) c.nF :=
  (rfl)

/-- The quark-from-quark entry of `γ^S(N)` is `γ_qq(N)`. -/
@[simp]
theorem gammaS_zero_zero (N : ℂ) : gammaS c N 0 0 = gammaQQ c N := by
  rw [gammaS_apply, Particles.Parton.Species.singletGluonMatrix_zero_zero]

/-- The quark-from-gluon entry of `γ^S(N)` is the singlet-normalised `2 n_f γ_qg(N)`. -/
@[simp]
theorem gammaS_zero_one (N : ℂ) : gammaS c N 0 1 = gammaQGSinglet c N := by
  rw [gammaS_apply, Particles.Parton.Species.singletGluonMatrix_zero_one, gammaQGSinglet_apply]

/-- The gluon-from-quark entry of `γ^S(N)` is `γ_gq(N)`. -/
@[simp]
theorem gammaS_one_zero (N : ℂ) : gammaS c N 1 0 = gammaGQ c N := by
  rw [gammaS_apply, Particles.Parton.Species.singletGluonMatrix_one_zero]

/-- The gluon-from-gluon entry of `γ^S(N)` is `γ_gg(N)`. -/
@[simp]
theorem gammaS_one_one (N : ℂ) : gammaS c N 1 1 = gammaGG c N := by
  rw [gammaS_apply, Particles.Parton.Species.singletGluonMatrix_one_one]

open Particles.Parton.Species in
/-- When `n_f` is the number of quark flavours, `γ^S(N)` is the matrix by which the
flavour-blind matrix of the four anomalous dimensions acts on the pair `(Σ, g)`. -/
theorem singletGluon_flavorBlindMatrix_mulVec_eq_gammaS_mulVec {Flavor : Type} [Fintype Flavor]
    [DecidableEq Flavor] (h : (Fintype.card Flavor : ℂ) = c.nF) (N : ℂ)
    (v : Particles.Parton.Species Flavor → ℂ) :
    singletGluon
        (flavorBlindMatrix (gammaQQ c N) (gammaQG c N) (gammaGQ c N) (gammaGG c N) *ᵥ v) =
      gammaS c N *ᵥ singletGluon v := by
  rw [singletGluon_flavorBlindMatrix_mulVec, h, gammaS_apply]

/-- At natural `N ≥ 2`, where all four kernel moments converge, `γ^S(N)` is the matrix of the
moments of the four kernels, with the singlet-normalised `2 n_f P_qg` in the quark-from-gluon
entry. -/
theorem gammaS_natCast_eq_moment {n : ℕ} (hn : 2 ≤ n) :
    gammaS c n =
      (!![(pqq c).moment n, (pqgSinglet c).moment n; (pgq c).moment n, (pgg c).moment n]).map
        ((↑) : ℝ → ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hqg : gammaQGSinglet c n = (pqgSinglet c).moment n := by
    simpa only [ofReal_natCast] using gammaQGSinglet_ofReal_eq_moment c hn0
  have hgq : gammaGQ c n = (pgq c).moment n := by
    simpa only [ofReal_natCast] using gammaGQ_ofReal_eq_moment c hn1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gammaQQ_natCast_eq_moment c (n := n) (by omega), hqg, hgq, gammaGG_natCast_eq_moment c hn]

/-- **The momentum sum rule in moment space.** `(1, 1)` is a left null vector of `γ^S(2)`: both
columns of the singlet matrix sum to zero at the momentum index `N = 2`. -/
theorem one_vecMul_gammaS_two_eq_zero : 1 ᵥ* gammaS c 2 = 0 := by
  have h := gammaS_natCast_eq_moment c (le_refl 2)
  push_cast at h
  rw [h]
  refine funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩) <;>
    simp only [vecMul, dotProduct, Fin.sum_univ_two, Pi.one_apply, one_mul, Pi.zero_apply,
      map_apply, of_apply, cons_val_zero, cons_val_one]
  · exact_mod_cast moment_pqq_two_add_moment_pgq_two_eq_zero c
  · exact_mod_cast (add_comm _ _).trans (moment_pgg_two_add_moment_pqgSinglet_two_eq_zero c)

end Evolution
end Factorization
end QFT
end EpsilonEridani
