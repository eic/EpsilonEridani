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
in closed form in `EpsilonEridani.QFT.Factorization.Evolution.Kernel.LeadingOrder`, wherever the
integral defining them converges. With the first harmonic sum continued to complex argument as
`S₁(s) = ψ(s + 1) + γ` (`EpsilonEridani.complexHarmonic`), the closed forms

* `γ_qq(N) = C_F [3/2 - 2 S₁(N) + 1/(N (N+1))]`,
* `γ_gq(N) = C_F (N² + N + 2) / ((N-1) N (N+1))`,
* `γ_qg(N) = T_F (N² + N + 2) / (N (N+1) (N+2))` per flavour,
* `γ_gg(N) = 2 C_A [-S₁(N) + 1/(N-1) - 1/N + 1/(N+1) - 1/(N+2)] + (11/6) C_A - (2/3) n_f T_F`

are meromorphic functions on the whole complex `N`-plane. They are normalised to `α_s / (2π)`, as
the kernels are, and the inverse Mellin transform that reconstructs the densities integrates them
along a contour in the complex plane, to the right of their rightmost singularity.

The singlet anomalous-dimension matrix `γ^S(N)` acts on the pair `(Σ, g)` of the quark singlet
`Σ = ∑ᵢ (qᵢ + q̄ᵢ)` and the gluon, with the row index the daughter and the column index the parent:

  `γ^S(N) = !![γ_qq(N), 2 n_f γ_qg(N); γ_gq(N), γ_gg(N)]`.

It is the matrix `Species.singletGluonMatrix` of
`EpsilonEridani.Particles.Parton.SingletDecomposition`, through which a flavour-blind kernel acts
on the singlet sector, evaluated at the four leading-order entries.

The pole structure at `N = 1` is the moment-space form of the small-`x` behaviour: `γ_gq` and
`γ_gg` have simple poles there, with residues `2 C_F` and `2 C_A`, the colour charges of the
emitting parton, and `γ_qq` and `γ_qg` are analytic there. The pole of `γ_gq` is also visible on
the moments themselves: `(N - 1) M[P_gq](N) → 2 C_F` as the real index `N` decreases to `1`.

## Main definitions

* `gammaQQ`, `gammaGQ`, `gammaQG`, `gammaGG`: the four leading-order anomalous dimensions as
  functions of complex `N`, with `gammaQG` per flavour as `pqg` is.
* `gammaS`: the singlet anomalous-dimension matrix in the basis `(Σ, g)`.

## Main statements

* `gammaQQ_natCast`, `gammaGQ_ofReal`, `gammaQG_ofReal`, `gammaGG_natCast`, `gammaS_natCast`:
  the continuations agree with the kernel moments wherever those converge in the closed forms of
  `LeadingOrder`.
* `meromorphic_gammaQQ`, `meromorphic_gammaGQ`, `meromorphic_gammaQG`, `meromorphic_gammaGG`:
  the entries of `γ^S` are meromorphic on `ℂ`.
* `analyticAt_gammaQQ`, `analyticAt_gammaQG`, `analyticAt_gammaGQ`, `analyticAt_gammaGG`: the
  regions of analyticity; in particular `γ_qq` and `γ_qg` are analytic at `N = 1`.
* `meromorphicOrderAt_gammaGQ_one`, `meromorphicOrderAt_gammaGG_one`: simple poles at `N = 1`.
* `tendsto_sub_one_mul_gammaGQ`, `tendsto_sub_one_mul_gammaGG`: their residues `2 C_F` and
  `2 C_A`, and `tendsto_sub_one_mul_moment_pgq` for the moments of `P_gq`.
* `gammaS_eq_singletGluonMatrix`: `γ^S` is the singlet block of a flavour-blind matrix.
* `vecMul_gammaS_two`: `(1, 1)` is a left null vector of `γ^S(2)`, the momentum sum rule.

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
theorem gammaQQ_natCast {n : ℕ} (hn : n ≠ 0) : gammaQQ c n = (pqq c).moment n := by
  rw [moment_pqq c hn, gammaQQ_apply, complexHarmonic_natCast]
  push_cast
  ring

/-- `γ_gq` continues the moments of `P_gq` from the real half-line `N > 1`. -/
theorem gammaGQ_ofReal {N : ℝ} (hN : 1 < N) : gammaGQ c N = (pgq c).moment N := by
  rw [moment_pgq c hN, gammaGQ_apply]
  push_cast
  ring

/-- `γ_qg` continues the moments of the per-flavour kernel `P_qg` from the real half-line
`N > 0`. -/
theorem gammaQG_ofReal {N : ℝ} (hN : 0 < N) : gammaQG c N = (pqg c).moment N := by
  rw [moment_pqg c hN, gammaQG_apply]
  push_cast
  ring

/-- `γ_gg` continues the moments of `P_gg` from the natural indices `N ≥ 2`. -/
theorem gammaGG_natCast {n : ℕ} (hn : 2 ≤ n) : gammaGG c n = (pgg c).moment n := by
  rw [moment_pgg c hn, gammaGG_apply, complexHarmonic_natCast]
  push_cast
  ring

/-- **Quark-number conservation** in moment space: `γ_qq(1) = 0`. -/
@[simp]
theorem gammaQQ_one : gammaQQ c 1 = 0 := by
  simpa using gammaQQ_natCast c one_ne_zero

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
theorem analyticAt_gammaQQ {N : ℂ} (hN : ∀ m : ℕ, N ≠ -m) : AnalyticAt ℂ (gammaQQ c) N := by
  have h0 : N ≠ 0 := by simpa using hN 0
  have h1 : N + 1 ≠ 0 := fun h => hN 1 (by push_cast; linear_combination h)
  have hd : N * (N + 1) ≠ 0 := mul_ne_zero h0 h1
  have hS : AnalyticAt ℂ complexHarmonic N :=
    analyticAt_complexHarmonic fun m h => hN (m + 1) (by push_cast; exact h)
  unfold gammaQQ
  fun_prop (disch := assumption)

/-- `γ_qg` is analytic away from `N = 0, -1, -2`. -/
theorem analyticAt_gammaQG {N : ℂ} (h0 : N ≠ 0) (h1 : N ≠ -1) (h2 : N ≠ -2) :
    AnalyticAt ℂ (gammaQG c) N := by
  replace h1 : N + 1 ≠ 0 := fun h => h1 (eq_neg_of_add_eq_zero_left h)
  replace h2 : N + 2 ≠ 0 := fun h => h2 (eq_neg_of_add_eq_zero_left h)
  unfold gammaQG
  fun_prop (disch := exact mul_ne_zero (mul_ne_zero h0 h1) h2)

/-- `γ_gq` is analytic away from `N = 1, 0, -1`. -/
theorem analyticAt_gammaGQ {N : ℂ} (h : N ≠ 1) (h0 : N ≠ 0) (h1 : N ≠ -1) :
    AnalyticAt ℂ (gammaGQ c) N := by
  replace h : N - 1 ≠ 0 := sub_ne_zero.2 h
  replace h1 : N + 1 ≠ 0 := fun h' => h1 (eq_neg_of_add_eq_zero_left h')
  unfold gammaGQ
  fun_prop (disch := exact mul_ne_zero (mul_ne_zero h h0) h1)

/-- `γ_gg` is analytic away from `N = 1` and the non-positive integers. -/
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

/-- `γ_qq` is analytic at `N = 1`. -/
theorem analyticAt_gammaQQ_one : AnalyticAt ℂ (gammaQQ c) 1 :=
  analyticAt_gammaQQ c fun m h => by
    have h' : (1 : ℝ) = -m := by simpa using congrArg re h
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- `γ_qg` is analytic at `N = 1`. -/
theorem analyticAt_gammaQG_one : AnalyticAt ℂ (gammaQG c) 1 :=
  analyticAt_gammaQG c one_ne_zero (by norm_num) (by norm_num)

/-! ### The poles at `N = 1` -/

/-- The analytic factor of `γ_gq` at its pole at `N = 1`. -/
private theorem gammaGQ_eq_inv_mul (N : ℂ) :
    gammaGQ c N = (N - 1)⁻¹ * (c.cF * (N ^ 2 + N + 2) / (N * (N + 1))) := by
  simp only [gammaGQ_apply, div_eq_mul_inv, mul_inv]
  ring

private theorem analyticAt_gammaGQ_residue :
    AnalyticAt ℂ (fun N : ℂ => c.cF * (N ^ 2 + N + 2) / (N * (N + 1))) 1 := by
  fun_prop (disch := norm_num)

/-- **The residue of `γ_gq` at `N = 1`** is `2 C_F`. -/
theorem tendsto_sub_one_mul_gammaGQ :
    Tendsto (fun N => (N - 1) * gammaGQ c N) (𝓝[≠] 1) (𝓝 (2 * c.cF)) := by
  have ht := ((analyticAt_gammaGQ_residue c).continuousAt.continuousWithinAt (s := {1}ᶜ)).tendsto
  rw [show (c.cF : ℂ) * (1 ^ 2 + 1 + 2) / (1 * (1 + 1)) = 2 * c.cF by ring] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with N hN
  rw [gammaGQ_eq_inv_mul, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hN), one_mul]

/-- **`γ_gq` has a simple pole at `N = 1`** whenever `C_F ≠ 0`. -/
theorem meromorphicOrderAt_gammaGQ_one (hc : c.cF ≠ 0) :
    meromorphicOrderAt (gammaGQ c) 1 = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast,
    meromorphicOrderAt_eq_int_iff (meromorphic_gammaGQ c 1)]
  refine ⟨_, analyticAt_gammaGQ_residue c, by norm_num [hc], ?_⟩
  filter_upwards with N
  rw [gammaGQ_eq_inv_mul, _root_.zpow_neg_one, smul_eq_mul]

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

/-- The analytic factor of `γ_gg` at its pole at `N = 1`. -/
private noncomputable def gammaGGResidue (N : ℂ) : ℂ :=
  (N - 1) * (2 * c.cA * (-complexHarmonic N - 1 / N + 1 / (N + 1) - 1 / (N + 2)) +
    11 / 6 * c.cA - 2 / 3 * c.nF * c.tF) + 2 * c.cA

private theorem gammaGG_eq_inv_mul {N : ℂ} (hN : N ≠ 1) :
    gammaGG c N = (N - 1)⁻¹ * gammaGGResidue c N := by
  have h : N - 1 ≠ 0 := sub_ne_zero.2 hN
  rw [gammaGG_apply, gammaGGResidue]
  field_simp
  ring

private theorem analyticAt_gammaGGResidue : AnalyticAt ℂ (gammaGGResidue c) 1 := by
  have hS : AnalyticAt ℂ complexHarmonic 1 :=
    analyticAt_complexHarmonic fun m h => by
      have h' : (1 : ℝ) = -(m + 1) := by simpa using congrArg re h
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  unfold gammaGGResidue
  fun_prop (disch := norm_num)

private theorem gammaGGResidue_one : gammaGGResidue c 1 = 2 * c.cA := by
  simp [gammaGGResidue]

/-- **The residue of `γ_gg` at `N = 1`** is `2 C_A`. -/
theorem tendsto_sub_one_mul_gammaGG :
    Tendsto (fun N => (N - 1) * gammaGG c N) (𝓝[≠] 1) (𝓝 (2 * c.cA)) := by
  have ht := ((analyticAt_gammaGGResidue c).continuousAt.continuousWithinAt (s := {1}ᶜ)).tendsto
  rw [gammaGGResidue_one] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with N hN
  rw [gammaGG_eq_inv_mul c hN, ← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.2 hN), one_mul]

/-- **`γ_gg` has a simple pole at `N = 1`** whenever `C_A ≠ 0`. -/
theorem meromorphicOrderAt_gammaGG_one (hc : c.cA ≠ 0) :
    meromorphicOrderAt (gammaGG c) 1 = -1 := by
  rw [show (-1 : WithTop ℤ) = ((-1 : ℤ) : WithTop ℤ) by norm_cast,
    meromorphicOrderAt_eq_int_iff (meromorphic_gammaGG c 1)]
  refine ⟨_, analyticAt_gammaGGResidue c, by simp [gammaGGResidue_one, hc], ?_⟩
  filter_upwards [self_mem_nhdsWithin] with N hN
  rw [gammaGG_eq_inv_mul c hN, _root_.zpow_neg_one, smul_eq_mul]

/-! ### The singlet matrix -/

/-- The leading-order singlet anomalous-dimension matrix in the basis `(Σ, g)` of the quark
singlet and the gluon, with the row index the daughter and the column index the parent:
`γ^S(N) = !![γ_qq(N), 2 n_f γ_qg(N); γ_gq(N), γ_gg(N)]`. -/
noncomputable def gammaS (N : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![gammaQQ c N, 2 * c.nF * gammaQG c N; gammaGQ c N, gammaGG c N]

theorem gammaS_apply (N : ℂ) :
    gammaS c N = !![gammaQQ c N, 2 * c.nF * gammaQG c N; gammaGQ c N, gammaGG c N] :=
  (rfl)

@[simp]
theorem gammaS_zero_zero (N : ℂ) : gammaS c N 0 0 = gammaQQ c N := (rfl)

@[simp]
theorem gammaS_zero_one (N : ℂ) : gammaS c N 0 1 = 2 * c.nF * gammaQG c N := (rfl)

@[simp]
theorem gammaS_one_zero (N : ℂ) : gammaS c N 1 0 = gammaGQ c N := (rfl)

@[simp]
theorem gammaS_one_one (N : ℂ) : gammaS c N 1 1 = gammaGG c N := (rfl)

/-- For an integer number `n` of active flavours, `γ^S(N)` is the matrix by which the
flavour-blind matrix of the four anomalous dimensions acts on the pair `(Σ, g)`
(`Species.singletGluon_flavorBlindMatrix_mulVec`). -/
theorem gammaS_eq_singletGluonMatrix {n : ℕ} (hn : c.nF = n) (N : ℂ) :
    gammaS c N =
      Particles.Parton.Species.singletGluonMatrix (gammaQQ c N) (gammaQG c N) (gammaGQ c N)
        (gammaGG c N) n := by
  rw [gammaS_apply, Particles.Parton.Species.singletGluonMatrix_def, hn]
  norm_cast

/-- At natural `N ≥ 2`, where all four kernel moments converge, `γ^S(N)` is the matrix of the
moments of the four kernels, with the singlet-normalised `2 n_f P_qg` in the quark-from-gluon
entry. -/
theorem gammaS_natCast {n : ℕ} (hn : 2 ≤ n) :
    gammaS c n =
      (!![(pqq c).moment n, (pqgSinglet c).moment n; (pgq c).moment n, (pgg c).moment n]).map
        ((↑) : ℝ → ℂ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  rw [gammaS_apply, gammaQQ_natCast c (by omega), gammaGG_natCast c hn,
    show ((n : ℂ)) = ((n : ℝ) : ℂ) by norm_cast, gammaQG_ofReal c hn0, gammaGQ_ofReal c hn1,
    pqgSinglet_def, KernelForm.moment_smul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **The momentum sum rule in moment space.** `(1, 1)` is a left null vector of `γ^S(2)`: both
columns of the singlet matrix sum to zero at the momentum index `N = 2`. -/
theorem vecMul_gammaS_two : vecMul (fun _ => 1) (gammaS c 2) = 0 := by
  have h := gammaS_natCast c (le_refl 2)
  push_cast at h
  rw [h]
  ext j
  fin_cases j
  · simp [vecMul, dotProduct, Fin.sum_univ_two]
  · simp [vecMul, dotProduct, Fin.sum_univ_two]

end Evolution
end Factorization
end QFT
end EpsilonEridani
