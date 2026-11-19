/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.QFT.Factorization.Evolution.Basic
public import EpsilonEridani.Mathematics.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!

# DGLAP Evolution in Moment Space

## i. Overview

Under a Mellin transform in the momentum fraction, the DGLAP integro-differential system
becomes, at each Mellin index `N`, a *linear* ordinary differential system in the log-scale
variable `τ = log Q2`:

`d F i / d τ = (αs (exp τ) / (2 * π)) * ∑ j, γ i j N * F j`,

where `γ i j N` are the anomalous dimensions, the Mellin transforms of the splitting
kernels. This module formalizes that system, its well-posedness, and the conservation of
the sum rules that follows from vanishing column sums of `γ`.

Moment space is the recommended route to well-posedness: the system is linear with
continuous coefficients, so global existence and uniqueness are standard. Well-posedness
directly in `x`-space would need a function-space setting and the plus-distribution
structure of the physical kernels, which is a much larger project and is not attempted
here.

## ii. Key results

- `DglapMomentSystem` is the data of the moment-space system: anomalous dimensions as a
  function of the Mellin index, and a continuous running coupling.
- `IsMomentSolution` is the linear ODE system, stated componentwise with `HasDerivAt`.
- `momentEvolution S N τ₀ τ` is the evolution operator `exp ((∫_{τ₀}^{τ} αs/(2π)) • γ(N))`,
  the exponential of the anomalous-dimension matrix times the `integratedCoupling` of the
  running coupling;
  `momentEvolution_mul` is its cocycle law.
- `moment_exists_unique` is well-posedness: a unique global solution for each initial
  condition, and `IsMomentSolution.eq_momentEvolution_mulVec` identifies every solution with
  the evolution operator applied to its value at a reference scale.
- `IsMomentSolution.apply_eq_exp_mul_of_gamma_apply_eq_zero` is the closed form for a channel
  that mixes with no other: it evolves by the scalar exponential of the integrated coupling times
  its own anomalous dimension. `momentEvolution_apply_of_gamma_apply_eq_zero` is the same fact
  for the corresponding row of the evolution operator, and `momentEvolution_eq_diagonal` and
  `IsMomentSolution.apply_eq_exp_mul_of_gamma_eq_diagonal` are the case of a diagonal
  anomalous-dimension matrix.
- `sumRule_conserved` is the conservation law: if the anomalous-dimension matrix has
  vanishing column sums at `N`, then `∑ i, F i` is `τ`-independent.
- `momentum_sumRule_conserved` and `valence_sumRule_conserved` are its specializations to
  the two physical sum rules.
- `isMomentSolution_momentVector` reduces an `x`-space solution to a moment-space one,
  under the assumption bundle `MomentReductionAssumptions`.

## iii. Conventions

The Mellin index convention of this repository is the one fixed by
`EpsilonEridani.Particles.Parton.PDF.mellinMoment`:

`mellinMoment f n i Q2 = ∫ x in Set.Icc 0 1, x ^ n * f i x Q2`,

i.e. the index `n` counts powers of `x` directly. The momentum sum rule is therefore the
`n = 1` moment and the valence (number) sum rules are the `n = 0` moments. The literature's
`N`-th moment is `∫ x ^ (N - 1) * f`, which puts the momentum sum rule at `N = 2` and the
valence sum rules at `N = 1`. The two indices are recorded as `momentumMomentIndex` and
`valenceMomentIndex` so that no statement in this development has to spell the number out.

The prefactor convention is inherited from `dglapRhsLogScale`: `αs / (2 * π)`, with `αs`
the standard strong coupling.

## iv. Table of contents

- A. The moment-space system
- B. Well-posedness
  - B.1. Uniqueness
  - B.2. Existence: the evolution operator
- C. Sum-rule conservation
  - C.1. The general conservation law
  - C.2. The physical sum rules
- D. Reduction of an `x`-space solution to moment space

-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

variable {Flavor : Type}

/-! ## A. The moment-space system -/

/-- The data of the DGLAP system in moment space, on a finite index set `ι` of flavor
channels.

`gamma N` is the anomalous-dimension matrix at Mellin index `N`: the matrix of Mellin
transforms of the splitting kernels, `γ i j N = M[P i j] N`. `alphaS` is the running
coupling as a function of `Q2`, required to be continuous, which is what makes the
coefficient matrix of the system continuous in `τ` and hence the system well posed. -/
structure DglapMomentSystem (ι : Type) where
  /-- The anomalous-dimension matrix as a function of the Mellin index. -/
  gamma : ℂ → Matrix ι ι ℂ
  /-- The running coupling as a function of `Q2`. -/
  alphaS : ℝ → ℝ
  /-- Continuity of the running coupling in `Q2`. -/
  alphaS_continuous : Continuous alphaS

/-- The right-hand side of the moment-space DGLAP system in channel `i`:

`momentRhs S N τ F i = (S.alphaS (exp τ) / (2 * π)) * ∑ j, S.gamma N i j * F j`.

This is the `i`-th component of the matrix-vector product of the coefficient matrix
`(αs (exp τ) / (2 * π)) • S.gamma N` with `F`, written out as a sum so that no matrix
notation is needed downstream. -/
def momentRhs {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ) (τ : ℝ)
    (F : ι → ℂ) (i : ι) : ℂ :=
  ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ) * ∑ j, S.gamma N i j * F j

/-- `F` solves the moment-space DGLAP system at Mellin index `N`: every component is
differentiable in `τ = log Q2` with derivative the corresponding component of
`momentRhs`. -/
def IsMomentSolution {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    (F : ℝ → ι → ℂ) : Prop :=
  ∀ i τ, HasDerivAt (fun s => F s i) (momentRhs S N τ (F τ) i) τ

/-! ## B. Well-posedness

The vector field `(τ, F) ↦ momentRhs S N τ F` is linear in `F` with coefficients continuous
in `τ`, so on every compact `τ`-interval it is Lipschitz in `F` uniformly in `τ`. Uniqueness
follows by Gronwall (`momentSolution_unique`). Existence is global and explicit: the solution
is the evolution operator `momentEvolution` applied to the initial condition
(`momentSolution_exists`). The two together are `moment_exists_unique`. This is the achievable
form of DGLAP well-posedness; see the module docstring on why `x`-space is not attempted. -/

/-! ### B.1. Uniqueness -/

/-- Uniqueness for the moment-space system: two solutions agreeing at one point agree
everywhere.

The proof is Gronwall's inequality (`ODE_solution_unique_of_mem_Icc`) on a compact interval
containing both scales, where the coupling is bounded and the linear vector field is therefore
Lipschitz. -/
lemma momentSolution_unique {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    {F G : ℝ → ι → ℂ} (hF : IsMomentSolution S N F) (hG : IsMomentSolution S N G)
    (τ0 : ℝ) (h0 : F τ0 = G τ0) (τ : ℝ) :
    F τ = G τ := by
  classical
  set v : ℝ → (ι → ℂ) → (ι → ℂ) := fun t X => momentRhs S N t X with hvdef
  -- the componentwise hypothesis is the vector-valued one, via `hasDerivAt_pi`
  have hFd : ∀ t, HasDerivAt F (v t (F t)) t := fun t => hasDerivAt_pi.2 (fun i => hF i t)
  have hGd : ∀ t, HasDerivAt G (v t (G t)) t := fun t => hasDerivAt_pi.2 (fun i => hG i t)
  -- a compact interval containing both times in its interior
  set a : ℝ := min τ0 τ - 1 with hadef
  set b : ℝ := max τ0 τ + 1 with hbdef
  have hmin : min τ0 τ ≤ max τ0 τ := min_le_max
  have hτ0 : τ0 ∈ Set.Ioo a b :=
    ⟨by simp only [hadef]; have := min_le_left τ0 τ; linarith,
     by simp only [hbdef]; have := le_max_left τ0 τ; linarith⟩
  have hτ : τ ∈ Set.Ioo a b :=
    ⟨by simp only [hadef]; have := min_le_right τ0 τ; linarith,
     by simp only [hbdef]; have := le_max_right τ0 τ; linarith⟩
  -- the coupling is continuous, hence bounded on the compact interval
  have hcont : ContinuousOn (fun t => |S.alphaS (Real.exp t)| / (2 * Real.pi))
      (Set.Icc a b) :=
    (((continuous_abs.comp
      (S.alphaS_continuous.comp Real.continuous_exp)).div_const _)).continuousOn
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr (le_of_lt (hτ0.1.trans hτ0.2))
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  set M : ℝ := |S.alphaS (Real.exp tm)| / (2 * Real.pi) with hMdef
  have hM0 : 0 ≤ M := by positivity
  -- a finite bound on the anomalous-dimension matrix
  set Γ : ℝ := ∑ i : ι, ∑ j : ι, ‖S.gamma N i j‖ with hGdef
  have hΓ0 : 0 ≤ Γ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  refine ODE_solution_unique_of_mem_Icc (K := ⟨M * Γ, by positivity⟩)
    (s := fun _ => Set.univ) ?_ hτ0
    (fun t _ => (hFd t).continuousAt.continuousWithinAt)
    (fun t _ => hFd t) (fun _ _ => Set.mem_univ _)
    (fun t _ => (hGd t).continuousAt.continuousWithinAt)
    (fun t _ => hGd t) (fun _ _ => Set.mem_univ _) h0 (Set.mem_Icc_of_Ioo hτ)
  -- the vector field is Lipschitz on the interval, with the constant just built
  intro t ht
  refine LipschitzOnWith.of_dist_le_mul fun X _ Y _ => ?_
  have hcoef : |S.alphaS (Real.exp t)| / (2 * Real.pi) ≤ M :=
    hmax (Set.mem_Icc_of_Ioo ht)
  simp only [dist_eq_norm] at *
  -- the bound is `↑K * ‖X - Y‖`; `positivity` cannot see through the `set` locals in `K`
  refine (pi_norm_le_iff_of_nonneg
    (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg (X - Y)))).2 fun i => ?_
  -- The componentwise estimate. Done with explicit `calc` steps: `gcongr` picks side goals
  -- that do not line up with `momentRhs`'s normal form here.
  rw [Pi.sub_apply]
  have hc : ‖((S.alphaS (Real.exp t) / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    exact hcoef
  have hdiff : momentRhs S N t X i - momentRhs S N t Y i
      = ((S.alphaS (Real.exp t) / (2 * Real.pi) : ℝ) : ℂ)
          * ∑ j, S.gamma N i j * (X j - Y j) := by
    simp only [momentRhs, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hrow : ‖∑ j, S.gamma N i j * (X j - Y j)‖
      ≤ (∑ j, ‖S.gamma N i j‖) * ‖X - Y‖ := by
    calc ‖∑ j, S.gamma N i j * (X j - Y j)‖
        ≤ ∑ j, ‖S.gamma N i j * (X j - Y j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖S.gamma N i j‖ * ‖X - Y‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          simpa using norm_le_pi_norm (X - Y) j
      _ = (∑ j, ‖S.gamma N i j‖) * ‖X - Y‖ := by rw [Finset.sum_mul]
  have hrowΓ : (∑ j, ‖S.gamma N i j‖) ≤ Γ :=
    Finset.single_le_sum (f := fun i' : ι => ∑ j : ι, ‖S.gamma N i' j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  calc ‖momentRhs S N t X i - momentRhs S N t Y i‖
      = ‖((S.alphaS (Real.exp t) / (2 * Real.pi) : ℝ) : ℂ)‖
          * ‖∑ j, S.gamma N i j * (X j - Y j)‖ := by rw [hdiff, norm_mul]
    _ ≤ M * ((∑ j, ‖S.gamma N i j‖) * ‖X - Y‖) :=
        mul_le_mul hc hrow (norm_nonneg _) hM0
    _ ≤ M * (Γ * ‖X - Y‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hrowΓ (norm_nonneg _)) hM0
    _ = M * Γ * ‖X - Y‖ := by ring

/-! ### B.2. Existence: the evolution operator

The coefficient matrix of the system at log scale `τ` is `a(τ) • γ(N)`, with
`a(τ) = αs(e^τ) / (2π)`: a scalar multiple of the single matrix `γ(N)`. The coefficient matrices
at different scales therefore commute, and the system is solved by the exponential of the
*integrated* coupling times `γ(N)`, with no time ordering. The integrated coupling
`∫_{τ₀}^{τ} a(s) ds` is the evolution variable in which the moment-space flow becomes a
one-parameter group generated by `γ(N)`; on log scales the evolution operators satisfy the
two-parameter cocycle law instead.

The matrix exponential is `NormedSpace.exp` on `Matrix ι ι ℂ` with its product topology. Its
derivative is computed with Mathlib's `L∞` operator norm (`Matrix.Norms.Operator`) installed
locally inside the proof, as in Mathlib's `Matrix.exp_add_of_commute`; no norm on matrices
appears in any statement (`Matrix.hasDerivAt_exp_smul_const_mulVec`). -/

section Existence

variable {ι : Type}

/-- The integrated coupling from log scale `τ₀` to log scale `τ`,

`integratedCoupling αs τ₀ τ = ∫ s in τ₀..τ, αs(e^s) / (2π)`.

It is the evolution variable of the moment-space system: in it the coefficient matrix becomes
the constant `γ(N)`. -/
def integratedCoupling (αs : RunningCoupling) (τ₀ τ : ℝ) : ℝ :=
  ∫ s in τ₀..τ, αs (Real.exp s) / (2 * Real.pi)

lemma integratedCoupling_def (αs : RunningCoupling) (τ₀ τ : ℝ) :
    integratedCoupling αs τ₀ τ = ∫ s in τ₀..τ, αs (Real.exp s) / (2 * Real.pi) := (rfl)

@[simp]
lemma integratedCoupling_self (αs : RunningCoupling) (τ : ℝ) :
    integratedCoupling αs τ τ = 0 := by
  rw [integratedCoupling_def, intervalIntegral.integral_same]

/-- The integrated coupling of a continuous coupling is additive over adjacent scale
intervals. -/
lemma integratedCoupling_add {αs : RunningCoupling} (hαs : Continuous αs) (τ₀ τ₁ τ₂ : ℝ) :
    integratedCoupling αs τ₀ τ₁ + integratedCoupling αs τ₁ τ₂ = integratedCoupling αs τ₀ τ₂ := by
  have h := (hαs.comp Real.continuous_exp).div_const (2 * Real.pi)
  simp only [integratedCoupling_def]
  exact intervalIntegral.integral_add_adjacent_intervals (h.intervalIntegrable _ _)
    (h.intervalIntegrable _ _)

/-- Reversing the scale interval reverses the sign of the integrated coupling. -/
lemma integratedCoupling_swap (αs : RunningCoupling) (τ₀ τ : ℝ) :
    integratedCoupling αs τ τ₀ = -integratedCoupling αs τ₀ τ := by
  simp only [integratedCoupling_def]
  exact intervalIntegral.integral_symm τ₀ τ

/-- The integrated coupling of a continuous coupling has derivative `αs(e^τ) / (2π)` in its
upper limit. -/
lemma hasDerivAt_integratedCoupling {αs : RunningCoupling} (hαs : Continuous αs) (τ₀ τ : ℝ) :
    HasDerivAt (integratedCoupling αs τ₀) (αs (Real.exp τ) / (2 * Real.pi)) τ :=
  (((hαs.comp Real.continuous_exp).div_const (2 * Real.pi)).integral_hasStrictDerivAt
    τ₀ τ).hasDerivAt

/-- For a continuous coupling that is positive at every positive scale, the integrated coupling
is strictly increasing in its upper limit, so it is an admissible reparametrisation of the log
scale. -/
lemma strictMono_integratedCoupling {αs : RunningCoupling} (hαs : Continuous αs)
    (hα : ∀ Q2, 0 < Q2 → 0 < αs Q2) (τ₀ : ℝ) :
    StrictMono (integratedCoupling αs τ₀) :=
  strictMono_of_hasDerivAt_pos (hasDerivAt_integratedCoupling hαs τ₀) fun τ =>
    div_pos (hα _ (Real.exp_pos τ)) (by positivity)

/-- The moment-space evolution operator from log scale `τ₀` to log scale `τ` at Mellin
index `N`: the matrix exponential of the integrated coupling times the anomalous-dimension
matrix,

`momentEvolution S N τ₀ τ = exp ((∫ s in τ₀..τ, αs(e^s) / (2π)) • γ(N))`.

This is the standard moment-space solution of DGLAP evolution (Furmanski and Petronzio,
Z. Phys. C 11 (1982) 293). -/
def momentEvolution [Fintype ι] [DecidableEq ι] (S : DglapMomentSystem ι) (N : ℂ) (τ₀ τ : ℝ) :
    Matrix ι ι ℂ :=
  NormedSpace.exp ((integratedCoupling S.alphaS τ₀ τ : ℂ) • S.gamma N)

section momentEvolution

variable [Fintype ι] [DecidableEq ι]

lemma momentEvolution_def (S : DglapMomentSystem ι) (N : ℂ) (τ₀ τ : ℝ) :
    momentEvolution S N τ₀ τ =
      NormedSpace.exp ((integratedCoupling S.alphaS τ₀ τ : ℂ) • S.gamma N) :=
  (rfl)

@[simp]
lemma momentEvolution_self (S : DglapMomentSystem ι) (N : ℂ) (τ : ℝ) :
    momentEvolution S N τ τ = 1 := by
  rw [momentEvolution_def, integratedCoupling_self, Complex.ofReal_zero, zero_smul,
    NormedSpace.exp_zero]

/-- **The cocycle law.** Evolving from `τ₀` to `τ₁` and then from `τ₁` to `τ₂` is evolving from
`τ₀` to `τ₂`. -/
lemma momentEvolution_mul (S : DglapMomentSystem ι) (N : ℂ) (τ₀ τ₁ τ₂ : ℝ) :
    momentEvolution S N τ₁ τ₂ * momentEvolution S N τ₀ τ₁ = momentEvolution S N τ₀ τ₂ := by
  simp only [momentEvolution_def]
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl (S.gamma N)).smul_left _).smul_right _),
    ← add_smul, ← integratedCoupling_add S.alphaS_continuous τ₀ τ₁ τ₂]
  congr 2
  push_cast
  ring

/-- Evolving backwards from `τ` to `τ₀` inverts evolving from `τ₀` to `τ`. -/
lemma momentEvolution_swap (S : DglapMomentSystem ι) (N : ℂ) (τ₀ τ : ℝ) :
    momentEvolution S N τ τ₀ = (momentEvolution S N τ₀ τ)⁻¹ := by
  simp only [momentEvolution_def]
  rw [integratedCoupling_swap, Complex.ofReal_neg, neg_smul, Matrix.exp_neg]

/-- The evolution operator applied to a fixed vector has the moment-space right-hand side
`a(τ) • γ(N) *ᵥ ·` as its derivative in the log scale. -/
lemma hasDerivAt_momentEvolution_mulVec (S : DglapMomentSystem ι) (N : ℂ) (τ₀ τ : ℝ)
    (F₀ : ι → ℂ) :
    HasDerivAt (fun s => momentEvolution S N τ₀ s *ᵥ F₀)
      (((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ) •
        (S.gamma N *ᵥ (momentEvolution S N τ₀ τ *ᵥ F₀))) τ := by
  simpa only [momentEvolution_def] using Matrix.hasDerivAt_exp_smul_const_mulVec
    (hasDerivAt_integratedCoupling S.alphaS_continuous τ₀ τ).ofReal_comp (S.gamma N) F₀

/-- The evolution operator applied to an initial vector solves the moment-space system. -/
theorem isMomentSolution_momentEvolution_mulVec (S : DglapMomentSystem ι) (N : ℂ) (τ₀ : ℝ)
    (F₀ : ι → ℂ) :
    IsMomentSolution S N fun τ => momentEvolution S N τ₀ τ *ᵥ F₀ := by
  intro i τ
  have h := hasDerivAt_pi.1 (hasDerivAt_momentEvolution_mulVec S N τ₀ τ F₀) i
  simpa only [momentRhs, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_apply_eq_sum] using h

/-- Every solution of the moment-space system is the evolution operator applied to its value at
any reference scale: `F τ = momentEvolution S N τ₀ τ *ᵥ F τ₀`. -/
theorem IsMomentSolution.eq_momentEvolution_mulVec {S : DglapMomentSystem ι} {N : ℂ}
    {F : ℝ → ι → ℂ} (hF : IsMomentSolution S N F) (τ₀ τ : ℝ) :
    F τ = momentEvolution S N τ₀ τ *ᵥ F τ₀ :=
  momentSolution_unique S N hF (isMomentSolution_momentEvolution_mulVec S N τ₀ (F τ₀)) τ₀
    (by rw [momentEvolution_self, Matrix.one_mulVec]) τ

omit [DecidableEq ι] in
/-- **The closed form for an unmixed channel.** If channel `i` mixes with no other channel at
`N`, that is if the off-diagonal entries of row `i` of the anomalous-dimension matrix vanish,
channel `i` of a solution evolves multiplicatively:
`F τ i = exp ((∫ s in τ₀..τ, αs(e^s) / (2π)) * γ i i) * F τ₀ i`.

Only row `i` enters, so this applies to a non-singlet channel inside a full flavor system whose
singlet sector mixes quarks and gluons. -/
theorem IsMomentSolution.apply_eq_exp_mul_of_gamma_apply_eq_zero {S : DglapMomentSystem ι}
    {N : ℂ} {F : ℝ → ι → ℂ} (hF : IsMomentSolution S N F) {i : ι}
    (h : ∀ j, j ≠ i → S.gamma N i j = 0) (τ₀ τ : ℝ) :
    F τ i = Complex.exp (integratedCoupling S.alphaS τ₀ τ * S.gamma N i i) * F τ₀ i := by
  set c : ℝ → ℂ := fun s => (integratedCoupling S.alphaS τ₀ s : ℂ) with hc
  -- `exp (-c s * γ i i) * F s i` is constant in `s`
  have hderiv : ∀ s,
      HasDerivAt (fun s => Complex.exp (-(c s * S.gamma N i i)) * F s i) 0 s := by
    intro s
    have hcs : HasDerivAt c ((S.alphaS (Real.exp s) / (2 * Real.pi) : ℝ) : ℂ) s :=
      (hasDerivAt_integratedCoupling S.alphaS_continuous τ₀ s).ofReal_comp
    have hFs : HasDerivAt (fun s => F s i)
        (((S.alphaS (Real.exp s) / (2 * Real.pi) : ℝ) : ℂ) * (S.gamma N i i * F s i)) s := by
      have hFi := hF i s
      rwa [momentRhs, Finset.sum_eq_single i (fun j _ hj => by rw [h j hj, zero_mul])
        (fun hi => absurd (Finset.mem_univ i) hi)] at hFi
    convert ((hcs.mul_const (S.gamma N i i)).neg.cexp).mul hFs using 1
    ring
  have hconst := eq_of_hasDerivAt_zero hderiv τ τ₀
  simp only [hc, integratedCoupling_self, Complex.ofReal_zero, zero_mul, neg_zero,
    Complex.exp_zero, one_mul] at hconst
  rw [← hconst, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- **The evolution operator of an unmixed channel.** If the off-diagonal entries of row `i` of
the anomalous-dimension matrix at `N` vanish, row `i` of the evolution operator is the scalar
exponential of the integrated coupling times `γ i i`, placed on the diagonal. -/
lemma momentEvolution_apply_of_gamma_apply_eq_zero {S : DglapMomentSystem ι} {N : ℂ} {i : ι}
    (h : ∀ j, j ≠ i → S.gamma N i j = 0) (τ₀ τ : ℝ) (j : ι) :
    momentEvolution S N τ₀ τ i j =
      if i = j then Complex.exp (integratedCoupling S.alphaS τ₀ τ * S.gamma N i i) else 0 := by
  -- the `j`-th column is the solution starting from the `j`-th basis vector
  have hcol := (isMomentSolution_momentEvolution_mulVec S N τ₀ (Pi.single j 1)
    ).apply_eq_exp_mul_of_gamma_apply_eq_zero h τ₀ τ
  simpa only [Matrix.mulVec_single_one, momentEvolution_self, Matrix.col_apply,
    Matrix.one_apply, mul_ite, mul_one, mul_zero] using hcol

/-- Without mixing between channels, that is for a diagonal anomalous-dimension matrix, each
channel evolves by the scalar exponential of the integrated coupling times its own anomalous
dimension. -/
lemma momentEvolution_eq_diagonal {S : DglapMomentSystem ι} {N : ℂ} {d : ι → ℂ}
    (h : S.gamma N = Matrix.diagonal d) (τ₀ τ : ℝ) :
    momentEvolution S N τ₀ τ =
      Matrix.diagonal fun i => Complex.exp (integratedCoupling S.alphaS τ₀ τ * d i) := by
  ext i j
  rw [momentEvolution_apply_of_gamma_apply_eq_zero
      (fun j hj => by rw [h, Matrix.diagonal_apply_ne d hj.symm]),
    Matrix.diagonal_apply, h, Matrix.diagonal_apply_eq]

/-- **The closed form without channel mixing.** If the anomalous-dimension matrix at `N` is
diagonal, as for the non-singlet combinations, each channel of a solution evolves
multiplicatively:
`F τ i = exp ((∫ s in τ₀..τ, αs(e^s) / (2π)) * d i) * F τ₀ i`. -/
theorem IsMomentSolution.apply_eq_exp_mul_of_gamma_eq_diagonal {S : DglapMomentSystem ι}
    {N : ℂ} {d : ι → ℂ} (h : S.gamma N = Matrix.diagonal d) {F : ℝ → ι → ℂ}
    (hF : IsMomentSolution S N F) (τ₀ τ : ℝ) (i : ι) :
    F τ i = Complex.exp (integratedCoupling S.alphaS τ₀ τ * d i) * F τ₀ i := by
  rw [hF.eq_momentEvolution_mulVec τ₀ τ, momentEvolution_eq_diagonal h, Matrix.mulVec_diagonal]

end momentEvolution

/-- Global existence for the moment-space system: for every Mellin index, initial log scale and
initial condition there is a solution, namely `τ ↦ momentEvolution S N τ0 τ *ᵥ F0`. -/
lemma momentSolution_exists [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ) (F0 : ι → ℂ) (τ0 : ℝ) :
    ∃ F : ℝ → ι → ℂ, F τ0 = F0 ∧ IsMomentSolution S N F := by
  classical
  exact ⟨fun τ => momentEvolution S N τ0 τ *ᵥ F0,
    by simp only [momentEvolution_self, Matrix.one_mulVec],
    isMomentSolution_momentEvolution_mulVec S N τ0 F0⟩

/-- **Well-posedness of DGLAP evolution in moment space.** For each Mellin index `N` and
each initial condition `F0` at `τ0`, the linear moment-space system has a unique global
solution. -/
theorem moment_exists_unique [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ) (F0 : ι → ℂ) (τ0 : ℝ) :
    ∃! F : ℝ → ι → ℂ, F τ0 = F0 ∧ IsMomentSolution S N F := by
  obtain ⟨F, hF0, hF⟩ := momentSolution_exists S N F0 τ0
  refine ⟨F, ⟨hF0, hF⟩, ?_⟩
  intro G hG
  funext τ
  exact momentSolution_unique S N hG.2 hF τ0 (hG.1.trans hF0.symm) τ

end Existence

/-! ## C. Sum-rule conservation -/

/-! ### C.1. The general conservation law -/

/-- **Sum-rule conservation in moment space.** If the anomalous-dimension matrix at Mellin
index `N` has vanishing column sums, `∑ i, γ i j N = 0` for every `j`, then the total moment
`∑ i, F i` of any solution is independent of the log scale.

The hypothesis is exactly the constraint the splitting kernels satisfy in QCD: momentum
conservation in the splitting process is `∑ i, ∫ z * P i j z = 0`, which in moment space is
the vanishing of the column sums of `γ` at the momentum index. -/
theorem sumRule_conserved {ι : Type} [Fintype ι] (S : DglapMomentSystem ι) (N : ℂ)
    (hcol : ∀ j, ∑ i, S.gamma N i j = 0)
    (F : ℝ → ι → ℂ) (hF : IsMomentSolution S N F) (τ₁ τ₂ : ℝ) :
    ∑ i, F τ₁ i = ∑ i, F τ₂ i := by
  have hderiv : ∀ τ : ℝ, HasDerivAt (fun s => ∑ i, F s i) 0 τ := by
    intro τ
    have hsum : HasDerivAt (fun s => ∑ i, F s i) (∑ i, momentRhs S N τ (F τ) i) τ :=
      HasDerivAt.fun_sum fun i _ => hF i τ
    have hzero : ∑ i, momentRhs S N τ (F τ) i = 0 := by
      calc ∑ i, momentRhs S N τ (F τ) i
          = ∑ i, ∑ j, ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ)
              * (S.gamma N i j * F τ j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [momentRhs, Finset.mul_sum]
        _ = ∑ j, ∑ i, ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ)
              * (S.gamma N i j * F τ j) := Finset.sum_comm
        _ = ∑ j, ((S.alphaS (Real.exp τ) / (2 * Real.pi) : ℝ) : ℂ)
              * ((∑ i, S.gamma N i j) * F τ j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
        _ = 0 := by
            refine Finset.sum_eq_zero fun j _ => ?_
            rw [hcol j, zero_mul, mul_zero]
    rwa [hzero] at hsum
  exact eq_of_hasDerivAt_zero hderiv τ₁ τ₂

/-! ### C.2. The physical sum rules -/

/-- The Mellin index carrying the momentum sum rule, in the convention of
`EpsilonEridani.Particles.Parton.PDF.mellinMoment` (`mellinMoment f n = ∫ x ^ n * f`), namely
`n = 1`. In the literature's convention, where the `N`-th moment is `∫ x ^ (N - 1) * f`, the
same sum rule sits at `N = 2`. -/
def momentumMomentIndex : ℂ := 1

/-- The Mellin index carrying the valence (number) sum rules, in the convention of
`EpsilonEridani.Particles.Parton.PDF.mellinMoment`, namely `n = 0`. In the literature's convention
the same sum rules sit at `N = 1`. -/
def valenceMomentIndex : ℂ := 0

/-- **Momentum sum-rule conservation.** If the anomalous dimensions have vanishing column
sums at the momentum index, the total momentum fraction carried by the partons is
independent of the scale.

This is the moment-space counterpart of the `momentum` field of
`EpsilonEridani.Particles.Parton.PDF.SumRuleAssumptions`, which asserts
`∑ i, mellinMoment f 1 i Q2 = 1` at every `Q2`: the theorem here supplies the reason that
assertion can hold at every scale at once, namely that the DGLAP flow preserves the total
first moment. Connecting the two literally — turning `∑ i, F τ i` into
`∑ i, mellinMoment f 1 i (exp τ)` — needs the reduction of section D together with the
Mellin convolution theorem of task `task/e1-mellin-convolution`. -/
theorem momentum_sumRule_conserved {ι : Type} [Fintype ι] (S : DglapMomentSystem ι)
    (hcol : ∀ j, ∑ i, S.gamma momentumMomentIndex i j = 0)
    (F : ℝ → ι → ℂ) (hF : IsMomentSolution S momentumMomentIndex F) (τ₁ τ₂ : ℝ) :
    ∑ i, F τ₁ i = ∑ i, F τ₂ i :=
  sumRule_conserved S momentumMomentIndex hcol F hF τ₁ τ₂

/-- **Valence sum-rule conservation.** If the anomalous dimensions have vanishing column
sums at the valence index, the total parton number is independent of the scale.

For the physical valence sum rules one applies this to the non-singlet combinations, whose
anomalous dimension at the valence index vanishes on its own. -/
theorem valence_sumRule_conserved {ι : Type} [Fintype ι] (S : DglapMomentSystem ι)
    (hcol : ∀ j, ∑ i, S.gamma valenceMomentIndex i j = 0)
    (F : ℝ → ι → ℂ) (hF : IsMomentSolution S valenceMomentIndex F) (τ₁ τ₂ : ℝ) :
    ∑ i, F τ₁ i = ∑ i, F τ₂ i :=
  sumRule_conserved S valenceMomentIndex hcol F hF τ₁ τ₂

/-! ## D. Reduction of an `x`-space solution to moment space -/

/-- The Mellin-moment vector of a PDF family at index `n`, as a function of the log scale
`τ = log Q2`, valued in `ℂ` so that it can be fed to the moment-space system. -/
def momentVector (f : EpsilonEridani.Particles.Parton.PDF.Pdf Flavor) (n : ℕ) (τ : ℝ)
    (i : Flavor) : ℂ :=
  ((EpsilonEridani.Particles.Parton.PDF.mellinMoment f n i (Real.exp τ) : ℝ) : ℂ)

/-- Transport of a real derivative along the inclusion `ℝ → ℂ`.

This is `HasDerivAt.ofReal_comp` (`Mathlib/Analysis/Complex/RealDeriv.lean`), which is
exactly the composition with the `ℝ`-linear isometry `Complex.ofRealCLM` that the earlier
note anticipated. -/
lemma hasDerivAt_ofReal {g : ℝ → ℝ} {g' τ : ℝ} (h : HasDerivAt g g' τ) :
    HasDerivAt (fun s => ((g s : ℝ) : ℂ)) ((g' : ℝ) : ℂ) τ :=
  h.ofReal_comp

/-- Assumptions reducing an `x`-space DGLAP solution to the moment-space linear system at
index `n`, with real anomalous dimensions `γ`.

Neither field is an opaque proposition: `derivMoment` is the interchange of the
`τ`-derivative with the moment integral (differentiation under the integral sign, which
needs dominated-convergence hypotheses not available in this development), and
`mellinFactorization` is the Mellin convolution theorem for the collinear kernel, which is
the target of task `task/e1-mellin-convolution`. Once that task lands, both become
derivable from integrability assumptions on `f` and `P` rather than assumed. -/
structure MomentReductionAssumptions [Fintype Flavor]
    (P : SplittingKernel Flavor) (αs : RunningCoupling)
    (f : EpsilonEridani.Particles.Parton.PDF.Pdf Flavor)
    (S : DglapMomentSystem Flavor) (n : ℕ) (γ : Flavor → Flavor → ℝ) : Prop where
  /-- The system's coupling is the one driving the `x`-space equation. -/
  coupling : S.alphaS = αs
  /-- The system's anomalous dimensions at the real index `n` are the real matrix `γ`. -/
  gamma_ofReal : ∀ i j, S.gamma (n : ℂ) i j = ((γ i j : ℝ) : ℂ)
  /-- Differentiation under the moment integral: the `τ`-derivative of the `n`-th moment of
  `f` is the `n`-th moment of the DGLAP right-hand side. -/
  derivMoment : ∀ i τ,
    HasDerivAt (fun s => EpsilonEridani.Particles.Parton.PDF.mellinMoment f n i (Real.exp s))
      (∫ x in Set.Icc (0 : ℝ) 1, x ^ n * dglapRhsLogScale P αs f i x τ) τ
  /-- Mellin convolution theorem: the `n`-th moment of the convolution right-hand side is
  the anomalous-dimension matrix acting on the moments. -/
  mellinFactorization : ∀ i τ,
    (∫ x in Set.Icc (0 : ℝ) 1, x ^ n * dglapRhsLogScale P αs f i x τ)
      = αs (Real.exp τ) / (2 * Real.pi)
        * ∑ j, γ i j * EpsilonEridani.Particles.Parton.PDF.mellinMoment f n j (Real.exp τ)

/-- Under `MomentReductionAssumptions`, the Mellin moments of an `x`-space DGLAP solution
solve the moment-space linear system, so the well-posedness and conservation results of this
module apply to them. -/
lemma isMomentSolution_momentVector [Fintype Flavor]
    (P : SplittingKernel Flavor) (αs : RunningCoupling)
    (f : EpsilonEridani.Particles.Parton.PDF.Pdf Flavor)
    (S : DglapMomentSystem Flavor) (n : ℕ) (γ : Flavor → Flavor → ℝ)
    (h : MomentReductionAssumptions P αs f S n γ) :
    IsMomentSolution S (n : ℂ) (momentVector f n) := by
  intro i τ
  have hreal : HasDerivAt
      (fun s => EpsilonEridani.Particles.Parton.PDF.mellinMoment f n i (Real.exp s))
      (αs (Real.exp τ) / (2 * Real.pi)
        * ∑ j, γ i j * EpsilonEridani.Particles.Parton.PDF.mellinMoment f n j (Real.exp τ)) τ := by
    have hd := h.derivMoment i τ
    rwa [h.mellinFactorization i τ] at hd
  have hrhs : momentRhs S (n : ℂ) τ (momentVector f n τ) i
      = ((αs (Real.exp τ) / (2 * Real.pi)
          * ∑ j, γ i j
            * EpsilonEridani.Particles.Parton.PDF.mellinMoment f n j (Real.exp τ) : ℝ) : ℂ) := by
    simp only [momentRhs, momentVector, h.coupling, h.gamma_ofReal]
    push_cast
    ring
  rw [hrhs]
  exact hasDerivAt_ofReal hreal

end Evolution
end Factorization
end QFT
end EpsilonEridani
