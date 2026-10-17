/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# The moment problem on a compact interval

An integrable function on a compact interval `[a, b]` is determined almost everywhere by the
numbers `∫_a^b x^n f(x) dx`, `n ∈ ℕ`: this is the uniqueness half of the Hausdorff moment
problem, and `ae_eq_of_forall_setIntegral_Icc_pow_mul_eq` is the form proved here. The proof is
the classical one — the moments determine the integral of `f` against every polynomial, the
Weierstrass approximation theorem upgrades that to every continuous function, and a function
integrating to zero against every smooth compactly supported test function vanishes almost
everywhere.

Determinacy is sharp in the number of moments used: **no finite set of moments determines the
function.** For every `N` the functions annihilated by the moments of order `0, …, N` already
contain a nonzero polynomial of degree at most `N + 1`, because the `N + 2` monomials of that
degree have only `N + 1` moments to match and so satisfy a nontrivial linear relation
(`exists_polynomial_ne_zero_setIntegral_Icc_pow_mul_eq_zero`). The counterexamples are thus a
nonzero subspace of an explicit `(N + 2)`-dimensional space of polynomials; its lowest member,
`x - (a + b)/2` for `N = 0`, is recorded in `setIntegral_Icc_sub_midpoint_eq_zero`.

The two statements together are what separates a moment *constraint* from moment *knowledge*: a
function on a bounded interval is determined by all of its moments and by no finite part of
them.

## Main results

- `setIntegral_Icc_eval_mul_eq_zero`: vanishing moments give a vanishing integral against every
  polynomial.
- `setIntegral_Icc_mul_eq_zero_of_continuousOn`: the same against every function continuous on
  the interval, by Weierstrass approximation.
- `ae_eq_zero_of_forall_setIntegral_Icc_pow_mul_eq_zero` and
  `ae_eq_of_forall_setIntegral_Icc_pow_mul_eq`: **moment determinacy.**
- `setIntegral_Icc_eval_mul_eq_sum` and `setIntegral_Icc_pow_mul_eval_eq_sum`: moments against a
  polynomial, and the moments of a polynomial, from its coefficients.
- `exists_polynomial_ne_zero_setIntegral_Icc_pow_mul_eq_zero`: **failure of determinacy
  from finitely many moments.**
- `setIntegral_Icc_sub_midpoint_eq_zero`: the lowest counterexample, explicitly.

## References

* N. I. Akhiezer, *The Classical Moment Problem*, Hafner (1965), Chapter 2, for the Hausdorff
  moment problem and the role of polynomial density.

Nothing in this file is physics-specific.
-/

public section

noncomputable section

open MeasureTheory Set

namespace EpsilonEridani

variable {a b : ℝ} {f g : ℝ → ℝ}

/-- The integral of a polynomial against `f` is the coefficient-weighted combination of the
moments of `f`, for any range of indices containing the degree of the polynomial. -/
theorem setIntegral_Icc_eval_mul_eq_sum {m : ℕ} {p : Polynomial ℝ} (hm : p.natDegree < m)
    (hf : IntegrableOn f (Icc a b)) :
    ∫ x in Icc a b, p.eval x * f x
      = ∑ i ∈ Finset.range m, p.coeff i * ∫ x in Icc a b, x ^ i * f x := by
  have hint : ∀ i : ℕ, IntegrableOn (fun x : ℝ => p.coeff i * (x ^ i * f x)) (Icc a b) := by
    intro i
    have h : IntegrableOn (fun x : ℝ => x ^ i * f x) (Icc a b) :=
      IntegrableOn.continuousOn_mul (by fun_prop) hf isCompact_Icc
    exact h.const_mul (p.coeff i)
  have hterm : ∀ x : ℝ, p.eval x * f x
      = ∑ i ∈ Finset.range m, p.coeff i * (x ^ i * f x) := by
    intro x
    rw [Polynomial.eval_eq_sum_range' hm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc ∫ x in Icc a b, p.eval x * f x
      = ∫ x in Icc a b, ∑ i ∈ Finset.range m, p.coeff i * (x ^ i * f x) := by simp_rw [hterm]
    _ = ∑ i ∈ Finset.range m, ∫ x in Icc a b, p.coeff i * (x ^ i * f x) :=
        integral_finsetSum _ fun i _ => hint i
    _ = ∑ i ∈ Finset.range m, p.coeff i * ∫ x in Icc a b, x ^ i * f x :=
        Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- The moments of a polynomial itself, from its coefficients and the moments of the monomials. -/
theorem setIntegral_Icc_pow_mul_eval_eq_sum {m : ℕ} {p : Polynomial ℝ} (hm : p.natDegree < m)
    (n : ℕ) :
    ∫ x in Icc a b, x ^ n * p.eval x
      = ∑ i ∈ Finset.range m, p.coeff i * ∫ x in Icc a b, x ^ (n + i) := by
  have hf : IntegrableOn (fun x : ℝ => x ^ n) (Icc a b) :=
    (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  rw [setIntegral_congr_fun (f := fun x : ℝ => x ^ n * p.eval x)
      (g := fun x : ℝ => p.eval x * x ^ n) measurableSet_Icc fun x _ => mul_comm _ _,
    setIntegral_Icc_eval_mul_eq_sum hm hf]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact setIntegral_congr_fun measurableSet_Icc fun x _ => by rw [← pow_add, add_comm]

/-- If every moment of `f` on `[a, b]` vanishes then so does the integral of `f` against every
polynomial. -/
theorem setIntegral_Icc_eval_mul_eq_zero (hf : IntegrableOn f (Icc a b))
    (hmom : ∀ n : ℕ, ∫ x in Icc a b, x ^ n * f x = 0) (p : Polynomial ℝ) :
    ∫ x in Icc a b, p.eval x * f x = 0 := by
  rw [setIntegral_Icc_eval_mul_eq_sum (Nat.lt_succ_self _) hf]
  simp [hmom]

/-- If every moment of `f` on `[a, b]` vanishes then so does the integral of `f` against every
function continuous on `[a, b]`. This is where the Weierstrass approximation theorem enters. -/
theorem setIntegral_Icc_mul_eq_zero_of_continuousOn (hf : IntegrableOn f (Icc a b))
    (hmom : ∀ n : ℕ, ∫ x in Icc a b, x ^ n * f x = 0) (hg : ContinuousOn g (Icc a b)) :
    ∫ x in Icc a b, g x * f x = 0 := by
  have hgf : IntegrableOn (fun x => g x * f x) (Icc a b) :=
    IntegrableOn.continuousOn_mul hg hf isCompact_Icc
  have habs : IntegrableOn (fun x => |f x|) (Icc a b) := hf.abs
  have hLnonneg : 0 ≤ ∫ x in Icc a b, |f x| :=
    setIntegral_nonneg measurableSet_Icc fun x _ => abs_nonneg _
  -- The integral is within `ε * ∫ |f|` of zero for every `ε > 0`, by approximating `g` uniformly
  -- on `[a, b]` by a polynomial, against which the integral vanishes exactly.
  have key : ∀ ε : ℝ, 0 < ε →
      |∫ x in Icc a b, g x * f x| ≤ ε * ∫ x in Icc a b, |f x| := by
    intro ε hε
    obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b g hg ε hε
    have hpf : IntegrableOn (fun x => p.eval x * f x) (Icc a b) :=
      IntegrableOn.continuousOn_mul p.continuous.continuousOn hf isCompact_Icc
    have hdiff : IntegrableOn (fun x => (g x - p.eval x) * f x) (Icc a b) := by
      simp_rw [sub_mul]; exact hgf.sub hpf
    have hsub : ∫ x in Icc a b, (g x - p.eval x) * f x = ∫ x in Icc a b, g x * f x := by
      simp_rw [sub_mul]
      rw [integral_sub hgf hpf, setIntegral_Icc_eval_mul_eq_zero hf hmom p, sub_zero]
    rw [← hsub]
    calc |∫ x in Icc a b, (g x - p.eval x) * f x|
        ≤ ∫ x in Icc a b, |(g x - p.eval x) * f x| := abs_integral_le_integral_abs
      _ ≤ ∫ x in Icc a b, ε * |f x| := by
          refine setIntegral_mono_on hdiff.abs (habs.const_mul ε) measurableSet_Icc fun x hx => ?_
          rw [abs_mul]
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          rw [← abs_neg, neg_sub]
          exact (hp x hx).le
      _ = ε * ∫ x in Icc a b, |f x| := integral_const_mul ε _
  -- Letting `ε → 0` kills the integral.
  have hzero : |∫ x in Icc a b, g x * f x| ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    rw [zero_add]
    refine (key (ε / ((∫ x in Icc a b, |f x|) + 1)) (by positivity)).trans ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < (∫ x in Icc a b, |f x|) + 1)]
    nlinarith
  exact abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))

/-- **Determinacy of the Hausdorff moment problem.** An integrable function on a compact
interval all of whose moments vanish is almost everywhere zero. -/
theorem ae_eq_zero_of_forall_setIntegral_Icc_pow_mul_eq_zero (hf : IntegrableOn f (Icc a b))
    (hmom : ∀ n : ℕ, ∫ x in Icc a b, x ^ n * f x = 0) :
    f =ᵐ[volume.restrict (Icc a b)] 0 :=
  ae_eq_zero_of_integral_contDiff_smul_eq_zero hf.locallyIntegrable fun φ hφ _ => by
    simpa only [smul_eq_mul] using
      setIntegral_Icc_mul_eq_zero_of_continuousOn hf hmom hφ.continuous.continuousOn

/-- **An integrable function on a compact interval is determined by its moments.** -/
theorem ae_eq_of_forall_setIntegral_Icc_pow_mul_eq (hf : IntegrableOn f (Icc a b))
    (hg : IntegrableOn g (Icc a b))
    (hmom : ∀ n : ℕ, ∫ x in Icc a b, x ^ n * f x = ∫ x in Icc a b, x ^ n * g x) :
    f =ᵐ[volume.restrict (Icc a b)] g := by
  have hdiff : (fun x => f x - g x) =ᵐ[volume.restrict (Icc a b)] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_Icc_pow_mul_eq_zero (hf.sub hg) fun n => ?_
    have hfn : IntegrableOn (fun x : ℝ => x ^ n * f x) (Icc a b) :=
      IntegrableOn.continuousOn_mul (by fun_prop) hf isCompact_Icc
    have hgn : IntegrableOn (fun x : ℝ => x ^ n * g x) (Icc a b) :=
      IntegrableOn.continuousOn_mul (by fun_prop) hg isCompact_Icc
    simp_rw [mul_sub]
    rw [integral_sub hfn hgn, hmom n, sub_self]
  filter_upwards [hdiff] with x hx using by simpa [sub_eq_zero] using hx

/-! ### Failure of determinacy from finitely many moments -/

/-- **No finite set of moments determines a function on `[a, b]`.** For every `N` there is a
nonzero polynomial of degree at most `N + 1`, not identically zero on `[a, b]`, all of whose
moments of order `0, …, N` on `[a, b]` vanish.

The reason is a dimension count: the `N + 2` monomials `1, …, x^(N + 1)` give `N + 2` vectors in
the `(N + 1)`-dimensional space of moment vectors of order `0, …, N`, so they satisfy a
nontrivial linear relation, and the matching linear combination of monomials is the
counterexample. The counterexamples therefore form a nonzero subspace of an explicit
`(N + 2)`-dimensional space of polynomials. Contrast
`ae_eq_of_forall_setIntegral_Icc_pow_mul_eq`, where *all* moments are used. -/
theorem exists_polynomial_ne_zero_setIntegral_Icc_pow_mul_eq_zero (hab : a < b) (N : ℕ) :
    ∃ p : Polynomial ℝ, p ≠ 0 ∧ p.natDegree ≤ N + 1 ∧ (∃ x ∈ Icc a b, p.eval x ≠ 0) ∧
      ∀ n ≤ N, ∫ x in Icc a b, x ^ n * p.eval x = 0 := by
  classical
  -- `N + 2` monomial moment vectors in an `(N + 1)`-dimensional space are linearly dependent.
  obtain ⟨c, hsum, j, hj⟩ : ∃ c : Fin (N + 2) → ℝ,
      ∑ i : Fin (N + 2), c i •
          (fun n : Fin (N + 1) => ∫ x in Icc a b, x ^ ((n : ℕ) + (i : ℕ))) = 0 ∧ ∃ i, c i ≠ 0 := by
    rw [← Fintype.not_linearIndependent_iff]
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fin_fun] at hle
    omega
  set p : Polynomial ℝ := ∑ i : Fin (N + 2), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)
    with hpdef
  have hcoeff : ∀ i : Fin (N + 2), p.coeff (i : ℕ) = c i := by
    intro i
    rw [hpdef]
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow, Fin.val_eq_val]
  have hdeg : p.natDegree ≤ N + 1 := by
    rw [hpdef]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simpa using Nat.lt_succ_iff.mp i.isLt)
  have hne : p ≠ 0 := fun h => hj (by rw [← hcoeff j, h, Polynomial.coeff_zero])
  refine ⟨p, hne, hdeg, ?_, ?_⟩
  · -- A nonzero polynomial has finitely many roots, while `[a, b]` is infinite.
    by_contra hcon
    push Not at hcon
    exact hne (Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.Icc_infinite hab).mono fun x hx => hcon x hx))
  · intro n hn
    have h := congrFun hsum ⟨n, Nat.lt_succ_of_le hn⟩
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h
    rw [setIntegral_Icc_pow_mul_eval_eq_sum (Nat.lt_succ_of_le hdeg) n,
      ← Fin.sum_univ_eq_sum_range
        (fun i => p.coeff i * ∫ x in Icc a b, x ^ (n + i)) (N + 2)]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h
    rw [hcoeff i]

/-- The `N = 0` counterexample, explicitly: `x - (a + b)/2` has vanishing zeroth moment on
`[a, b]`, so the integral of a function over the interval already fails to determine it. -/
theorem setIntegral_Icc_sub_midpoint_eq_zero (hab : a ≤ b) :
    ∫ x in Icc a b, (x - (a + b) / 2) = 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ => x).intervalIntegrable a b)
      intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
  ring

end EpsilonEridani
