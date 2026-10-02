/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Nested harmonic sums

For a multi-index `m = [m₁, …, m_k]` of integers, the nested harmonic sum is

  `S_{m₁,…,m_k}(N) = ∑_{N ≥ i₁ ≥ i₂ ≥ ⋯ ≥ i_k ≥ 1} ∏_j sign(m_j)^{i_j} / i_j^{|m_j|}`,

defined by the recursion on the outermost index

  `S_∅(N) = 1`,  `S_{m₁,m₂,…,m_k}(N) = ∑_{i=1}^{N} sign(m₁)^i / i^{|m₁|} · S_{m₂,…,m_k}(i)`.

A positive index `m` contributes the factor `1 / i^m`, and a negative index `m` the alternating
factor `(-1)^i / i^{|m|}`. The length of `m` is the *depth* of the sum (`List.length`) and the
sum of the absolute values of its entries is the *weight*, `HarmonicSum.weight`.

The zero index is not part of the standard family. With the definition above it contributes the
factor `0^i = 0` for `i ≥ 1`, so any multi-index containing `0` gives the zero sum; that is a junk
value, and every statement below holds without excluding it.

The sums take values in `ℚ`, like Mathlib's `harmonic`, which is the depth-one sum
`S₁` (`harmonicSum_singleton_one_eq_harmonic`). Real and complex versions are obtained by casting.

The Mellin moments of the splitting kernels and coefficient functions of perturbative QCD are
expressed in terms of these sums; the product of two sums of the same argument is again a linear
combination of such sums, which is the quasi-shuffle product of
`EpsilonEridani.Mathematics.HarmonicSum.QuasiShuffle`.

## Main definitions

* `EpsilonEridani.HarmonicSum.term m i`: the summand `sign(m)^i / i^{|m|}` of an index `m`.
* `EpsilonEridani.harmonicSum m N`: the nested harmonic sum `S_m(N)`.
* `EpsilonEridani.HarmonicSum.weight m`: the weight `∑ |m_j|` of a multi-index.

## Main statements

* `EpsilonEridani.harmonicSum_cons_succ`: the recursion
  `S_{a,m}(N+1) = S_{a,m}(N) + term a (N+1) · S_m(N+1)` in the upper argument.
* `EpsilonEridani.harmonicSum_singleton_one_eq_harmonic`: `S₁ = harmonic`.
* `EpsilonEridani.harmonicSum_pos`: sums with positive indices are positive.

## References

* J. A. M. Vermaseren, *Harmonic sums, Mellin transforms and integrals*,
  Int. J. Mod. Phys. A 14 (1999) 2037, arXiv:hep-ph/9806280.
* J. Blümlein and S. Kurth, *Harmonic sums and Mellin transforms up to two-loop order*,
  Phys. Rev. D 60 (1999) 014018, arXiv:hep-ph/9810241.
-/

public section

namespace EpsilonEridani

namespace HarmonicSum

/-- The summand attached to an index `m` at the summation variable `i`,
`sign(m)^i / i^{|m|}`. For `m > 0` this is `1 / i^m`; for `m < 0` it is `(-1)^i / i^{|m|}`. -/
def term (m : ℤ) (i : ℕ) : ℚ :=
  (m.sign : ℚ) ^ i / (i : ℚ) ^ m.natAbs

theorem term_def (m : ℤ) (i : ℕ) : term m i = (m.sign : ℚ) ^ i / (i : ℚ) ^ m.natAbs :=
  (rfl)

@[simp]
theorem term_zero_left {i : ℕ} (hi : i ≠ 0) : term 0 i = 0 := by
  simp [term, hi]

theorem term_of_pos {m : ℤ} (hm : 0 < m) (i : ℕ) : term m i = 1 / (i : ℚ) ^ m.natAbs := by
  simp [term, Int.sign_eq_one_of_pos hm]

theorem term_of_neg {m : ℤ} (hm : m < 0) (i : ℕ) :
    term m i = (-1) ^ i / (i : ℚ) ^ m.natAbs := by
  simp [term, Int.sign_eq_neg_one_of_neg hm]

@[simp]
theorem term_one_left (i : ℕ) : term 1 i = (i : ℚ)⁻¹ := by
  simp [term]

theorem term_pos {m : ℤ} (hm : 0 < m) {i : ℕ} (hi : i ≠ 0) : 0 < term m i := by
  have : (0 : ℚ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi
  rw [term_of_pos hm]
  exact one_div_pos.2 (pow_pos this _)

/-- The weight `∑ |m_j|` of a multi-index. Together with the depth `m.length` it grades the
nested harmonic sums. -/
def weight (m : List ℤ) : ℕ :=
  (m.map Int.natAbs).sum

theorem weight_def (m : List ℤ) : weight m = (m.map Int.natAbs).sum :=
  (rfl)

@[simp]
theorem weight_nil : weight [] = 0 :=
  (rfl)

@[simp]
theorem weight_cons (a : ℤ) (m : List ℤ) : weight (a :: m) = a.natAbs + weight m := by
  simp [weight]

@[simp]
theorem weight_append (m m' : List ℤ) : weight (m ++ m') = weight m + weight m' := by
  simp [weight]

end HarmonicSum

open HarmonicSum

/-- The nested harmonic sum `S_m(N)` of a multi-index `m = [m₁, …, m_k]`, defined by the
recursion on the outermost index: `S_∅(N) = 1` and
`S_{m₁,m₂,…}(N) = ∑_{i=1}^{N} sign(m₁)^i / i^{|m₁|} · S_{m₂,…}(i)`. -/
def harmonicSum : List ℤ → ℕ → ℚ
  | [], _ => 1
  | a :: m, n => ∑ i ∈ Finset.range n, term a (i + 1) * harmonicSum m (i + 1)

@[simp]
theorem harmonicSum_nil (n : ℕ) : harmonicSum [] n = 1 :=
  (rfl)

theorem harmonicSum_cons (a : ℤ) (m : List ℤ) (n : ℕ) :
    harmonicSum (a :: m) n = ∑ i ∈ Finset.range n, term a (i + 1) * harmonicSum m (i + 1) :=
  (rfl)

@[simp]
theorem harmonicSum_cons_zero (a : ℤ) (m : List ℤ) : harmonicSum (a :: m) 0 = 0 := by
  simp [harmonicSum_cons]

/-- The recursion in the upper argument:
`S_{a,m}(N+1) = S_{a,m}(N) + term a (N+1) · S_m(N+1)`. -/
@[simp]
theorem harmonicSum_cons_succ (a : ℤ) (m : List ℤ) (n : ℕ) :
    harmonicSum (a :: m) (n + 1) =
      harmonicSum (a :: m) n + term a (n + 1) * harmonicSum m (n + 1) := by
  simp only [harmonicSum_cons, Finset.sum_range_succ]

/-- The sum over the summation range `1 ≤ i ≤ N`, as it is usually written. -/
theorem harmonicSum_cons_eq_sum_Icc (a : ℤ) (m : List ℤ) (n : ℕ) :
    harmonicSum (a :: m) n = ∑ i ∈ Finset.Icc 1 n, term a i * harmonicSum m i := by
  rw [harmonicSum_cons, Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun i => term a i * harmonicSum m i) 0 n (c := 1)]
  simp only [zero_add, Finset.Ico_add_one_right_eq_Icc]

/-- The first harmonic sum `S₁` is Mathlib's `harmonic`. -/
theorem harmonicSum_singleton_one_eq_harmonic (n : ℕ) : harmonicSum [1] n = harmonic n := by
  simp [harmonicSum_cons, harmonic]

/-- A multi-index containing `0` gives the zero sum at every argument. -/
theorem harmonicSum_eq_zero_of_zero_mem {m : List ℤ} (hm : 0 ∈ m) (n : ℕ) :
    harmonicSum m n = 0 := by
  induction m generalizing n with
  | nil => simp at hm
  | cons a m ih =>
    rcases List.mem_cons.1 hm with rfl | hm
    · simp [harmonicSum_cons]
    · simp [harmonicSum_cons, ih hm]

/-- A nested harmonic sum all of whose indices are positive is positive at every positive
argument. -/
theorem harmonicSum_pos {m : List ℤ} (hm : ∀ a ∈ m, 0 < a) {n : ℕ} (hn : n ≠ 0) :
    0 < harmonicSum m n := by
  induction m generalizing n with
  | nil => simp
  | cons a m ih =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    rw [harmonicSum_cons, Finset.sum_range_succ]
    have ha := hm a List.mem_cons_self
    have hm' : ∀ b ∈ m, 0 < b := fun b hb => hm b (List.mem_cons_of_mem a hb)
    refine add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun i _ => ?_) ?_
    · exact (mul_pos (term_pos ha i.succ_ne_zero) (ih hm' i.succ_ne_zero)).le
    · exact mul_pos (term_pos ha n.succ_ne_zero) (ih hm' n.succ_ne_zero)

/-! ### Small values -/

/-- `S₁(1) = 1`. -/
theorem harmonicSum_singleton_one_one : harmonicSum [1] 1 = 1 := by
  norm_num [harmonicSum_cons]

/-- `S₁(2) = 3/2`. -/
theorem harmonicSum_singleton_one_two : harmonicSum [1] 2 = 3 / 2 := by
  norm_num [harmonicSum_cons, Finset.sum_range_succ]

/-- `S₂(2) = 5/4`. -/
theorem harmonicSum_singleton_two_two : harmonicSum [2] 2 = 5 / 4 := by
  norm_num [harmonicSum_cons, Finset.sum_range_succ, term_of_pos]

example : harmonicSum [-1] 2 = -1 / 2 := by
  norm_num [harmonicSum_cons, Finset.sum_range_succ, term_of_neg]

example : harmonicSum [1, 1] 2 = 7 / 4 := by
  norm_num [harmonicSum_cons, Finset.sum_range_succ]

end EpsilonEridani
