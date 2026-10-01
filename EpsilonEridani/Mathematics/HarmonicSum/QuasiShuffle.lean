/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.HarmonicSum.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The quasi-shuffle product of nested harmonic sums

The product of two nested harmonic sums of the same argument is an integer linear combination of
nested harmonic sums of that argument. Writing `t_a(i) = sign(a)^i / i^{|a|}` for the summand of
an index `a`, the combination is computed by the recursion

  `S_{a,m} · S_{b,m'} = S_{a, m * (b,m')} + S_{b, (a,m) * m'} - S_{a ⋄ b, m * m'}`,

with the empty multi-index as unit, where `a ⋄ b = sign(a) sign(b) (|a| + |b|)` is the index whose
summand is the product `t_a(i) t_b(i)`. The minus sign comes from the diagonal `i₁ = j₁` of the
two outermost summations, which the first two terms count twice because the nesting of the
sums `S` is non-strict.

The formal linear combinations are finitely supported functions `List ℤ →₀ ℤ`, and a
combination `c` is evaluated at the argument `N` by `Finsupp.linearCombination ℤ
(harmonicSum · N) c`. This is the quasi-shuffle product of Hoffman on generators (multi-indices):
it is commutative and has the empty multi-index as unit, and its evaluation at `N` is the product
of the two sums, which is what reduces every product of harmonic sums of one argument to a linear
combination of them. Its bilinear extension to formal combinations, its associativity and the
resulting algebra structure are not formalised here.

## Main definitions

* `EpsilonEridani.HarmonicSum.indexMul a b`: the index `a ⋄ b` with `t_{a ⋄ b} = t_a t_b`.
* `EpsilonEridani.HarmonicSum.quasiShuffle m m'`: the quasi-shuffle product of two multi-indices,
  as a formal integer combination of multi-indices.

## Main statements

* `EpsilonEridani.harmonicSum_mul_harmonicSum`: `S_m(N) S_{m'}(N)` is the evaluation at `N` of
  `quasiShuffle m m'`.
* `EpsilonEridani.HarmonicSum.quasiShuffle_comm`: the product is commutative.
* `EpsilonEridani.HarmonicSum.weight_of_mem_support_quasiShuffle`: for indices that are all
  non-zero, the product is homogeneous of weight `weight m + weight m'`, and its multi-indices
  again have non-zero entries (`ne_zero_of_mem_support_quasiShuffle`).

The depth-one relation `S_a S_b = S_{a,b} + S_{b,a} - S_{a ⋄ b}` and its special case
`S₁ S₁ = 2 S_{1,1} - S₂` are worked out as examples at the end of the file.

## References

* J. A. M. Vermaseren, *Harmonic sums, Mellin transforms and integrals*,
  Int. J. Mod. Phys. A 14 (1999) 2037, arXiv:hep-ph/9806280, section 2.
* M. E. Hoffman, *Quasi-shuffle products*, J. Algebraic Combin. 11 (2000) 49,
  arXiv:math/9907173.
-/

public section

namespace EpsilonEridani

namespace HarmonicSum

/-- The product of two indices in the quasi-shuffle algebra of harmonic sums,
`a ⋄ b = sign(a) sign(b) (|a| + |b|)`: the index whose summand is the product of the summands of
`a` and `b` (`term_indexMul`). For example `1 ⋄ 1 = 2` and `1 ⋄ (-1) = -2`. -/
def indexMul (a b : ℤ) : ℤ :=
  a.sign * b.sign * ((a.natAbs + b.natAbs : ℕ) : ℤ)

theorem indexMul_def (a b : ℤ) :
    indexMul a b = a.sign * b.sign * ((a.natAbs + b.natAbs : ℕ) : ℤ) :=
  (rfl)

theorem indexMul_comm (a b : ℤ) : indexMul a b = indexMul b a := by
  simp only [indexMul, mul_comm a.sign, add_comm a.natAbs]

@[simp]
theorem indexMul_zero_left (b : ℤ) : indexMul 0 b = 0 := by
  simp [indexMul]

@[simp]
theorem indexMul_zero_right (a : ℤ) : indexMul a 0 = 0 := by
  simp [indexMul]

theorem sign_indexMul (a b : ℤ) : (indexMul a b).sign = a.sign * b.sign := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have h : a.natAbs + b.natAbs ≠ 0 := by simp [ha]
  rw [indexMul, Int.sign_mul, Int.sign_natCast_of_ne_zero h]
  simp

theorem natAbs_indexMul {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (indexMul a b).natAbs = a.natAbs + b.natAbs := by
  rw [indexMul, Int.natAbs_mul, Int.natAbs_natCast]
  simp [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero ha, Int.natAbs_sign_of_ne_zero hb]

/-- For positive indices, `a ⋄ b = a + b`. -/
theorem indexMul_of_pos {a b : ℤ} (ha : 0 < a) (hb : 0 < b) : indexMul a b = a + b := by
  rw [indexMul, Int.sign_eq_one_of_pos ha, Int.sign_eq_one_of_pos hb]
  omega

theorem indexMul_ne_zero {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) : indexMul a b ≠ 0 := by
  rw [← Int.natAbs_ne_zero, natAbs_indexMul ha hb]
  simp [ha]

/-- The summand of `a ⋄ b` is the product of the summands of `a` and `b`, at every positive
value of the summation variable. -/
theorem term_indexMul (a b : ℤ) {i : ℕ} (hi : i ≠ 0) :
    term (indexMul a b) i = term a i * term b i := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [hi]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [hi]
  simp only [term_def, sign_indexMul, natAbs_indexMul ha hb]
  push_cast
  ring

/-- The quasi-shuffle product of two multi-indices, as a formal integer linear combination of
multi-indices, defined by the recursion
`(a, m) * (b, m') = (a, m * (b, m')) + (b, (a, m) * m') - (a ⋄ b, m * m')` with the empty
multi-index as unit. Its evaluation at `N` is the product of the two nested harmonic sums
(`harmonicSum_mul_harmonicSum`). -/
noncomputable def quasiShuffle : List ℤ → List ℤ → (List ℤ →₀ ℤ)
  | [], m' => Finsupp.single m' 1
  | m, [] => Finsupp.single m 1
  | a :: m, b :: m' =>
    (quasiShuffle m (b :: m')).mapDomain (a :: ·) +
      (quasiShuffle (a :: m) m').mapDomain (b :: ·) -
      (quasiShuffle m m').mapDomain (indexMul a b :: ·)

@[simp]
theorem quasiShuffle_nil_left (m' : List ℤ) : quasiShuffle [] m' = Finsupp.single m' 1 := by
  rw [quasiShuffle]

@[simp]
theorem quasiShuffle_nil_right (m : List ℤ) : quasiShuffle m [] = Finsupp.single m 1 := by
  cases m with
  | nil => rw [quasiShuffle]
  | cons a m => rw [quasiShuffle]; exact List.cons_ne_nil a m

theorem quasiShuffle_cons_cons (a b : ℤ) (m m' : List ℤ) :
    quasiShuffle (a :: m) (b :: m') =
      (quasiShuffle m (b :: m')).mapDomain (a :: ·) +
        (quasiShuffle (a :: m) m').mapDomain (b :: ·) -
        (quasiShuffle m m').mapDomain (indexMul a b :: ·) := by
  rw [quasiShuffle]

/-- The quasi-shuffle product is commutative. -/
theorem quasiShuffle_comm (m m' : List ℤ) : quasiShuffle m m' = quasiShuffle m' m := by
  induction m, m' using quasiShuffle.induct with
  | case1 m' => simp
  | case2 m hm => simp
  | case3 a m b m' ih₁ ih₂ ih₃ =>
    simp only [quasiShuffle_cons_cons, ih₁, ih₂, ih₃, indexMul_comm a b, add_comm]

/-- For multi-indices whose entries are all non-zero, every multi-index occurring in the
quasi-shuffle product of `m` and `m'` has weight `weight m + weight m'` and again has non-zero
entries. The two conclusions are proved together because the induction for the weight needs the
non-vanishing of the entries; they are stated separately as
`weight_of_mem_support_quasiShuffle` and `ne_zero_of_mem_support_quasiShuffle`. -/
theorem weight_and_ne_zero_of_mem_support_quasiShuffle {m m' : List ℤ} (hm : ∀ a ∈ m, a ≠ 0)
    (hm' : ∀ b ∈ m', b ≠ 0) {w : List ℤ} (hw : w ∈ (quasiShuffle m m').support) :
    weight w = weight m + weight m' ∧ ∀ c ∈ w, c ≠ 0 := by
  classical
  induction m, m' using quasiShuffle.induct generalizing w with
  | case1 m' =>
    simp only [quasiShuffle_nil_left] at hw
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
    exact ⟨by simp, hm'⟩
  | case2 m hm'' =>
    simp only [quasiShuffle_nil_right] at hw
    rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hw)]
    exact ⟨by simp, hm⟩
  | case3 a m b m' ih₁ ih₂ ih₃ =>
    have ha := hm a List.mem_cons_self
    have hb := hm' b List.mem_cons_self
    have hmt : ∀ c ∈ m, c ≠ 0 := fun c hc => hm c (List.mem_cons_of_mem a hc)
    have hmt' : ∀ c ∈ m', c ≠ 0 := fun c hc => hm' c (List.mem_cons_of_mem b hc)
    rw [quasiShuffle_cons_cons] at hw
    have hw' := Finsupp.support_sub hw
    rw [Finset.mem_union] at hw'
    rcases hw' with hw' | hw'
    · rcases Finset.mem_union.1 (Finsupp.support_add hw') with hw' | hw'
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw')
        obtain ⟨hvw, hv0⟩ := ih₁ hmt hm' hv
        refine ⟨?_, List.forall_mem_cons.2 ⟨ha, hv0⟩⟩
        simp only [weight_cons, hvw]
        omega
      · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw')
        obtain ⟨hvw, hv0⟩ := ih₂ hm hmt' hv
        refine ⟨?_, List.forall_mem_cons.2 ⟨hb, hv0⟩⟩
        simp only [weight_cons, hvw]
        omega
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw')
      obtain ⟨hvw, hv0⟩ := ih₃ hmt hmt' hv
      refine ⟨?_, List.forall_mem_cons.2 ⟨indexMul_ne_zero ha hb, hv0⟩⟩
      simp only [weight_cons, hvw, natAbs_indexMul ha hb]
      omega

/-- For multi-indices whose entries are all non-zero, every multi-index occurring in the
quasi-shuffle product of `m` and `m'` has weight `weight m + weight m'`: the product is
homogeneous for the weight grading. -/
theorem weight_of_mem_support_quasiShuffle {m m' : List ℤ} (hm : ∀ a ∈ m, a ≠ 0)
    (hm' : ∀ b ∈ m', b ≠ 0) {w : List ℤ} (hw : w ∈ (quasiShuffle m m').support) :
    weight w = weight m + weight m' :=
  (weight_and_ne_zero_of_mem_support_quasiShuffle hm hm' hw).1

/-- For multi-indices whose entries are all non-zero, every multi-index occurring in the
quasi-shuffle product of `m` and `m'` again has non-zero entries. Together with
`weight_of_mem_support_quasiShuffle` this lets the weight grading be applied to iterated
products. -/
theorem ne_zero_of_mem_support_quasiShuffle {m m' : List ℤ} (hm : ∀ a ∈ m, a ≠ 0)
    (hm' : ∀ b ∈ m', b ≠ 0) {w : List ℤ} (hw : w ∈ (quasiShuffle m m').support) :
    ∀ c ∈ w, c ≠ 0 :=
  (weight_and_ne_zero_of_mem_support_quasiShuffle hm hm' hw).2

end HarmonicSum

open HarmonicSum

/-- **The quasi-shuffle relation.** The product of two nested harmonic sums of the same argument
is the evaluation at that argument of the quasi-shuffle product of their multi-indices. -/
theorem harmonicSum_mul_harmonicSum (m m' : List ℤ) (n : ℕ) :
    harmonicSum m n * harmonicSum m' n =
      Finsupp.linearCombination ℤ (harmonicSum · n) (quasiShuffle m m') := by
  induction m, m' using quasiShuffle.induct generalizing n with
  | case1 m' => simp
  | case2 m hm => simp
  | case3 a m b m' ih₁ ih₂ ih₃ =>
    -- Induction on the argument: both sides vanish at `0`, and at `n + 1` each side changes by
    -- the outermost summands at `n + 1`, which match by the inductive hypotheses for the three
    -- shorter products and `term_indexMul`.
    induction n with
    | zero =>
      simp only [quasiShuffle_cons_cons, map_sub, map_add, linearCombination_mapDomain_cons_zero]
      simp
    | succ n ihn =>
      simp only [quasiShuffle_cons_cons, map_sub, map_add, linearCombination_mapDomain_cons_succ,
        ← ih₁, ← ih₂, ← ih₃, term_indexMul a b n.add_one_ne_zero] at ihn ⊢
      rw [harmonicSum_cons_succ a m n, harmonicSum_cons_succ b m' n]
      linear_combination ihn

/-! ### Examples -/

/-- The quasi-shuffle relation in depth one: `S_a S_b = S_{a,b} + S_{b,a} - S_{a ⋄ b}`. -/
example (a b : ℤ) (n : ℕ) :
    harmonicSum [a] n * harmonicSum [b] n =
      harmonicSum [a, b] n + harmonicSum [b, a] n - harmonicSum [indexMul a b] n := by
  rw [harmonicSum_mul_harmonicSum, quasiShuffle_cons_cons]
  simp [Finsupp.mapDomain_single]

/-- The simplest quasi-shuffle relation, `S₁(N) S₁(N) = 2 S_{1,1}(N) - S₂(N)`. -/
example (n : ℕ) :
    harmonicSum [1] n * harmonicSum [1] n = 2 * harmonicSum [1, 1] n - harmonicSum [2] n := by
  rw [harmonicSum_mul_harmonicSum, quasiShuffle_cons_cons]
  have : indexMul 1 1 = 2 := by decide
  simp [Finsupp.mapDomain_single, this]
  ring

end EpsilonEridani
