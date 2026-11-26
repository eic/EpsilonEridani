/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import EpsilonEridani.Mathematics.Analysis.Asymptotics.ApproximatesToOrder
public import EpsilonEridani.QFT.Quarkonium.NRQCD.PowerCounting
public import Mathlib.LinearAlgebra.Matrix.Rank
import EpsilonEridani.Mathematics.Analysis.Asymptotics.TruncatedExpansion
import TauCeti.LinearAlgebra.Matrix.Rank

/-!
# Matching coefficients and their uniqueness

A matching coefficient of non-relativistic QCD is not computed from a formula: it is *defined* by
the condition that the effective theory reproduces the full theory. This module states that
condition for the operator basis of a velocity power counting (`PowerCounting`) and proves that it
determines the coefficients exactly when an explicit matrix, with finitely many columns, has full
column rank.

The data are a set `A` of amplitudes (each a process at fixed external momenta), and for every
amplitude `a`:

* the full-theory amplitude `F a ε`, as a function of the power-counting parameter `ε`;
* the velocity-stripped matrix element `M a o` of each composite operator `o`: the matrix element
  of `o` in the amplitude `a` is `M a o * ε ^ k` when `o` has total degree `k`, so that `ε` counts
  the orders in the relative velocity `v` and in `1/m` together, as the truncations
  `PowerCounting.truncation` do.

A coefficient assignment `c` gives the effective-theory amplitude through total degree `n`,
`effectiveAmplitude n (M a) c ε = ∑_{o of total degree ≤ n} c o * M a o * ε ^ (total degree of o)`,
and `c` satisfies the matching condition `IsMatching` when, for every amplitude, the full and
effective amplitudes agree up to a remainder `O(ε ^ (n + 1))` as `ε → 0⁺`, that is when the
effective amplitude `ApproximatesToOrder` the full one to order `n + 1`. Matching through total
degree `n` implies matching through every lower total degree (`IsMatching.mono`).

Matching to this order constrains the coefficients one total degree at a time, through the
*matching matrix* `matchingMatrix M k`: its rows are the amplitudes, its columns the finitely many
operators of total degree exactly `k` (`PowerCounting.totalDegreePiece k`), and its entries the
velocity-stripped matrix elements; the set of amplitudes need not be finite. Given one matching
assignment `c`, another assignment `c'` matches if and only if, at every total degree `k ≤ n`, the
difference `c' - c` lies in the kernel of the matching matrix
(`IsMatching.iff_mulVec_sub_eq_zero`). Hence the matching coefficients of the operators
of a total degree `k ≤ n` are unique exactly when the matching matrix at total degree `k` has full
column rank, that is when no nonzero combination of the operators of total degree `k` has a
vanishing matrix element in every amplitude
(`IsMatching.eqOn_totalDegreePiece` and `IsMatching.forall_eqOn_totalDegreePiece_iff`), and they
are unique on the whole truncation exactly when this holds at every total degree `k ≤ n`
(`IsMatching.eqOn_truncation` and `IsMatching.forall_eqOn_truncation_iff`).

## Main definitions

* `PowerCounting.effectiveAmplitude`: the effective-theory amplitude through total degree `n`.
* `PowerCounting.IsMatching`: the matching condition through total degree `n`.
* `PowerCounting.matchingMatrix`: the matrix of velocity-stripped matrix elements at total
  degree `k`.

## Main results

* `PowerCounting.IsMatching.mono`: matching through total degree `n` implies matching through
  every total degree `m ≤ n`.
* `PowerCounting.isMatching_effectiveAmplitude`: every coefficient assignment matches the
  amplitudes it generates itself, so the matching condition is inhabited.
* `PowerCounting.forall_approximatesToOrder_effectiveAmplitude_iff`: two coefficient assignments
  give effective amplitudes agreeing to order `n + 1` exactly when their difference lies in the
  kernels of the matching matrices up to total degree `n`.
* `PowerCounting.IsMatching.iff_mulVec_sub_eq_zero`: on the truncation, the matching
  assignments are the translates of one of them by the kernels of the matching matrices.
* `PowerCounting.IsMatching.eqOn_totalDegreePiece`: **uniqueness** at one total degree — under
  the rank condition at that degree, two matching assignments agree on its operators.
* `PowerCounting.IsMatching.eqOn_truncation`: **uniqueness** — under the rank condition at every
  total degree, two matching assignments agree on the truncation.
* `PowerCounting.IsMatching.forall_eqOn_totalDegreePiece_iff`,
  `PowerCounting.IsMatching.forall_eqOn_truncation_iff`: the rank condition is also necessary for
  uniqueness, at each total degree and on the whole truncation.

## Implementation notes

The renormalisation scale and the coupling are held fixed: `F` and `M` are the amplitudes and
matrix elements at the stated order in the coupling and at one scale, and every statement applies
at each scale separately, so a scale-dependent assignment `c : FreeMonoid B → ℝ → ℝ` is unique
when each `c · μ` is. Existence of a matching assignment is not claimed in general; it is a
property of the full theory, not of this linear algebra, and the one existence fact proved here
is that every assignment matches the amplitudes it generates itself
(`isMatching_effectiveAmplitude`).

The full-theory amplitudes `F` and the velocity-stripped matrix elements `M` are given data: nothing
here derives them from QCD or NRQCD, and no dynamics, renormalisation or operator mixing is
modelled. The results are statements of linear algebra and real analysis about such data, and no
instance in which the rank condition holds is supplied here.

The rank condition is turned into injectivity of the matching matrices by
`Matrix.rank_eq_card_iff_mulVec_injective` of `TauCeti.LinearAlgebra.Matrix.Rank`, and the
coefficients are read off degree by degree with `Asymptotics.isBigO_sum_range_pow_smul_pow_succ_iff`
of `EpsilonEridani.Mathematics.Analysis.Asymptotics.TruncatedExpansion`.

## References

* G. T. Bodwin, E. Braaten and G. P. Lepage, *Rigorous QCD analysis of inclusive annihilation and
  production of heavy quarkonium*, Phys. Rev. D 51 (1995) 1125, Section II.
* N. Brambilla, A. Pineda, J. Soto and A. Vairo, *Effective field theories for heavy quarkonium*,
  Rev. Mod. Phys. 77 (2005) 1423, Section III.
-/

public section

open Filter Finset Topology Asymptotics

namespace EpsilonEridani.QFT.Quarkonium

namespace PowerCounting

variable {A B : Type*} (P : PowerCounting B)

/-! ### The effective-theory amplitude -/

/-- The effective-theory amplitude through total degree `n`, as a function of the power-counting
parameter `ε`: each operator `o` of the truncation contributes its coefficient `c o` times its
matrix element `M o * ε ^ k`, where `M o` is the velocity-stripped matrix element and `k` the total
degree of `o`. -/
noncomputable def effectiveAmplitude (n : ℕ) (M c : FreeMonoid B → ℝ) (ε : ℝ) : ℝ :=
  ∑ o ∈ P.truncation n, c o * M o * ε ^ totalDegree (compositeDeg P.deg o)

theorem effectiveAmplitude_def (n : ℕ) (M c : FreeMonoid B → ℝ) (ε : ℝ) :
    P.effectiveAmplitude n M c ε =
      ∑ o ∈ P.truncation n, c o * M o * ε ^ totalDegree (compositeDeg P.deg o) := (rfl)

/-- The effective-theory amplitude as a polynomial in the power-counting parameter: the
coefficient of `ε ^ k` collects the operators of total degree `k`. -/
theorem effectiveAmplitude_eq_sum_range (n : ℕ) (M c : FreeMonoid B → ℝ) (ε : ℝ) :
    P.effectiveAmplitude n M c ε =
      ∑ k ∈ range (n + 1), ε ^ k • ∑ o ∈ P.totalDegreePiece k, c o * M o := by
  rw [effectiveAmplitude_def, ← sum_fiberwise_of_maps_to
    (g := fun o => totalDegree (compositeDeg P.deg o)) (t := range (n + 1))
    fun o ho => by simpa [Nat.lt_succ_iff] using ho]
  refine sum_congr rfl fun k hk => ?_
  rw [smul_sum, P.filter_truncation_eq_totalDegreePiece (Nat.lt_succ_iff.1 (mem_range.1 hk))]
  refine sum_congr rfl fun o ho => ?_
  rw [(P.mem_totalDegreePiece).1 ho, smul_eq_mul, mul_comm]

/-- The effective-theory amplitude through total degree `n` depends only on the matrix elements
and the coefficients of the operators of the truncation. -/
theorem effectiveAmplitude_congr {n : ℕ} {M M' c c' : FreeMonoid B → ℝ}
    (hM : Set.EqOn M M' (P.truncation n)) (hc : Set.EqOn c c' (P.truncation n)) (ε : ℝ) :
    P.effectiveAmplitude n M c ε = P.effectiveAmplitude n M' c' ε := by
  simp only [effectiveAmplitude_def]
  exact sum_congr rfl fun o ho => by rw [hM ho, hc ho]

/-- Truncating the effective-theory amplitude from total degree `n` to a total degree `m ≤ n`
changes it by `O(ε ^ (m + 1))` as `ε → 0⁺`: the dropped operators all have total degree at
least `m + 1`. -/
theorem approximatesToOrder_effectiveAmplitude {m n : ℕ} (hmn : m ≤ n) (M c : FreeMonoid B → ℝ) :
    ApproximatesToOrder (P.effectiveAmplitude n M c) (P.effectiveAmplitude m M c) (m + 1) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  -- the difference is the sum of the terms of total degree `m + 1` through `m + d`
  have hdiff : ∀ ε, P.effectiveAmplitude (m + d) M c ε - P.effectiveAmplitude m M c ε =
      ∑ j ∈ range d, (∑ o ∈ P.totalDegreePiece (m + 1 + j), c o * M o) * ε ^ (m + 1 + j) :=
    fun ε => by
      simp only [effectiveAmplitude_eq_sum_range, add_right_comm m d 1, sum_range_add,
        add_sub_cancel_left, smul_eq_mul, mul_comm (ε ^ _)]
  refine approximatesToOrder_def.2 <|
    (IsBigO.fun_sum fun j _ => ?_).congr_left fun ε => (hdiff ε).symm
  exact ((isBigO_pow_pow (Nat.le_add_right (m + 1) j)).mono nhdsWithin_le_nhds).const_mul_left _

/-- The effective-theory amplitude is additive in the coefficient assignment. -/
theorem effectiveAmplitude_add_right (n : ℕ) (M c c' : FreeMonoid B → ℝ) (ε : ℝ) :
    P.effectiveAmplitude n M (c + c') ε =
      P.effectiveAmplitude n M c ε + P.effectiveAmplitude n M c' ε := by
  simp only [effectiveAmplitude_def, ← sum_add_distrib, Pi.add_apply, add_mul]

/-- The effective-theory amplitude commutes with differences of coefficient assignments. -/
theorem effectiveAmplitude_sub_right (n : ℕ) (M c c' : FreeMonoid B → ℝ) (ε : ℝ) :
    P.effectiveAmplitude n M (c - c') ε =
      P.effectiveAmplitude n M c ε - P.effectiveAmplitude n M c' ε := by
  simp only [effectiveAmplitude_def, ← sum_sub_distrib, Pi.sub_apply, sub_mul]

/-! ### The matching condition -/

/-- **The matching condition.** The coefficient assignment `c` matches the full-theory amplitudes
`F` through total degree `n` when, for every amplitude `a`, the full-theory amplitude `F a ε` and
the effective-theory amplitude built from the velocity-stripped matrix elements `M a` differ by
`O(ε ^ (n + 1))` as the power-counting parameter `ε` tends to `0⁺`. -/
def IsMatching (n : ℕ) (F : A → ℝ → ℝ) (M : A → FreeMonoid B → ℝ) (c : FreeMonoid B → ℝ) :
    Prop :=
  ∀ a, ApproximatesToOrder (F a) (P.effectiveAmplitude n (M a) c) (n + 1)

/-- Unfolding the matching condition. -/
theorem isMatching_def {n : ℕ} {F : A → ℝ → ℝ} {M : A → FreeMonoid B → ℝ}
    {c : FreeMonoid B → ℝ} :
    P.IsMatching n F M c ↔
      ∀ a, ApproximatesToOrder (F a) (P.effectiveAmplitude n (M a) c) (n + 1) :=
  Iff.rfl

/-- The matching condition through total degree `n` depends only on the matrix elements and the
coefficients of the operators of the truncation. -/
theorem isMatching_congr {n : ℕ} {F : A → ℝ → ℝ} {M M' : A → FreeMonoid B → ℝ}
    {c c' : FreeMonoid B → ℝ} (hM : ∀ a, Set.EqOn (M a) (M' a) (P.truncation n))
    (hc : Set.EqOn c c' (P.truncation n)) :
    P.IsMatching n F M c ↔ P.IsMatching n F M' c' :=
  forall_congr' fun a => by rw [funext (P.effectiveAmplitude_congr (hM a) hc)]

variable {P} in
/-- **Matching to a lower order.** An assignment matching the full-theory amplitudes through
total degree `n` matches them through every total degree `m ≤ n`. -/
theorem IsMatching.mono {n m : ℕ} {F : A → ℝ → ℝ} {M : A → FreeMonoid B → ℝ}
    {c : FreeMonoid B → ℝ} (h : P.IsMatching n F M c) (hmn : m ≤ n) : P.IsMatching m F M c :=
  fun a =>
    ((h a).mono (Nat.succ_le_succ hmn)).trans (P.approximatesToOrder_effectiveAmplitude hmn _ _)

/-- Every coefficient assignment matches the amplitudes it generates itself. -/
theorem isMatching_effectiveAmplitude (n : ℕ) (M : A → FreeMonoid B → ℝ)
    (c : FreeMonoid B → ℝ) :
    P.IsMatching n (fun a => P.effectiveAmplitude n (M a) c) M c := fun _ =>
  ApproximatesToOrder.refl _ _

/-! ### The matching matrix -/

/-- The matching matrix at total degree `k`: its rows are the amplitudes, its columns the
operators of total degree `k`, and its entry at `(a, o)` the velocity-stripped matrix element
`M a o`. -/
def matchingMatrix (M : A → FreeMonoid B → ℝ) (k : ℕ) : Matrix A (P.totalDegreePiece k) ℝ :=
  Matrix.of fun a o => M a o

@[simp]
theorem matchingMatrix_apply (M : A → FreeMonoid B → ℝ) (k : ℕ) (a : A)
    (o : P.totalDegreePiece k) : P.matchingMatrix M k a o = M a o := (rfl)

/-- Applying the matching matrix at total degree `k` to a vector `v` of coefficients of the
operators of total degree `k` gives, for each amplitude `a`, the sum of `M a o * v o` over those
operators. -/
theorem matchingMatrix_mulVec_apply (M : A → FreeMonoid B → ℝ) (k : ℕ)
    (v : P.totalDegreePiece k → ℝ) (a : A) :
    (P.matchingMatrix M k).mulVec v a = ∑ o : P.totalDegreePiece k, M a o * v o := by
  simp only [Matrix.mulVec_apply_eq_sum, matchingMatrix_apply]

/-- The effective-theory amplitude as a polynomial in the power-counting parameter whose
coefficient of `ε ^ k` is the matching matrix at total degree `k` applied to the coefficient
assignment. -/
theorem effectiveAmplitude_eq_sum_range_mulVec (n : ℕ) (M : A → FreeMonoid B → ℝ)
    (c : FreeMonoid B → ℝ) (a : A) (ε : ℝ) :
    P.effectiveAmplitude n (M a) c ε =
      ∑ k ∈ range (n + 1), ε ^ k • (P.matchingMatrix M k).mulVec (fun o => c o) a := by
  rw [effectiveAmplitude_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [matchingMatrix_mulVec_apply, ← sum_coe_sort (P.totalDegreePiece k)]
  simp only [mul_comm]

/-! ### Uniqueness -/

variable {P} {n : ℕ} {F : A → ℝ → ℝ} {M : A → FreeMonoid B → ℝ} {c c' : FreeMonoid B → ℝ}

/-- Two coefficient assignments give effective-theory amplitudes agreeing to order `n + 1` in
every amplitude exactly when, at every total degree `k ≤ n`, their difference lies in the kernel
of the matching matrix. -/
theorem forall_approximatesToOrder_effectiveAmplitude_iff :
    (∀ a, ApproximatesToOrder (P.effectiveAmplitude n (M a) c) (P.effectiveAmplitude n (M a) c')
        (n + 1)) ↔
      ∀ k ≤ n, (P.matchingMatrix M k).mulVec (fun o => c' o - c o) = 0 := by
  have hl : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] 0 := nhdsGT_le_nhdsNE 0
  -- the difference of the effective amplitudes, as a polynomial with the matching-matrix
  -- coefficients
  have hdiff : ∀ a ε, P.effectiveAmplitude n (M a) c' ε - P.effectiveAmplitude n (M a) c ε =
      ∑ k ∈ range (n + 1), ε ^ k • (P.matchingMatrix M k).mulVec (fun o => c' o - c o) a :=
    fun a ε => by
      rw [← effectiveAmplitude_sub_right, effectiveAmplitude_eq_sum_range_mulVec]
      simp only [Pi.sub_apply]
  constructor
  · intro happ k hk
    funext a
    rw [Pi.zero_apply]
    refine (isBigO_sum_range_pow_smul_pow_succ_iff hl
      (a := fun k => (P.matchingMatrix M k).mulVec (fun o => c' o - c o) a)).1 ?_ k hk
    exact (approximatesToOrder_def.1 (happ a).symm).congr_left (hdiff a)
  · intro h a
    refine (ApproximatesToOrder.refl (P.effectiveAmplitude n (M a) c) _).congr_sub fun ε => ?_
    rw [sub_self, eq_comm, ← neg_sub, neg_eq_zero, hdiff]
    exact sum_eq_zero fun k hk => by
      rw [h k (Nat.lt_succ_iff.1 (mem_range.1 hk)), Pi.zero_apply, smul_zero]

/-- **The space of matching coefficients.** Given one assignment `c` matching through total
degree `n`, an assignment `c'` matches as well exactly when, at every total degree `k ≤ n`, the
difference `c' - c` lies in the kernel of the matching matrix. -/
theorem IsMatching.iff_mulVec_sub_eq_zero (hc : P.IsMatching n F M c) :
    P.IsMatching n F M c' ↔
      ∀ k ≤ n, (P.matchingMatrix M k).mulVec (fun o => c' o - c o) = 0 :=
  ⟨fun hc' => forall_approximatesToOrder_effectiveAmplitude_iff.1 fun a =>
      (hc a).symm.trans (hc' a),
    fun h a => (hc a).trans (forall_approximatesToOrder_effectiveAmplitude_iff.2 h a)⟩

/-- **Uniqueness of the matching coefficients at one total degree.** If the matching matrix at a
total degree `k ≤ n` has full column rank — no nonzero combination of the operators of total
degree `k` has a vanishing matrix element in every amplitude — then two coefficient assignments
matching the same amplitudes through total degree `n`
agree on every operator of total degree `k`. -/
theorem IsMatching.eqOn_totalDegreePiece (hc : P.IsMatching n F M c)
    (hc' : P.IsMatching n F M c') {k : ℕ} (hk : k ≤ n)
    (hrank : (P.matchingMatrix M k).rank = (P.totalDegreePiece k).card) :
    Set.EqOn c c' (P.totalDegreePiece k) := fun o ho => by
  have hinj := (Matrix.rank_eq_card_iff_mulVec_injective (P.matchingMatrix M k)).1
    (by simpa only [Fintype.card_coe] using hrank)
  have h0 : (fun o : P.totalDegreePiece k => c' o - c o) = 0 :=
    hinj <| by rw [(hc.iff_mulVec_sub_eq_zero).1 hc' k hk, Matrix.mulVec_zero]
  exact (sub_eq_zero.1 (congrFun h0 ⟨o, ho⟩)).symm

/-- **Uniqueness of the matching coefficients.** If at every total degree `k ≤ n` the matching
matrix has full column rank, then two coefficient assignments matching the same amplitudes through
total degree `n` agree on every operator of the truncation. -/
theorem IsMatching.eqOn_truncation (hc : P.IsMatching n F M c) (hc' : P.IsMatching n F M c')
    (hrank : ∀ k ≤ n, (P.matchingMatrix M k).rank = (P.totalDegreePiece k).card) :
    Set.EqOn c c' (P.truncation n) := fun _ ho =>
  hc.eqOn_totalDegreePiece hc' (P.mem_truncation.1 ho) (hrank _ (P.mem_truncation.1 ho))
    ((P.mem_totalDegreePiece).2 rfl)

/-- **The rank condition at one total degree is necessary and sufficient.** Given one assignment
matching through total degree `n` and a total degree `k ≤ n`, every matching assignment agrees with
it on the operators of total degree `k` exactly when the matching matrix at total degree `k` has
full column rank. -/
theorem IsMatching.forall_eqOn_totalDegreePiece_iff (hc : P.IsMatching n F M c) {k : ℕ}
    (hk : k ≤ n) :
    (∀ c', P.IsMatching n F M c' → Set.EqOn c c' (P.totalDegreePiece k)) ↔
      (P.matchingMatrix M k).rank = (P.totalDegreePiece k).card := by
  refine ⟨fun huniq => ?_, fun hrank c' hc' => hc.eqOn_totalDegreePiece hc' hk hrank⟩
  classical
  by_contra hrank
  rw [← Fintype.card_coe] at hrank
  -- a nonzero kernel vector `d` of the matching matrix at total degree `k`
  obtain ⟨d₁, d₂, hd, hne⟩ :=
    Function.not_injective_iff.1 (mt (Matrix.rank_eq_card_iff_mulVec_injective _).2 hrank)
  set d := d₁ - d₂ with hd_def
  obtain ⟨o, ho⟩ : ∃ o, d o ≠ 0 := by
    by_contra! h
    exact hne (sub_eq_zero.1 (funext h))
  -- shifting `c` by `d` on the operators of total degree `k` keeps the matching condition
  set c' : FreeMonoid B → ℝ := fun o => c o + if h : o ∈ P.totalDegreePiece k then d ⟨o, h⟩ else 0
  have hc' : P.IsMatching n F M c' := by
    refine (hc.iff_mulVec_sub_eq_zero).2 fun j _ => ?_
    by_cases hjk : j = k
    · subst hjk
      have : (fun o : P.totalDegreePiece j => c' o - c o) = d := funext fun o => by
        simp only [c', o.2, ↓reduceDIte, Subtype.coe_eta, add_sub_cancel_left]
      rw [this, hd_def, Matrix.mulVec_sub, hd, sub_self]
    · have : (fun o : P.totalDegreePiece j => c' o - c o) = 0 := funext fun o => by
        have : (o : FreeMonoid B) ∉ P.totalDegreePiece k := fun h =>
          hjk (((P.mem_totalDegreePiece).1 o.2).symm.trans ((P.mem_totalDegreePiece).1 h))
        simp only [c', this, ↓reduceDIte, add_zero, sub_self, Pi.zero_apply]
      rw [this, Matrix.mulVec_zero]
  have := huniq c' hc' o.2
  simp only [c', o.2, ↓reduceDIte, Subtype.coe_eta] at this
  exact ho (by linarith)

/-- **The rank condition is necessary and sufficient.** Given one assignment matching through
total degree `n`, every matching assignment agrees with it on the truncation exactly when the
matching matrix has full column rank at every total degree `k ≤ n`. -/
theorem IsMatching.forall_eqOn_truncation_iff (hc : P.IsMatching n F M c) :
    (∀ c', P.IsMatching n F M c' → Set.EqOn c c' (P.truncation n)) ↔
      ∀ k ≤ n, (P.matchingMatrix M k).rank = (P.totalDegreePiece k).card :=
  ⟨fun huniq _ hk => (hc.forall_eqOn_totalDegreePiece_iff hk).1 fun c' hc' =>
      (huniq c' hc').mono (Finset.coe_subset.2 (P.totalDegreePiece_subset_truncation hk)),
    fun hrank _ hc' => hc.eqOn_truncation hc' hrank⟩

end PowerCounting

end EpsilonEridani.QFT.Quarkonium
