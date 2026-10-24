/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import EpsilonEridani.Mathematics.MeasureTheory.StrictMono

/-!
# The ordered iterated integral of a product

For `f : ℝ → ℝ` and endpoints `t`, `T`, the `n`-fold integral of `f t₁ * ⋯ * f tₙ` over the
descending region `T > t₁ > ⋯ > tₙ > t` equals `(∫ s in t..T, f s) ^ n / n !`.

`orderedProdIntegral f T n t` is that region integral, written as an *iterated* interval
integral with the **smallest** variable outermost:

  `orderedProdIntegral f T 0       t = 1`
  `orderedProdIntegral f T (n + 1) t = ∫ x in t..T, f x * orderedProdIntegral f T n x`

Fixing the smallest coordinate at `x` leaves the remaining `n` coordinates ranging over the
same ordered region with lower endpoint `x`, which is exactly this recursion.  The main
result is `orderedProdIntegral_eq`.

## The proof, and why not symmetrization

The textbook argument is a symmetrization: the integrand is symmetric, the `n !` orderings
of the coordinates tile the cube `[t, T] ^ n` up to a measure-zero diagonal, so the ordered
region carries `1 / n !` of the cube integral.  That is correct, but as a formalization
target it needs almost-disjointness of `n !` permuted simplices, that they cover, and a
measure-preserving change of variables under each permutation — a composite that does not
exist ready-made in `Mathlib` at the pinned revision.

The route taken here is induction on `n` with the fundamental theorem of calculus, and it
needs none of that.  Write `F x = ∫ s in x..T, f s`.  Integrating out the smallest variable
turns the inductive hypothesis into `∫ x in t..T, f x * F x ^ n / n !`; since `F` is the
integral *up to* `T` its derivative is `-f`, so `x ↦ -F x ^ (n + 1) / (n + 1)` is an
antiderivative of `x ↦ f x * F x ^ n`, and FTC-2 collapses the integral to
`F t ^ (n + 1) / (n + 1)` because `F T = 0`.  Only `intervalIntegral`, the FTC pair and the
chain rule for `x ↦ F x ^ n` are used; there is no measure theory on the simplex, no
permutation argument and no almost-everywhere reasoning.

The iterated form is also the one an application usually wants, since a sequential sampler
of the ordered coordinates produces precisely this nesting.

## The ordered region and the Fubini identification

The second half of the file identifies the iterated integral with a Lebesgue integral on
`ℝ ^ n`.  `orderedRegion T n t` is the subset `{p : Fin n → ℝ | t < p 0 < ⋯ < p (n - 1) < T}`
of `Fin n → ℝ`, with its smallest coordinate first.

* `setIntegral_orderedRegion_succ`: for an integrand `g` integrable on the region, splitting
  off the smallest coordinate `p 0` (a volume-preserving `Fin.cons` decomposition followed by
  Fubini) turns the integral over the `(n + 1)`-coordinate region into the integral over
  `x ∈ (t, T)` of the integral of `q ↦ g (Fin.cons x q)` over the `n`-coordinate region with
  lower endpoint `x`;
* `setIntegral_orderedRegion_eq_orderedProdIntegral`: hence, by induction, for continuous `f`
  and `t ≤ T`, `∫ p in orderedRegion T n t, ∏ i, f (p i) = orderedProdIntegral f T n t`;
* `setIntegral_orderedRegion_eq_pow_div_factorial` and `volume_orderedRegion`: combined with
  `orderedProdIntegral_eq`, for continuous `f` and `t ≤ T` the region integral is
  `(∫ s in t..T, f s) ^ n / n !`, and the region has volume `(T - t) ^ n / n !` for every
  `t` and `T`;
* `preimage_comp_rev_orderedRegion` with its `volume_` and `setIntegral_` companions: the
  same region with its largest coordinate first — the descending region
  `{p | StrictAnti p ∧ ∀ i, p i ∈ (t, T)}` in which ordered tuples are usually labelled — is
  the preimage of `orderedRegion` under the measure-preserving coordinate reversal
  `p ↦ p ∘ Fin.rev`, so its volume and integrals reduce to the ascending ones.

The same induction again avoids the symmetrization argument: no permuted copies of the region
appear, only the measurable set itself and Fubini on `ℝ × ℝ ^ n`.

## Scope

Stated for `f : ℝ → ℝ` under `Continuous f`.  Continuity is used for the derivative of the
primitive, for interval integrability of the integrand at each stage, and for integrability of
the product integrand on the bounded ordered region.  It could be relaxed towards
`IntervalIntegrable` at the cost of carrying integrability hypotheses through the induction;
that is not attempted here.

The identification theorems `setIntegral_orderedRegion_eq_orderedProdIntegral` and
`setIntegral_orderedRegion_eq_pow_div_factorial` additionally require `t ≤ T`: for `T < t`
and `n ≥ 1` the region is empty, while `orderedProdIntegral` is a signed iterated integral
and need not vanish.  The slicing, measurability, integrability and volume statements carry
no such hypothesis; `volume_orderedRegion` covers the empty regime as well, both sides
vanishing there.

Nothing in this file is physics-specific: it is mathlib-shaped and upstreamable, and is kept
here only so that downstream files can use it now.  Upstreaming is handled separately, as
for this repository's su(N) material.
-/

@[expose] public section

namespace EpsilonEridani
namespace OrderedSimplex

open scoped Nat
open MeasureTheory intervalIntegral

/-- The integral of `f t₁ * ⋯ * f tₙ` over the descending region `T > t₁ > ⋯ > tₙ > t`,
written as an iterated interval integral with the smallest coordinate outermost.  The empty
product integrates to `1`. -/
noncomputable def orderedProdIntegral (f : ℝ → ℝ) (T : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t => ∫ x in t..T, f x * orderedProdIntegral f T n x

variable {f : ℝ → ℝ}

/-- The zero-fold ordered integral is the empty product. -/
@[simp]
lemma orderedProdIntegral_zero (f : ℝ → ℝ) (T t : ℝ) : orderedProdIntegral f T 0 t = 1 := by
  simp only [orderedProdIntegral]

/-- Peeling off the smallest coordinate: fixing it at `x` leaves the ordered integral of one
fewer coordinate over the region with lower endpoint `x`. -/
lemma orderedProdIntegral_succ (f : ℝ → ℝ) (T : ℝ) (n : ℕ) (t : ℝ) :
    orderedProdIntegral f T (n + 1) t = ∫ x in t..T, f x * orderedProdIntegral f T n x := by
  simp only [orderedProdIntegral]

/-- The primitive `u ↦ ∫ s in u..T, f s` of a continuous `f`, differentiated in its *lower*
limit: the derivative is `-f`, which is what makes the induction below telescope. -/
lemma hasDerivAt_integral_lower (hf : Continuous f) (T x : ℝ) :
    HasDerivAt (fun u => ∫ s in u..T, f s) (-f x) x :=
  integral_hasDerivAt_left (hf.intervalIntegrable _ _)
    (hf.stronglyMeasurableAtFilter _ _) hf.continuousAt

/-- The primitive of a continuous function, as a function of its lower limit, is continuous.
This is what makes each stage of the induction interval integrable. -/
lemma continuous_integral_lower (hf : Continuous f) (T : ℝ) :
    Continuous fun u => ∫ s in u..T, f s :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_integral_lower hf T x).continuousAt

/-- The inductive step, by FTC-2: `x ↦ -(∫ s in x..T, f s) ^ (n + 1) / (n + 1)` is an
antiderivative of `x ↦ f x * (∫ s in x..T, f s) ^ n`, and it vanishes at `T`. -/
lemma integral_mul_integral_pow (hf : Continuous f) (T t : ℝ) (n : ℕ) :
    (∫ x in t..T, f x * (∫ s in x..T, f s) ^ n) = (∫ s in t..T, f s) ^ (n + 1) / (n + 1) := by
  have hne : (-((n : ℝ) + 1)) ≠ 0 := neg_ne_zero.mpr (by positivity)
  have key : ∀ x : ℝ, HasDerivAt
      (fun u : ℝ => (∫ s in u..T, f s) ^ (n + 1) / (-((n : ℝ) + 1)))
      (f x * (∫ s in x..T, f s) ^ n) x := by
    intro x
    have hp : HasDerivAt (fun u : ℝ => (∫ s in u..T, f s) ^ (n + 1))
        (((n + 1 : ℕ) : ℝ) * (∫ s in x..T, f s) ^ (n + 1 - 1) * -f x) x :=
      (hasDerivAt_integral_lower hf T x).fun_pow (n + 1)
    have h := hp.div_const (-((n : ℝ) + 1))
    have heq : ((n + 1 : ℕ) : ℝ) * (∫ s in x..T, f s) ^ (n + 1 - 1) * -f x / (-((n : ℝ) + 1))
        = f x * (∫ s in x..T, f s) ^ n := by
      rw [div_eq_iff hne]
      simp only [Nat.add_sub_cancel]
      push_cast
      ring
    rw [heq] at h
    exact h
  have hint : IntervalIntegrable (fun x : ℝ => f x * (∫ s in x..T, f s) ^ n) volume t T :=
    (hf.mul ((continuous_integral_lower hf T).pow n)).intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => key x) hint]
  simp only [integral_same, zero_pow n.succ_ne_zero, zero_div, div_neg, neg_zero, zero_sub,
    neg_neg]

/-- **The ordered-simplex identity.** The `n`-fold integral of `f t₁ * ⋯ * f tₙ` over the
descending region `T > t₁ > ⋯ > tₙ > t` is `1 / n !` times the `n`-th power of the single
integral `∫ s in t..T, f s`.

No inequality between `t` and `T` is required: `intervalIntegral` is signed, and both sides
change sign together when the endpoints are swapped. -/
lemma orderedProdIntegral_eq (hf : Continuous f) (T : ℝ) (n : ℕ) (t : ℝ) :
    orderedProdIntegral f T n t = (∫ s in t..T, f s) ^ n / n ! := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
    rw [orderedProdIntegral_succ]
    have hrw : ∀ x : ℝ,
        f x * orderedProdIntegral f T n x = f x * (∫ s in x..T, f s) ^ n / (n ! : ℝ) := by
      intro x
      rw [ih x]
      ring
    simp_rw [hrw]
    rw [intervalIntegral.integral_div, integral_mul_integral_pow hf, Nat.factorial_succ,
      div_div]
    push_cast
    ring

/-! ### The ordered region and the Fubini identification -/

/-- The ordered region `t < p 0 < p 1 < ⋯ < p (n - 1) < T` of `ℝ ^ n`, as a subset of
`Fin n → ℝ`.  Its smallest coordinate `p 0` is the one `orderedProdIntegral f T n t`
integrates outermost; for `n = 0` it is the whole (one-point) space. -/
def orderedRegion (T : ℝ) (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  {p | StrictMono p ∧ ∀ i, p i ∈ Set.Ioo t T}

/-- Membership in the ordered region: strictly increasing coordinates, all in `(t, T)`. -/
@[simp]
lemma mem_orderedRegion {T t : ℝ} {n : ℕ} {p : Fin n → ℝ} :
    p ∈ orderedRegion T n t ↔ StrictMono p ∧ ∀ i, p i ∈ Set.Ioo t T :=
  Iff.rfl

/-- With no coordinates, the ordered region is the whole (one-point) space. -/
@[simp]
lemma orderedRegion_zero (T t : ℝ) : orderedRegion T 0 t = Set.univ :=
  Set.eq_univ_of_forall fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- For `T ≤ t`, the ordered region with at least one coordinate is empty: every coordinate
would have to lie in the empty interval `(t, T)`.  The regime excluded by the `t ≤ T`
hypothesis of the identification theorems is thus the strict inequality `T < t`; at `T = t`
the region is empty as well, but those theorems still apply. -/
@[simp]
lemma orderedRegion_eq_empty {T t : ℝ} (h : T ≤ t) (n : ℕ) :
    orderedRegion T (n + 1) t = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro p hp
  exact absurd ((hp.2 0).1.trans (hp.2 0).2) (not_lt.mpr h)

/-- Peeling off the smallest coordinate: `Fin.cons x q` lies in the ordered region with
`n + 1` coordinates exactly when `x ∈ (t, T)` and `q` lies in the ordered region with lower
endpoint `x`.  This is the set-level form of `orderedProdIntegral_succ`. -/
lemma cons_mem_orderedRegion_iff {T t x : ℝ} {n : ℕ} {q : Fin n → ℝ} :
    (Fin.cons x q : Fin (n + 1) → ℝ) ∈ orderedRegion T (n + 1) t ↔
      x ∈ Set.Ioo t T ∧ q ∈ orderedRegion T n x := by
  simp only [mem_orderedRegion, Fin.strictMono_cons, Fin.forall_fin_succ, Fin.cons_zero,
    Fin.cons_succ, Set.mem_Ioo]
  constructor
  · rintro ⟨⟨hxq, hq⟩, ⟨htx, hxT⟩, hqi⟩
    exact ⟨⟨htx, hxT⟩, hq, fun i => ⟨hxq i, (hqi i).2⟩⟩
  · rintro ⟨⟨htx, hxT⟩, hq, hqi⟩
    exact ⟨⟨fun i => (hqi i).1, hq⟩, ⟨htx, hxT⟩, fun i => ⟨htx.trans (hqi i).1, (hqi i).2⟩⟩

/-- The ordered region is a measurable subset of `Fin n → ℝ`. -/
@[simp, measurability]
lemma measurableSet_orderedRegion (T : ℝ) (n : ℕ) (t : ℝ) :
    MeasurableSet (orderedRegion T n t) :=
  measurableSet_strictMono.inter (MeasurableSet.univ_pi' fun _ => measurableSet_Ioo)

/-- The ordered region sits inside the cube `[t, T] ^ n`. -/
lemma orderedRegion_subset_Icc (T : ℝ) (n : ℕ) (t : ℝ) :
    orderedRegion T n t ⊆ Set.Icc (fun _ => t) (fun _ => T) :=
  fun _ hp => ⟨fun i => (hp.2 i).1.le, fun i => (hp.2 i).2.le⟩

/-- A function continuous on the cube `[t, T] ^ n` is integrable on the ordered region: the
region is a measurable subset of that compact cube. -/
lemma integrableOn_orderedRegion {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {g : (Fin n → ℝ) → E} {T t : ℝ}
    (hg : ContinuousOn g (Set.Icc (fun _ => t) (fun _ => T))) :
    IntegrableOn g (orderedRegion T n t) :=
  (hg.integrableOn_compact isCompact_Icc).mono_set (orderedRegion_subset_Icc T n t)

/-- For continuous `f`, the integrand `p ↦ f (p 0) * ⋯ * f (p (n - 1))` is integrable on the
ordered region, which is bounded. -/
lemma integrableOn_orderedRegion_prod (hf : Continuous f) (T : ℝ) (n : ℕ) (t : ℝ) :
    IntegrableOn (fun p : Fin n → ℝ => ∏ i, f (p i)) (orderedRegion T n t) :=
  integrableOn_orderedRegion
    (continuous_finsetProd _ fun i _ => hf.comp (continuous_apply i)).continuousOn

/-- **Fubini on the ordered region.** The integral of an integrand `g`, with values in a
normed space over `ℝ`, over the `(n + 1)`-coordinate ordered region equals the integral over
`x ∈ (t, T)` of the integral of `q ↦ g (Fin.cons x q)` over the `n`-coordinate ordered region
with lower endpoint `x`: splitting off the smallest coordinate `p 0`, a volume-preserving
`Fin.cons` decomposition followed by Fubini, leaves exactly that nested integral.  This is
the measure-theoretic counterpart of `orderedProdIntegral_succ`.  The integrability
hypothesis holds for any integrand continuous on the cube `[t, T] ^ (n + 1)`, by
`integrableOn_orderedRegion`; for the product integrand of a continuous `f` it is
`integrableOn_orderedRegion_prod`. -/
theorem setIntegral_orderedRegion_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ} {n : ℕ} {t : ℝ} {g : (Fin (n + 1) → ℝ) → E}
    (hg : IntegrableOn g (orderedRegion T (n + 1) t)) :
    ∫ p in orderedRegion T (n + 1) t, g p =
      ∫ x in Set.Ioo t T, ∫ q in orderedRegion T n x, g (Fin.cons x q) := by
  -- `e.symm (x, q) = Fin.cons x q` splits off the smallest coordinate and preserves volume.
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have he : MeasurePreserving e.symm (volume.prod volume) volume :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have he_apply (z : ℝ × (Fin n → ℝ)) : e.symm z = Fin.cons z.1 z.2 := by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  set S := e.symm ⁻¹' orderedRegion T (n + 1) t
  have hS : MeasurableSet S :=
    (measurableSet_orderedRegion T (n + 1) t).preimage e.symm.measurable
  have hmemS (x : ℝ) (q : Fin n → ℝ) :
      (x, q) ∈ S ↔ x ∈ Set.Ioo t T ∧ q ∈ orderedRegion T n x := by
    simp only [S, Set.mem_preimage, he_apply, cons_mem_orderedRegion_iff]
  set h : ℝ × (Fin n → ℝ) → E := fun z => g (Fin.cons z.1 z.2)
  have hh (z : ℝ × (Fin n → ℝ)) : g (e.symm z) = h z := by
    simp [h, he_apply]
  have hint : Integrable (S.indicator h) (volume.prod volume) := by
    rw [← he.integrableOn_comp_preimage e.symm.measurableEmbedding] at hg
    rw [integrable_indicator_iff hS]
    exact hg.congr_fun (fun z _ => hh z) hS
  -- At fixed `x`, the slice of `S` is the ordered region with lower endpoint `x`, or empty.
  have hslice (x : ℝ) : ∫ q, S.indicator h (x, q) =
      (Set.Ioo t T).indicator (fun x => ∫ q in orderedRegion T n x, g (Fin.cons x q)) x := by
    by_cases hx : x ∈ Set.Ioo t T
    · have hpt : (fun q => S.indicator h (x, q)) =
          (orderedRegion T n x).indicator (fun q => g (Fin.cons x q)) := by
        ext q
        by_cases hq : q ∈ orderedRegion T n x
        · rw [Set.indicator_of_mem ((hmemS x q).2 ⟨hx, hq⟩), Set.indicator_of_mem hq]
        · rw [Set.indicator_of_notMem (fun h => hq ((hmemS x q).1 h).2),
            Set.indicator_of_notMem hq]
      rw [hpt, MeasureTheory.integral_indicator (measurableSet_orderedRegion T n x),
        Set.indicator_of_mem hx]
    · have hpt : (fun q => S.indicator h (x, q)) = fun _ => 0 := by
        ext q
        simp [hmemS, hx]
      rw [hpt, MeasureTheory.integral_zero, Set.indicator_of_notMem hx]
  calc ∫ p in orderedRegion T (n + 1) t, g p
      = ∫ z in S, h z ∂(volume.prod volume) := by
        rw [← he.setIntegral_preimage_emb e.symm.measurableEmbedding]
        exact setIntegral_congr_fun hS fun z _ => hh z
    _ = ∫ x, ∫ q, S.indicator h (x, q) := by
        rw [← MeasureTheory.integral_indicator hS, integral_prod _ hint]
    _ = ∫ x in Set.Ioo t T, ∫ q in orderedRegion T n x, g (Fin.cons x q) := by
        simp_rw [hslice, MeasureTheory.integral_indicator measurableSet_Ioo]

/-- **The Fubini identification.** For continuous `f` and `t ≤ T`, the Lebesgue integral of
`f (p 0) * ⋯ * f (p (n - 1))` over the ordered region `t < p 0 < ⋯ < p (n - 1) < T` of `ℝ ^ n`
is the iterated integral `orderedProdIntegral f T n t`. -/
theorem setIntegral_orderedRegion_eq_orderedProdIntegral (hf : Continuous f) (n : ℕ) {t T : ℝ}
    (htT : t ≤ T) :
    ∫ p in orderedRegion T n t, ∏ i, f (p i) = orderedProdIntegral f T n t := by
  induction n generalizing t with
  | zero => simp [measureReal_def, volume_pi]
  | succ n ih =>
    rw [setIntegral_orderedRegion_succ (integrableOn_orderedRegion_prod hf T (n + 1) t),
      orderedProdIntegral_succ,
      intervalIntegral.integral_of_le htT, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    rw [MeasureTheory.integral_const_mul, ih hx.2.le]

/-- For continuous `f` and `t ≤ T`, the integral of `f (p 0) * ⋯ * f (p (n - 1))` over the
ordered region of `ℝ ^ n` is `(∫ s in t..T, f s) ^ n / n !`. -/
theorem setIntegral_orderedRegion_eq_pow_div_factorial (hf : Continuous f) (n : ℕ) {t T : ℝ}
    (htT : t ≤ T) :
    ∫ p in orderedRegion T n t, ∏ i, f (p i) = (∫ s in t..T, f s) ^ n / n ! := by
  rw [setIntegral_orderedRegion_eq_orderedProdIntegral hf n htT, orderedProdIntegral_eq hf]

/-- The Lebesgue measure of the ordered region `t < p 0 < ⋯ < p (n - 1) < T` is
`(T - t) ^ n / n !`, with `T - t` read through `ENNReal.ofReal`.  No inequality between `t`
and `T` is needed: for `T < t` and `n ≥ 1` the region is empty and `ENNReal.ofReal (T - t) = 0`
agrees with that, while for `n = 0` both sides are `1`. -/
theorem volume_orderedRegion (n : ℕ) (t T : ℝ) :
    volume (orderedRegion T n t) = ENNReal.ofReal (T - t) ^ n / (n ! : ENNReal) := by
  rcases n with _ | m
  · rw [orderedRegion_zero, volume_pi]
    simp
  · by_cases htT : t ≤ T
    · have hfin : volume (orderedRegion T (m + 1) t) ≠ ⊤ :=
        (measure_mono (orderedRegion_subset_Icc T (m + 1) t)).trans_lt
          isCompact_Icc.measure_lt_top |>.ne
      have h := setIntegral_orderedRegion_eq_pow_div_factorial continuous_const (m + 1) htT (f := 1)
      simp only [Pi.one_apply, Finset.prod_const_one, setIntegral_const, smul_eq_mul, mul_one,
        intervalIntegral.integral_const] at h
      rw [← ofReal_measureReal hfin, h, ENNReal.ofReal_div_of_pos (by positivity),
        ENNReal.ofReal_pow (sub_nonneg.2 htT), ENNReal.ofReal_natCast]
    · have hTt : T ≤ t := le_of_lt (not_le.mp htT)
      rw [orderedRegion_eq_empty hTt, measure_empty,
        ENNReal.ofReal_eq_zero.mpr (sub_nonpos.mpr hTt), zero_pow (by omega), ENNReal.zero_div]

/-! ### The descending region -/

/-- Reversing coordinates preserves volume: `p ↦ p ∘ Fin.rev` is the coordinate permutation
that `Fin.revPerm` induces on `Fin n → ℝ`, measure-preserving by
`volume_measurePreserving_piCongrLeft`. -/
lemma volume_preserving_comp_rev (n : ℕ) :
    MeasurePreserving (fun p : Fin n → ℝ => p ∘ Fin.rev) volume volume := by
  have hcoe : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) Fin.revPerm) =
      (fun p : Fin n → ℝ => p ∘ Fin.rev) := by
    funext p b
    have h2 : (Equiv.piCongrLeft (fun _ : Fin n => ℝ) Fin.revPerm) p
        (Fin.rev (Fin.rev b)) = p (Fin.rev b) :=
      Equiv.piCongrLeft_apply_apply (fun _ : Fin n => ℝ) Fin.revPerm p (Fin.rev b)
    rw [Fin.rev_rev] at h2
    exact h2
  rw [← hcoe]
  exact volume_measurePreserving_piCongrLeft _ _

/-- The ordered region read with its largest coordinate first: the preimage of
`orderedRegion T n t` under the coordinate reversal `p ↦ p ∘ Fin.rev` is the descending
region `{p | StrictAnti p ∧ ∀ i, p i ∈ (t, T)}`, the form in which ordered tuples are
usually labelled. -/
lemma preimage_comp_rev_orderedRegion (T : ℝ) (n : ℕ) (t : ℝ) :
    (fun p : Fin n → ℝ => p ∘ Fin.rev) ⁻¹' orderedRegion T n t =
      {p : Fin n → ℝ | StrictAnti p ∧ ∀ i, p i ∈ Set.Ioo t T} := by
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, mem_orderedRegion]
  constructor
  · rintro ⟨hmono, hrange⟩
    refine ⟨?_, fun i => ?_⟩
    · have hanti : StrictAnti ((p ∘ Fin.rev) ∘ Fin.rev) :=
        hmono.comp_strictAnti Fin.rev_strictAnti
      have hcomp : (p ∘ Fin.rev) ∘ Fin.rev = p := by funext i; simp
      rwa [hcomp] at hanti
    · have hi := hrange (Fin.rev i)
      rwa [Function.comp_apply, Fin.rev_rev] at hi
  · rintro ⟨hanti, hrange⟩
    exact ⟨hanti.comp Fin.rev_strictAnti, fun i => hrange (Fin.rev i)⟩

/-- The descending region has the same volume as the ordered region: coordinate reversal is
measure-preserving. -/
lemma volume_preimage_comp_rev_orderedRegion (T : ℝ) (n : ℕ) (t : ℝ) :
    volume ((fun p : Fin n → ℝ => p ∘ Fin.rev) ⁻¹' orderedRegion T n t) =
      volume (orderedRegion T n t) := by
  rw [← Measure.map_apply (volume_preserving_comp_rev n).measurable
      (measurableSet_orderedRegion T n t), MeasurePreserving.map_eq (volume_preserving_comp_rev n)]

/-- **The orientation bridge, integral form.** The integral of `g` over the descending region,
the preimage of the ordered region under coordinate reversal, equals the integral of
`g ∘ Fin.rev` over the ordered region: reversal is a measure-preserving change of variables
between the two readings of the region. -/
theorem setIntegral_preimage_comp_rev_orderedRegion {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} {g : (Fin n → ℝ) → E} {T t : ℝ} :
    ∫ p in (fun p : Fin n → ℝ => p ∘ Fin.rev) ⁻¹' orderedRegion T n t, g p =
      ∫ q in orderedRegion T n t, g (q ∘ Fin.rev) := by
  have hinv : ∀ p : Fin n → ℝ, (p ∘ Fin.rev) ∘ Fin.rev = p := fun p => by funext i; simp
  have hme : MeasurableEmbedding (fun p : Fin n → ℝ => p ∘ Fin.rev) := by
    refine MeasurableEmbedding.of_measurable_inverse
      (volume_preserving_comp_rev n).measurable ?_ (volume_preserving_comp_rev n).measurable hinv
    have hsurj : Function.Surjective (fun p : Fin n → ℝ => p ∘ Fin.rev) :=
      fun b => ⟨b ∘ Fin.rev, hinv b⟩
    rw [Set.range_eq_univ.mpr hsurj]
    exact MeasurableSet.univ
  have key := (volume_preserving_comp_rev n).setIntegral_preimage_emb hme
    (fun q : Fin n → ℝ => g (q ∘ Fin.rev)) (orderedRegion T n t)
  calc ∫ p in (fun p : Fin n → ℝ => p ∘ Fin.rev) ⁻¹' orderedRegion T n t, g p
      = ∫ p in (fun p : Fin n → ℝ => p ∘ Fin.rev) ⁻¹' orderedRegion T n t,
          g ((p ∘ Fin.rev) ∘ Fin.rev) :=
        setIntegral_congr_fun
          ((measurableSet_orderedRegion T n t).preimage (volume_preserving_comp_rev n).measurable)
          fun p _ => (congrArg g (hinv p)).symm
    _ = ∫ q in orderedRegion T n t, g (q ∘ Fin.rev) := key

end OrderedSimplex
end EpsilonEridani
