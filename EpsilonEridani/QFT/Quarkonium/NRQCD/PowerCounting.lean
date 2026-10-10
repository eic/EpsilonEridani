/-
Copyright (c) 2026 The EpsilonEridani contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The EpsilonEridani contributors
-/
module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Set.Finite.List

/-!
# Velocity power counting and the finiteness of each graded piece

Non-relativistic QCD organises its operators by how strongly their matrix elements in a heavy
quarkonium are suppressed: each operator carries an order in the relative velocity `v` and an
order in the inverse heavy-quark mass `1/m`. The operators are built from heavy-quark bilinears,
and the orders of a product of bilinears are the sums of the orders of its factors, because the
velocity scaling of a product is the product of the velocity scalings.

This module makes that grading explicit data. A family `B` of bilinears carries a grading
`deg : B → ℕ × ℕ`, the first component the order in `v` and the second the order in `1/m`. A
composite operator is a word in the bilinears, an element of `FreeMonoid B`, and its grading
`compositeDeg deg` is the sum of the gradings of its factors; it is additive on products
(`compositeDeg_mul`).

The substantive statement is the finiteness of each truncation: for every bound `n` only finitely
many composite operators have total order (`totalOrder`) at most `n`. This is what licenses
truncating an NRQCD sum over operators to finitely many terms. It is not automatic, and
`finite_compositeDeg_le_iff` identifies exactly what it needs: every bilinear is suppressed (has
positive total order), and only finitely many bilinears occur up to each total order. A single
unsuppressed bilinear already produces infinitely many operators of order zero, its powers. The
structure `PowerCounting` bundles a grading with these two conditions, and
`PowerCounting.truncation` is the resulting finite set of operators up to a given order.

## Main definitions

* `totalOrder`: the total order `a + b` of a grading `(a, b)` in `v` and `1/m`.
* `compositeDeg`: the grading of a product of bilinears.
* `gradedPiece`: the composite operators of a given grading.
* `PowerCounting`: a grading of bilinears in which every bilinear is suppressed and each total
  order is reached by finitely many bilinears.
* `PowerCounting.truncation`: the finite set of composite operators up to a given total order.

## Main results

* `compositeDeg_mul`: the grading is additive on products.
* `finite_compositeDeg_le`: the composite operators up to each total order form a finite set.
* `finite_compositeDeg_le_iff`: this finiteness holds for every bound exactly when every bilinear
  is suppressed and each total order is reached by finitely many bilinears.
* `finite_gradedPiece`: each graded piece is finite.
* `PowerCounting.mul_mem_truncation`: truncations are compatible with products.

## References

* G. P. Lepage, L. Magnea, C. Nakhleh, U. Magnea and K. Hornbostel, *Improved nonrelativistic
  QCD for heavy-quark physics*, Phys. Rev. D 46 (1992) 4052, Section II.
* G. T. Bodwin, E. Braaten and G. P. Lepage, *Rigorous QCD analysis of inclusive annihilation and
  production of heavy quarkonium*, Phys. Rev. D 51 (1995) 1125, Section II.
-/

public section

namespace EpsilonEridani.QFT.Quarkonium

variable {B : Type*}

/-! ### Total order and the grading of composite operators -/

/-- The total order `a + b` of a grading `(a, b)`, the sum of the order in the relative velocity
`v` and the order in the inverse heavy-quark mass `1/m`. -/
def totalOrder : ℕ × ℕ →+ ℕ := AddMonoidHom.fst ℕ ℕ + AddMonoidHom.snd ℕ ℕ

@[simp]
theorem totalOrder_apply (d : ℕ × ℕ) : totalOrder d = d.1 + d.2 := (rfl)

/-- The grading of a composite operator, a product of bilinears: the sum of the gradings `deg` of
its factors. -/
def compositeDeg (deg : B → ℕ × ℕ) (o : FreeMonoid B) : ℕ × ℕ :=
  (o.toList.map deg).sum

theorem compositeDeg_def (deg : B → ℕ × ℕ) (o : FreeMonoid B) :
    compositeDeg deg o = (o.toList.map deg).sum := (rfl)

variable (deg : B → ℕ × ℕ)

@[simp]
theorem compositeDeg_one : compositeDeg deg 1 = 0 := by
  simp [compositeDeg_def]

@[simp]
theorem compositeDeg_of (b : B) : compositeDeg deg (FreeMonoid.of b) = deg b := by
  simp [compositeDeg_def]

/-- The grading is additive on products: the grading of a composite operator is determined by its
factors. -/
@[simp]
theorem compositeDeg_mul (o o' : FreeMonoid B) :
    compositeDeg deg (o * o') = compositeDeg deg o + compositeDeg deg o' := by
  simp [compositeDeg_def]

@[simp]
theorem compositeDeg_pow (o : FreeMonoid B) (k : ℕ) :
    compositeDeg deg (o ^ k) = k • compositeDeg deg o := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, compositeDeg_mul, ih, succ_nsmul]

/-- The total order of a composite operator is the sum of the total orders of its factors. -/
theorem totalOrder_compositeDeg (o : FreeMonoid B) :
    totalOrder (compositeDeg deg o) = (o.toList.map fun b => totalOrder (deg b)).sum := by
  simp [compositeDeg_def, map_list_sum, Function.comp_def]

/-- Each factor of a composite operator has total order at most that of the operator. -/
theorem totalOrder_le_totalOrder_compositeDeg {o : FreeMonoid B} {b : B} (hb : b ∈ o.toList) :
    totalOrder (deg b) ≤ totalOrder (compositeDeg deg o) := by
  rw [totalOrder_compositeDeg]
  exact List.le_sum_of_mem (List.mem_map_of_mem hb)

/-- If every bilinear is suppressed, the number of factors of a composite operator is at most its
total order. -/
theorem length_le_totalOrder_compositeDeg (hpos : ∀ b, 0 < totalOrder (deg b))
    (o : FreeMonoid B) : o.length ≤ totalOrder (compositeDeg deg o) := by
  rw [totalOrder_compositeDeg, FreeMonoid.length,
    ← List.length_map (f := fun b => totalOrder (deg b))]
  refine List.length_le_sum_of_one_le _ fun _ hi => ?_
  obtain ⟨b, -, rfl⟩ := List.mem_map.1 hi
  exact hpos b

/-! ### Finiteness of the truncations -/

/-- **Finiteness of each truncation.** If every bilinear is suppressed and only finitely many
bilinears occur up to each total order, then only finitely many composite operators have total
order at most `n`. -/
theorem finite_compositeDeg_le (hpos : ∀ b, 0 < totalOrder (deg b))
    (hfin : ∀ n, {b | totalOrder (deg b) ≤ n}.Finite) (n : ℕ) :
    {o : FreeMonoid B | totalOrder (compositeDeg deg o) ≤ n}.Finite := by
  set S := {b | totalOrder (deg b) ≤ n}
  have : Finite S := hfin n
  refine ((List.finite_length_le S n).image
    fun l => FreeMonoid.ofList (l.map Subtype.val)).subset fun o ho => ?_
  have hmem : ∀ b ∈ o.toList, b ∈ S := fun b hb =>
    (totalOrder_le_totalOrder_compositeDeg deg hb).trans ho
  refine ⟨o.toList.pmap Subtype.mk hmem, ?_, ?_⟩
  · simpa [FreeMonoid.length] using (length_le_totalOrder_compositeDeg deg hpos o).trans ho
  · simp [List.map_pmap]

/-- An unsuppressed bilinear spoils finiteness: if the composite operators of total order zero
form a finite set, every bilinear has positive total order. -/
theorem totalOrder_pos_of_finite_compositeDeg_le
    (h : {o : FreeMonoid B | totalOrder (compositeDeg deg o) ≤ 0}.Finite) (b : B) :
    0 < totalOrder (deg b) := by
  refine Nat.pos_of_ne_zero fun hb => h.not_infinite ?_
  rw [totalOrder_apply, Nat.add_eq_zero_iff] at hb
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => FreeMonoid.ofList (List.replicate k b))
    (fun k k' hk => List.replicate_left_injective b (FreeMonoid.ofList.injective hk)) fun k => ?_
  simp [compositeDeg_def, List.map_replicate, List.sum_replicate, hb]

/-- If the composite operators up to total order `n` form a finite set, so do the bilinears up to
total order `n`. -/
theorem finite_deg_le_of_finite_compositeDeg_le {n : ℕ}
    (h : {o : FreeMonoid B | totalOrder (compositeDeg deg o) ≤ n}.Finite) :
    {b | totalOrder (deg b) ≤ n}.Finite :=
  h.preimage FreeMonoid.of_injective.injOn |>.subset fun b hb => by simpa using hb

/-- **What the finiteness of the truncations needs.** The composite operators up to every total
order form finite sets exactly when every bilinear is suppressed and each total order is reached
by finitely many bilinears. -/
theorem finite_compositeDeg_le_iff :
    (∀ n, {o : FreeMonoid B | totalOrder (compositeDeg deg o) ≤ n}.Finite) ↔
      (∀ b, 0 < totalOrder (deg b)) ∧ ∀ n, {b | totalOrder (deg b) ≤ n}.Finite :=
  ⟨fun h => ⟨totalOrder_pos_of_finite_compositeDeg_le deg (h 0),
      fun _ => finite_deg_le_of_finite_compositeDeg_le deg (h _)⟩,
    fun h => finite_compositeDeg_le deg h.1 h.2⟩

/-! ### Graded pieces -/

/-- The graded piece of grading `d`: the composite operators of order `d.1` in `v` and order
`d.2` in `1/m`. -/
def gradedPiece (d : ℕ × ℕ) : Set (FreeMonoid B) :=
  {o | compositeDeg deg o = d}

@[simp]
theorem mem_gradedPiece {d : ℕ × ℕ} {o : FreeMonoid B} :
    o ∈ gradedPiece deg d ↔ compositeDeg deg o = d := Iff.rfl

/-- The product of operators from two graded pieces lies in the piece of the summed grading. -/
theorem mul_mem_gradedPiece {d d' : ℕ × ℕ} {o o' : FreeMonoid B} (ho : o ∈ gradedPiece deg d)
    (ho' : o' ∈ gradedPiece deg d') : o * o' ∈ gradedPiece deg (d + d') := by
  simp_all

/-- Each graded piece is finite when every bilinear is suppressed and each total order is reached
by finitely many bilinears. -/
theorem finite_gradedPiece (hpos : ∀ b, 0 < totalOrder (deg b))
    (hfin : ∀ n, {b | totalOrder (deg b) ≤ n}.Finite) (d : ℕ × ℕ) :
    (gradedPiece deg d).Finite :=
  (finite_compositeDeg_le deg hpos hfin (totalOrder d)).subset fun o ho => by
    simp only [mem_gradedPiece] at ho
    simp [ho]

/-! ### Power countings -/

/-- A velocity power counting for an operator basis generated by a family `B` of heavy-quark
bilinears: each bilinear `b` has order `(deg b).1` in the relative velocity `v` and order
`(deg b).2` in the inverse heavy-quark mass `1/m`, every bilinear is suppressed, and only
finitely many bilinears occur up to each total order. By `finite_compositeDeg_le_iff`, the two
conditions are exactly what makes every truncation of the operator basis finite. -/
@[ext]
structure PowerCounting (B : Type*) where
  /-- The orders of a bilinear in `v` and in `1/m`. -/
  deg : B → ℕ × ℕ
  /-- Every bilinear has positive total order. -/
  totalOrder_pos : ∀ b, 0 < totalOrder (deg b)
  /-- Only finitely many bilinears occur up to each total order. -/
  finite_deg_le : ∀ n, {b | totalOrder (deg b) ≤ n}.Finite

namespace PowerCounting

/-- A grading of a finite family of bilinears in which every bilinear is suppressed is a power
counting. -/
def ofFinite [Finite B] (deg : B → ℕ × ℕ) (hpos : ∀ b, 0 < totalOrder (deg b)) :
    PowerCounting B where
  deg := deg
  totalOrder_pos := hpos
  finite_deg_le _ := Set.toFinite _

@[simp]
theorem ofFinite_deg [Finite B] (deg : B → ℕ × ℕ) (hpos : ∀ b, 0 < totalOrder (deg b)) :
    (ofFinite deg hpos).deg = deg := (rfl)

variable (P : PowerCounting B)

/-- The composite operators of a power counting up to each total order form a finite set. -/
theorem finite_compositeDeg_le (n : ℕ) :
    {o : FreeMonoid B | totalOrder (compositeDeg P.deg o) ≤ n}.Finite :=
  Quarkonium.finite_compositeDeg_le P.deg P.totalOrder_pos P.finite_deg_le n

/-- The truncation of the operator basis at total order `n`: the finitely many composite
operators of total order at most `n`. -/
noncomputable def truncation (n : ℕ) : Finset (FreeMonoid B) :=
  (P.finite_compositeDeg_le n).toFinset

@[simp]
theorem mem_truncation {n : ℕ} {o : FreeMonoid B} :
    o ∈ P.truncation n ↔ totalOrder (compositeDeg P.deg o) ≤ n := by
  simp [truncation]

/-- Raising the order of truncation keeps every operator already retained. -/
theorem truncation_mono : Monotone P.truncation := fun _ _ hmn _ ho =>
  P.mem_truncation.2 ((P.mem_truncation.1 ho).trans hmn)

/-- Every composite operator is retained by the truncation at its own total order. -/
theorem mem_truncation_totalOrder (o : FreeMonoid B) :
    o ∈ P.truncation (totalOrder (compositeDeg P.deg o)) :=
  P.mem_truncation.2 le_rfl

/-- The product of operators retained at orders `m` and `n` is retained at order `m + n`. -/
theorem mul_mem_truncation {m n : ℕ} {o o' : FreeMonoid B} (ho : o ∈ P.truncation m)
    (ho' : o' ∈ P.truncation n) : o * o' ∈ P.truncation (m + n) := by
  rw [mem_truncation] at ho ho' ⊢
  rw [compositeDeg_mul, map_add]
  exact add_le_add ho ho'

/-- The truncation at order zero is the identity operator alone. -/
theorem truncation_zero : P.truncation 0 = {1} := by
  ext o
  simp only [mem_truncation, nonpos_iff_eq_zero, Finset.mem_singleton]
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  have := length_le_totalOrder_compositeDeg P.deg P.totalOrder_pos o
  rw [h, nonpos_iff_eq_zero, FreeMonoid.length_eq_zero] at this
  exact this

end PowerCounting

end EpsilonEridani.QFT.Quarkonium
