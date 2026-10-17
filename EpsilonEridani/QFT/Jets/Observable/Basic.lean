/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.Algebra.Ring.Real

/-!
# Final states, observables, and infrared and collinear safety

A hadronic final state is a finite multiset of momenta `s : Multiset V` in an abstract real
vector space `V`, and an observable is a function on final states. A multiset rather than a list
so that no observable can depend on an ordering of the particles, and rather than a finite set so
that two partons of equal momentum, the configuration an exact collinear splitting produces, are
two partons.

This file defines the two operations that the safety conditions are about,

* adding a soft momentum `p` to `s`, which is `p ::ₘ s`, and
* the collinear splitting `splitCollinear p z s`, which replaces one copy of `p` in `s` by the
  collinear pair `z • p`, `(1 - z) • p`,

and the safety conditions themselves:

* `IsCollinearSafe O`: `O` is exactly invariant under every collinear splitting with `z ∈ [0, 1]`;
* `IsInfraredSafe O`: `O (p ::ₘ s)` tends to `O s` as `p` tends to `0`;
* `IsIRCSafe O`: both.

`IsCollinearSafe` is stated on final states `p ::ₘ s` that visibly contain the split momentum, so
that it needs no decidable equality on `V`; `isCollinearSafe_iff_splitCollinear` restates it with
`splitCollinear`.

Infrared safety is a limit condition, not continuity of `O` in the final state: `IsInfraredSafe`
constrains only the limit of adding a momentum at each fixed `s`, so a safe observable need not be
continuous as a function of the momenta. The limit is taken over the full neighbourhood filter
`𝓝 0`, which contains the point `p = 0` itself, so for a T1 codomain an infrared safe observable
also satisfies `O (0 ::ₘ s) = O s` exactly (`IsInfraredSafe.apply_zero_cons`).

The safety predicates are stated for observables with values in an arbitrary (topological)
codomain, so that vector-valued quantities such as the total momentum `Multiset.sum`, or later the
multiset of jet momenta, are covered by the same definitions. Each of the two conditions is
preserved by composition with maps (`IsCollinearSafe.map`, and `IsInfraredSafe.map` for continuous
maps) and by pairing (`IsCollinearSafe.prodMk`, `IsInfraredSafe.prodMk`), hence by addition,
negation, subtraction and multiplication (`IsCollinearSafe.add`, …, and `IsInfraredSafe.add`, …
for continuous operations), and so is their conjunction (`IsIRCSafe.add`, `IsIRCSafe.neg`,
`IsIRCSafe.sub`, `IsIRCSafe.mul`). The safe observables with values in a topological ring therefore
form a subring (`ircSafeSubring`).

The basic positive examples are the total momentum (`isIRCSafe_multisetSum`) and the invariant
mass squared `invariantMassSq g s = g P P` of the total momentum `P` of the whole final state, for
a continuous bilinear form `g` (`isIRCSafe_invariantMassSq`).

## References

* G. Sterman and S. Weinberg, *Jets from Quantum Chromodynamics*,
  Phys. Rev. Lett. 39 (1977) 1436.
* G. P. Salam, *Towards jetography*, Eur. Phys. J. C 67 (2010) 637, §2.
-/

public section

namespace EpsilonEridani.QFT.Jets

open Filter Topology

variable {V X Y : Type*}

/-- An observable: a real-valued function of a hadronic final state `s : Multiset V`.
Jet multiplicities, components of jet momenta and event shapes are all of this type. -/
abbrev Observable (V : Type*) := Multiset V → ℝ

/-! ### Collinear splitting -/

section Split

variable [AddCommGroup V] [Module ℝ V] [DecidableEq V]

/-- The collinear splitting of a final state: one copy of the momentum `p` in `s` is replaced by
the collinear pair `z • p` and `(1 - z) • p`. (When `p ∉ s` nothing is erased; the safety
conditions only ever split a member of `s`.) -/
def splitCollinear (p : V) (z : ℝ) (s : Multiset V) : Multiset V :=
  z • p ::ₘ (1 - z) • p ::ₘ s.erase p

theorem splitCollinear_def (p : V) (z : ℝ) (s : Multiset V) :
    splitCollinear p z s = z • p ::ₘ (1 - z) • p ::ₘ s.erase p :=
  (rfl)

@[simp]
theorem splitCollinear_cons_self (p : V) (z : ℝ) (s : Multiset V) :
    splitCollinear p z (p ::ₘ s) = z • p ::ₘ (1 - z) • p ::ₘ s := by
  simp [splitCollinear_def]

/-- The two fractions `z` and `1 - z` play symmetric roles. -/
theorem splitCollinear_one_sub (p : V) (z : ℝ) (s : Multiset V) :
    splitCollinear p (1 - z) s = splitCollinear p z s := by
  simp only [splitCollinear_def, sub_sub_cancel]
  exact Multiset.cons_swap _ _ _

/-- Splitting with fraction `0` is the same as adding a zero momentum. -/
@[simp]
theorem splitCollinear_zero {p : V} {s : Multiset V} (hp : p ∈ s) :
    splitCollinear p 0 s = 0 ::ₘ s := by
  simp [splitCollinear_def, Multiset.cons_erase hp]

/-- Splitting with fraction `1` is the same as adding a zero momentum. -/
@[simp]
theorem splitCollinear_one {p : V} {s : Multiset V} (hp : p ∈ s) :
    splitCollinear p 1 s = 0 ::ₘ s := by
  rw [← splitCollinear_one_sub, sub_self, splitCollinear_zero hp]

/-- The members of a collinear splitting: the two collinear fractions of `p`, and the members of
`s` with one copy of `p` removed. -/
@[simp]
theorem mem_splitCollinear {p q : V} {z : ℝ} {s : Multiset V} :
    q ∈ splitCollinear p z s ↔ q = z • p ∨ q = (1 - z) • p ∨ q ∈ s.erase p := by
  simp [splitCollinear_def]

/-- Splitting a momentum other than an added one commutes with adding it. -/
theorem splitCollinear_cons_of_ne {p q : V} (z : ℝ) (s : Multiset V) (h : p ≠ q) :
    splitCollinear p z (q ::ₘ s) = q ::ₘ splitCollinear p z s := by
  simp only [splitCollinear_def, Multiset.erase_cons_tail s h.symm]
  rw [Multiset.cons_swap ((1 - z) • p), Multiset.cons_swap (z • p)]

/-- Splitting a momentum already present commutes with adding any momentum, including another
copy of the same one. -/
theorem splitCollinear_cons_of_mem {p : V} (q : V) (z : ℝ) {s : Multiset V} (hp : p ∈ s) :
    splitCollinear p z (q ::ₘ s) = q ::ₘ splitCollinear p z s := by
  simp only [splitCollinear_def, Multiset.erase_cons_tail_of_mem hp]
  rw [Multiset.cons_swap ((1 - z) • p), Multiset.cons_swap (z • p)]

/-- A collinear splitting of a member adds exactly one particle. -/
@[simp]
theorem card_splitCollinear {p : V} (z : ℝ) {s : Multiset V} (hp : p ∈ s) :
    Multiset.card (splitCollinear p z s) = Multiset.card s + 1 := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  simp

/-- A collinear splitting of a member preserves the total momentum. -/
@[simp]
theorem sum_splitCollinear {p : V} (z : ℝ) {s : Multiset V} (hp : p ∈ s) :
    (splitCollinear p z s).sum = s.sum := by
  rw [splitCollinear_def, Multiset.sum_cons, Multiset.sum_cons, ← add_assoc, smul_add_one_sub_smul,
    ← Multiset.sum_cons, Multiset.cons_erase hp]

end Split

/-! ### The safety conditions -/

section Collinear

variable [AddCommGroup V] [Module ℝ V]

/-- An observable is *collinear safe* if it is exactly invariant under replacing a member `p` of
a final state `p ::ₘ s` by the collinear pair `z • p`, `(1 - z) • p` with `z ∈ [0, 1]`. -/
def IsCollinearSafe (O : Multiset V → X) : Prop :=
  ∀ (s : Multiset V) (p : V), ∀ z ∈ Set.Icc (0 : ℝ) 1, O (z • p ::ₘ (1 - z) • p ::ₘ s) = O (p ::ₘ s)

theorem isCollinearSafe_def {O : Multiset V → X} :
    IsCollinearSafe O ↔ ∀ (s : Multiset V) (p : V), ∀ z ∈ Set.Icc (0 : ℝ) 1,
      O (z • p ::ₘ (1 - z) • p ::ₘ s) = O (p ::ₘ s) :=
  Iff.rfl

/-- Collinear safety in terms of `splitCollinear`: `O` is invariant under every collinear splitting
of a member of a final state. -/
theorem isCollinearSafe_iff_splitCollinear [DecidableEq V] {O : Multiset V → X} :
    IsCollinearSafe O ↔ ∀ s : Multiset V, ∀ p ∈ s, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      O (splitCollinear p z s) = O s := by
  refine ⟨fun hO s p hp z hz => ?_, fun hO s p z hz => ?_⟩
  · obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
    rw [splitCollinear_cons_self]
    exact hO t p z hz
  · rw [← splitCollinear_cons_self]
    exact hO _ p (Multiset.mem_cons_self p s) z hz

/-- A collinear safe observable does not see an added zero momentum on a nonempty final state:
splitting with fraction `0` adds exactly a zero momentum. -/
theorem IsCollinearSafe.apply_zero_cons {O : Multiset V → X} (hO : IsCollinearSafe O)
    {s : Multiset V} (hs : s ≠ 0) : O (0 ::ₘ s) = O s := by
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hs
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  simpa using hO t _ 0 ⟨le_rfl, zero_le_one⟩

theorem isCollinearSafe_const (x : X) : IsCollinearSafe (fun _ : Multiset V => x) :=
  fun _ _ _ _ => rfl

theorem IsCollinearSafe.map {O : Multiset V → X} (f : X → Y) (hO : IsCollinearSafe O) :
    IsCollinearSafe (f ∘ O) :=
  fun s p z hz => congrArg f (hO s p z hz)

theorem IsCollinearSafe.prodMk {O₁ : Multiset V → X} {O₂ : Multiset V → Y}
    (h₁ : IsCollinearSafe O₁) (h₂ : IsCollinearSafe O₂) :
    IsCollinearSafe (fun s => (O₁ s, O₂ s)) :=
  fun s p z hz => Prod.ext (h₁ s p z hz) (h₂ s p z hz)

/-- Any function of two collinear safe observables is collinear safe. -/
theorem IsCollinearSafe.map₂ {Z : Type*} {O₁ : Multiset V → X} {O₂ : Multiset V → Y}
    (f : X → Y → Z) (h₁ : IsCollinearSafe O₁) (h₂ : IsCollinearSafe O₂) :
    IsCollinearSafe (fun s => f (O₁ s) (O₂ s)) :=
  (h₁.prodMk h₂).map (Function.uncurry f)

/-- The sum of two collinear safe observables is collinear safe. -/
theorem IsCollinearSafe.add [Add X] {O₁ O₂ : Multiset V → X} (h₁ : IsCollinearSafe O₁)
    (h₂ : IsCollinearSafe O₂) : IsCollinearSafe (fun s => O₁ s + O₂ s) :=
  h₁.map₂ (· + ·) h₂

/-- The negation of a collinear safe observable is collinear safe. -/
theorem IsCollinearSafe.neg [Neg X] {O : Multiset V → X} (h : IsCollinearSafe O) :
    IsCollinearSafe (fun s => -O s) :=
  h.map Neg.neg

/-- The difference of two collinear safe observables is collinear safe. -/
theorem IsCollinearSafe.sub [Sub X] {O₁ O₂ : Multiset V → X} (h₁ : IsCollinearSafe O₁)
    (h₂ : IsCollinearSafe O₂) : IsCollinearSafe (fun s => O₁ s - O₂ s) :=
  h₁.map₂ (· - ·) h₂

/-- The product of two collinear safe observables is collinear safe. -/
theorem IsCollinearSafe.mul [Mul X] {O₁ O₂ : Multiset V → X} (h₁ : IsCollinearSafe O₁)
    (h₂ : IsCollinearSafe O₂) : IsCollinearSafe (fun s => O₁ s * O₂ s) :=
  h₁.map₂ (· * ·) h₂

end Collinear

section Infrared

variable [Zero V] [TopologicalSpace V] [TopologicalSpace X] [TopologicalSpace Y]

/-- An observable is *infrared safe* if adding a momentum `p` to any final state and letting `p`
tend to zero recovers the value on the original state. This is a limit condition at each fixed
final state, not continuity of the observable. The limit is over the full neighbourhood filter
`𝓝 0`, not the punctured one, so for a T1 codomain such as `ℝ` it also forces the exact equality
`O (0 ::ₘ s) = O s` for every `s`, including `s = 0` (`IsInfraredSafe.apply_zero_cons`). -/
def IsInfraredSafe (O : Multiset V → X) : Prop :=
  ∀ s : Multiset V, Tendsto (fun p : V => O (p ::ₘ s)) (𝓝 0) (𝓝 (O s))

theorem isInfraredSafe_def {O : Multiset V → X} :
    IsInfraredSafe O ↔ ∀ s : Multiset V, Tendsto (fun p : V => O (p ::ₘ s)) (𝓝 0) (𝓝 (O s)) :=
  Iff.rfl

/-- In a T1 codomain an infrared safe observable does not see an added zero momentum, since the
limit defining infrared safety is over a filter containing `p = 0`. -/
theorem IsInfraredSafe.apply_zero_cons [T1Space X] {O : Multiset V → X} (hO : IsInfraredSafe O)
    (s : Multiset V) : O (0 ::ₘ s) = O s :=
  pure_le_nhds_iff.1 ((hO s).mono_left (pure_le_nhds 0))

theorem isInfraredSafe_const (x : X) : IsInfraredSafe (fun _ : Multiset V => x) :=
  fun _ => tendsto_const_nhds

theorem IsInfraredSafe.map {O : Multiset V → X} {f : X → Y} (hf : Continuous f)
    (hO : IsInfraredSafe O) : IsInfraredSafe (f ∘ O) :=
  fun s => (hf.tendsto _).comp (hO s)

theorem IsInfraredSafe.prodMk {O₁ : Multiset V → X} {O₂ : Multiset V → Y}
    (h₁ : IsInfraredSafe O₁) (h₂ : IsInfraredSafe O₂) :
    IsInfraredSafe (fun s => (O₁ s, O₂ s)) :=
  fun s => (h₁ s).prodMk_nhds (h₂ s)

/-- A continuous function of two infrared safe observables is infrared safe. -/
theorem IsInfraredSafe.map₂ {Z : Type*} [TopologicalSpace Z] {O₁ : Multiset V → X}
    {O₂ : Multiset V → Y} {f : X → Y → Z} (hf : Continuous (Function.uncurry f))
    (h₁ : IsInfraredSafe O₁) (h₂ : IsInfraredSafe O₂) :
    IsInfraredSafe (fun s => f (O₁ s) (O₂ s)) :=
  (h₁.prodMk h₂).map hf

/-- The sum of two infrared safe observables is infrared safe. -/
theorem IsInfraredSafe.add [Add X] [ContinuousAdd X] {O₁ O₂ : Multiset V → X}
    (h₁ : IsInfraredSafe O₁) (h₂ : IsInfraredSafe O₂) : IsInfraredSafe (fun s => O₁ s + O₂ s) :=
  h₁.map₂ (f := (· + ·)) continuous_add h₂

/-- The negation of an infrared safe observable is infrared safe. -/
theorem IsInfraredSafe.neg [Neg X] [ContinuousNeg X] {O : Multiset V → X} (h : IsInfraredSafe O) :
    IsInfraredSafe (fun s => -O s) :=
  h.map (f := Neg.neg) continuous_neg

/-- The difference of two infrared safe observables is infrared safe. -/
theorem IsInfraredSafe.sub [Sub X] [ContinuousSub X] {O₁ O₂ : Multiset V → X}
    (h₁ : IsInfraredSafe O₁) (h₂ : IsInfraredSafe O₂) : IsInfraredSafe (fun s => O₁ s - O₂ s) :=
  h₁.map₂ (f := (· - ·)) continuous_sub h₂

/-- The product of two infrared safe observables is infrared safe. -/
theorem IsInfraredSafe.mul [Mul X] [ContinuousMul X] {O₁ O₂ : Multiset V → X}
    (h₁ : IsInfraredSafe O₁) (h₂ : IsInfraredSafe O₂) : IsInfraredSafe (fun s => O₁ s * O₂ s) :=
  h₁.map₂ (f := (· * ·)) continuous_mul h₂

end Infrared

section IRC

variable [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [TopologicalSpace X]
  [TopologicalSpace Y]

/-- An observable is *infrared and collinear safe* if it is both collinear safe and infrared
safe. This is the condition under which an observable has a finite fixed-order prediction. -/
structure IsIRCSafe (O : Multiset V → X) : Prop where
  /-- Exact invariance under collinear splitting. -/
  collinear : IsCollinearSafe O
  /-- Insensitivity to a vanishingly soft added momentum. -/
  infrared : IsInfraredSafe O

theorem isIRCSafe_const (x : X) : IsIRCSafe (fun _ : Multiset V => x) :=
  ⟨isCollinearSafe_const x, isInfraredSafe_const x⟩

theorem IsIRCSafe.map {O : Multiset V → X} {f : X → Y} (hf : Continuous f) (hO : IsIRCSafe O) :
    IsIRCSafe (f ∘ O) :=
  ⟨hO.collinear.map f, hO.infrared.map hf⟩

theorem IsIRCSafe.prodMk {O₁ : Multiset V → X} {O₂ : Multiset V → Y} (h₁ : IsIRCSafe O₁)
    (h₂ : IsIRCSafe O₂) : IsIRCSafe (fun s => (O₁ s, O₂ s)) :=
  ⟨h₁.collinear.prodMk h₂.collinear, h₁.infrared.prodMk h₂.infrared⟩

/-- A continuous function of two infrared and collinear safe observables is safe. -/
theorem IsIRCSafe.map₂ {Z : Type*} [TopologicalSpace Z] {O₁ : Multiset V → X}
    {O₂ : Multiset V → Y} {f : X → Y → Z} (hf : Continuous (Function.uncurry f))
    (h₁ : IsIRCSafe O₁) (h₂ : IsIRCSafe O₂) : IsIRCSafe (fun s => f (O₁ s) (O₂ s)) :=
  ⟨h₁.collinear.map₂ f h₂.collinear, h₁.infrared.map₂ hf h₂.infrared⟩

/-- The sum of two infrared and collinear safe observables is safe. -/
theorem IsIRCSafe.add [Add X] [ContinuousAdd X] {O₁ O₂ : Multiset V → X} (h₁ : IsIRCSafe O₁)
    (h₂ : IsIRCSafe O₂) : IsIRCSafe (fun s => O₁ s + O₂ s) :=
  ⟨h₁.collinear.add h₂.collinear, h₁.infrared.add h₂.infrared⟩

/-- The negation of an infrared and collinear safe observable is safe. -/
theorem IsIRCSafe.neg [Neg X] [ContinuousNeg X] {O : Multiset V → X} (h : IsIRCSafe O) :
    IsIRCSafe (fun s => -O s) :=
  ⟨h.collinear.neg, h.infrared.neg⟩

/-- The difference of two infrared and collinear safe observables is safe. -/
theorem IsIRCSafe.sub [Sub X] [ContinuousSub X] {O₁ O₂ : Multiset V → X} (h₁ : IsIRCSafe O₁)
    (h₂ : IsIRCSafe O₂) : IsIRCSafe (fun s => O₁ s - O₂ s) :=
  ⟨h₁.collinear.sub h₂.collinear, h₁.infrared.sub h₂.infrared⟩

/-- The product of two infrared and collinear safe observables is safe. -/
theorem IsIRCSafe.mul [Mul X] [ContinuousMul X] {O₁ O₂ : Multiset V → X} (h₁ : IsIRCSafe O₁)
    (h₂ : IsIRCSafe O₂) : IsIRCSafe (fun s => O₁ s * O₂ s) :=
  ⟨h₁.collinear.mul h₂.collinear, h₁.infrared.mul h₂.infrared⟩

variable (V) in
/-- The infrared and collinear safe observables with values in a topological ring form a
subring of all observables. -/
def ircSafeSubring (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] :
    Subring (Multiset V → R) where
  carrier := {O | IsIRCSafe O}
  zero_mem' := isIRCSafe_const 0
  one_mem' := isIRCSafe_const 1
  add_mem' {O₁ O₂} (h₁ : IsIRCSafe O₁) (h₂ : IsIRCSafe O₂) := h₁.add h₂
  mul_mem' {O₁ O₂} (h₁ : IsIRCSafe O₁) (h₂ : IsIRCSafe O₂) := h₁.mul h₂
  neg_mem' {O} (h : IsIRCSafe O) := h.neg

@[simp]
theorem mem_ircSafeSubring {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {O : Multiset V → R} : O ∈ ircSafeSubring V R ↔ IsIRCSafe O :=
  (Iff.rfl)

/-- A finite sum of infrared and collinear safe observables is safe. -/
theorem isIRCSafe_finsetSum {ι M : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    {t : Finset ι} {O : ι → Multiset V → M} (hO : ∀ i ∈ t, IsIRCSafe (O i)) :
    IsIRCSafe (∑ i ∈ t, O i) :=
  Finset.sum_induction O IsIRCSafe (fun _ _ => IsIRCSafe.add) (isIRCSafe_const 0) hO

/-- A finite product of infrared and collinear safe observables with values in a commutative
topological monoid is safe. -/
theorem isIRCSafe_finsetProd {ι M : Type*} [CommMonoid M] [TopologicalSpace M] [ContinuousMul M]
    {t : Finset ι} {O : ι → Multiset V → M} (hO : ∀ i ∈ t, IsIRCSafe (O i)) :
    IsIRCSafe (∏ i ∈ t, O i) :=
  Finset.prod_induction O IsIRCSafe (fun _ _ => IsIRCSafe.mul) (isIRCSafe_const 1) hO

end IRC

/-! ### Total momentum and invariant mass -/

section TotalMomentum

/-- The total momentum of a final state is infrared safe. -/
theorem isInfraredSafe_multisetSum [AddCommMonoid V] [TopologicalSpace V] [ContinuousAdd V] :
    IsInfraredSafe (Multiset.sum : Multiset V → V) := by
  intro s
  simp only [Multiset.sum_cons]
  simpa using (tendsto_id : Tendsto id (𝓝 (0 : V)) (𝓝 0)).add_const s.sum

variable [AddCommGroup V] [Module ℝ V]

/-- The invariant mass squared of a final state with respect to a bilinear form `g` (the
Minkowski metric, say): `g P P` for the total momentum `P = s.sum`. -/
def invariantMassSq (g : LinearMap.BilinForm ℝ V) : Observable V :=
  fun s => g s.sum s.sum

theorem invariantMassSq_def (g : LinearMap.BilinForm ℝ V) (s : Multiset V) :
    invariantMassSq g s = g s.sum s.sum :=
  (rfl)

@[simp]
theorem invariantMassSq_zero (g : LinearMap.BilinForm ℝ V) : invariantMassSq g 0 = 0 := by
  simp [invariantMassSq_def]

/-- The invariant mass squared of the union of two final states is not additive: it picks up the
two cross terms `g P Q` and `g Q P` of their total momenta `P` and `Q`. -/
theorem invariantMassSq_add (g : LinearMap.BilinForm ℝ V) (s t : Multiset V) :
    invariantMassSq g (s + t) =
      invariantMassSq g s + g s.sum t.sum + g t.sum s.sum + invariantMassSq g t := by
  simp only [invariantMassSq_def, Multiset.sum_add, map_add, LinearMap.add_apply]
  abel

/-- The total momentum of a final state is collinear safe. -/
theorem isCollinearSafe_multisetSum : IsCollinearSafe (Multiset.sum : Multiset V → V) :=
  fun _ p z _ => by simp [← add_assoc, smul_add_one_sub_smul]

/-- The total momentum of a final state is infrared and collinear safe. -/
theorem isIRCSafe_multisetSum [TopologicalSpace V] [ContinuousAdd V] :
    IsIRCSafe (Multiset.sum : Multiset V → V) :=
  ⟨isCollinearSafe_multisetSum, isInfraredSafe_multisetSum⟩

/-- The invariant mass squared is infrared and collinear safe for any jointly continuous bilinear
form `g`. -/
theorem isIRCSafe_invariantMassSq [TopologicalSpace V] [ContinuousAdd V]
    (g : LinearMap.BilinForm ℝ V) (hg : Continuous fun q : V × V => g q.1 q.2) :
    IsIRCSafe (invariantMassSq g) :=
  isIRCSafe_multisetSum.map₂ (f := fun x y => g x y) hg isIRCSafe_multisetSum

/-- The invariant mass squared is infrared and collinear safe for any bilinear form `g` on a
finite-dimensional `V` with its canonical topology. -/
theorem isIRCSafe_invariantMassSq_of_finite [TopologicalSpace V] [IsModuleTopology ℝ V]
    [Module.Finite ℝ V] (g : LinearMap.BilinForm ℝ V) :
    IsIRCSafe (invariantMassSq g) := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℝ V
  exact isIRCSafe_invariantMassSq g (IsModuleTopology.continuous_bilinear_of_finite_left g)

end TotalMomentum

end EpsilonEridani.QFT.Jets
