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

Infrared safety is a limit condition, not continuity of `O` in the final state: `IsInfraredSafe`
constrains only the limit of adding a momentum at each fixed `s`, so a safe observable need not be
continuous as a function of the momenta.

The safety predicates are stated for observables with values in an arbitrary (topological)
codomain, so that vector-valued quantities such as the total momentum `Multiset.sum`, or later the
multiset of jet momenta, are covered by the same definitions. Safety is preserved by composition
with continuous maps (`IsIRCSafe.map`) and by pairing (`IsIRCSafe.prodMk`), hence by continuous
addition and multiplication (`IsIRCSafe.add`, `IsIRCSafe.mul`), so the safe observables with values
in a topological ring form a subring (`ircSafeSubring`).

The basic positive examples are the total momentum (`isIRCSafe_sum`) and the invariant mass
squared `g P P` of the total momentum `P` of the whole final state, for a continuous bilinear form
`g` (`isIRCSafe_bilinForm_sum_sum`).

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
  have := Multiset.card_pos_iff_exists_mem.2 ⟨p, hp⟩
  simp [splitCollinear_def, Multiset.card_erase_of_mem hp]
  omega

/-- A collinear splitting of a member preserves the total momentum. -/
@[simp]
theorem sum_splitCollinear {p : V} (z : ℝ) {s : Multiset V} (hp : p ∈ s) :
    (splitCollinear p z s).sum = s.sum := by
  rw [splitCollinear_def, Multiset.sum_cons, Multiset.sum_cons, ← add_assoc, smul_add_one_sub_smul,
    ← Multiset.sum_cons, Multiset.cons_erase hp]

end Split

/-! ### The safety conditions -/

section Collinear

variable [AddCommGroup V] [Module ℝ V] [DecidableEq V]

/-- An observable is *collinear safe* if it is exactly invariant under replacing any member `p` of
a final state by the collinear pair `z • p`, `(1 - z) • p` with `z ∈ [0, 1]`. -/
def IsCollinearSafe (O : Multiset V → X) : Prop :=
  ∀ s : Multiset V, ∀ p ∈ s, ∀ z ∈ Set.Icc (0 : ℝ) 1, O (splitCollinear p z s) = O s

theorem isCollinearSafe_iff {O : Multiset V → X} :
    IsCollinearSafe O ↔
      ∀ s : Multiset V, ∀ p ∈ s, ∀ z ∈ Set.Icc (0 : ℝ) 1, O (splitCollinear p z s) = O s :=
  Iff.rfl

theorem IsCollinearSafe.apply_splitCollinear {O : Multiset V → X} (hO : IsCollinearSafe O)
    {s : Multiset V} {p : V} (hp : p ∈ s) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    O (splitCollinear p z s) = O s :=
  hO s p hp z hz

/-- A collinear safe observable does not see an added zero momentum on a nonempty final state:
splitting with fraction `0` adds exactly a zero momentum. -/
theorem IsCollinearSafe.apply_zero_cons {O : Multiset V → X} (hO : IsCollinearSafe O)
    {s : Multiset V} (hs : s ≠ 0) : O (0 ::ₘ s) = O s := by
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hs
  rw [← splitCollinear_zero hp]
  exact hO.apply_splitCollinear hp ⟨le_rfl, zero_le_one⟩

theorem isCollinearSafe_const (x : X) : IsCollinearSafe (fun _ : Multiset V => x) :=
  fun _ _ _ _ _ => rfl

theorem IsCollinearSafe.map {O : Multiset V → X} (f : X → Y) (hO : IsCollinearSafe O) :
    IsCollinearSafe (f ∘ O) :=
  fun s p hp z hz => congrArg f (hO s p hp z hz)

theorem IsCollinearSafe.prodMk {O₁ : Multiset V → X} {O₂ : Multiset V → Y}
    (h₁ : IsCollinearSafe O₁) (h₂ : IsCollinearSafe O₂) :
    IsCollinearSafe (fun s => (O₁ s, O₂ s)) :=
  fun s p hp z hz => Prod.ext (h₁ s p hp z hz) (h₂ s p hp z hz)

end Collinear

section Infrared

variable [Zero V] [TopologicalSpace V] [TopologicalSpace X] [TopologicalSpace Y]

/-- An observable is *infrared safe* if adding a momentum `p` to any final state and letting `p`
tend to zero recovers the value on the original state. This is a limit condition at each fixed
final state, not continuity of the observable. -/
def IsInfraredSafe (O : Multiset V → X) : Prop :=
  ∀ s : Multiset V, Tendsto (fun p : V => O (p ::ₘ s)) (𝓝 0) (𝓝 (O s))

theorem isInfraredSafe_iff {O : Multiset V → X} :
    IsInfraredSafe O ↔ ∀ s : Multiset V, Tendsto (fun p : V => O (p ::ₘ s)) (𝓝 0) (𝓝 (O s)) :=
  Iff.rfl

theorem IsInfraredSafe.tendsto {O : Multiset V → X} (hO : IsInfraredSafe O) (s : Multiset V) :
    Tendsto (fun p : V => O (p ::ₘ s)) (𝓝 0) (𝓝 (O s)) :=
  hO s

theorem isInfraredSafe_const (x : X) : IsInfraredSafe (fun _ : Multiset V => x) :=
  fun _ => tendsto_const_nhds

theorem IsInfraredSafe.map {O : Multiset V → X} {f : X → Y} (hf : Continuous f)
    (hO : IsInfraredSafe O) : IsInfraredSafe (f ∘ O) :=
  fun s => (hf.tendsto _).comp (hO s)

theorem IsInfraredSafe.prodMk {O₁ : Multiset V → X} {O₂ : Multiset V → Y}
    (h₁ : IsInfraredSafe O₁) (h₂ : IsInfraredSafe O₂) :
    IsInfraredSafe (fun s => (O₁ s, O₂ s)) :=
  fun s => (h₁ s).prodMk_nhds (h₂ s)

end Infrared

section IRC

variable [AddCommGroup V] [Module ℝ V] [DecidableEq V] [TopologicalSpace V]
  [TopologicalSpace X] [TopologicalSpace Y]

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
  (h₁.prodMk h₂).map hf

/-- The sum of two infrared and collinear safe observables is safe. -/
theorem IsIRCSafe.add [Add X] [ContinuousAdd X] {O₁ O₂ : Multiset V → X} (h₁ : IsIRCSafe O₁)
    (h₂ : IsIRCSafe O₂) : IsIRCSafe (fun s => O₁ s + O₂ s) :=
  h₁.map₂ (f := (· + ·)) continuous_add h₂

/-- The product of two infrared and collinear safe observables is safe. -/
theorem IsIRCSafe.mul [Mul X] [ContinuousMul X] {O₁ O₂ : Multiset V → X} (h₁ : IsIRCSafe O₁)
    (h₂ : IsIRCSafe O₂) : IsIRCSafe (fun s => O₁ s * O₂ s) :=
  h₁.map₂ (f := (· * ·)) continuous_mul h₂

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
  neg_mem' {O} (h : IsIRCSafe O) := IsIRCSafe.map (f := fun x : R => -x) continuous_neg h

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
theorem isInfraredSafe_sum [AddCommMonoid V] [TopologicalSpace V] [ContinuousAdd V] :
    IsInfraredSafe (Multiset.sum : Multiset V → V) := by
  intro s
  simp only [Multiset.sum_cons]
  simpa using (tendsto_id : Tendsto id (𝓝 (0 : V)) (𝓝 0)).add_const s.sum

variable [AddCommGroup V] [Module ℝ V] [DecidableEq V]

/-- The total momentum of a final state is collinear safe. -/
theorem isCollinearSafe_sum : IsCollinearSafe (Multiset.sum : Multiset V → V) :=
  fun _ _ hp z _ => sum_splitCollinear z hp

/-- The total momentum of a final state is infrared and collinear safe. -/
theorem isIRCSafe_sum [TopologicalSpace V] [ContinuousAdd V] :
    IsIRCSafe (Multiset.sum : Multiset V → V) :=
  ⟨isCollinearSafe_sum, isInfraredSafe_sum⟩

/-- The invariant mass squared `g P P` of the total momentum `P` of a final state is infrared and
collinear safe, for any jointly continuous bilinear form `g`. -/
theorem isIRCSafe_bilinForm_sum_sum [TopologicalSpace V] [ContinuousAdd V]
    (g : LinearMap.BilinForm ℝ V) (hg : Continuous fun q : V × V => g q.1 q.2) :
    IsIRCSafe (fun s : Multiset V => g s.sum s.sum) :=
  isIRCSafe_sum.map₂ (f := fun x y => g x y) hg isIRCSafe_sum

/-- The invariant mass squared `g P P` of the total momentum `P` of a final state is infrared and
collinear safe, for any bilinear form `g` on a finite-dimensional `V` with its canonical
topology. -/
theorem isIRCSafe_bilinForm_sum_sum_of_finite [TopologicalSpace V] [IsModuleTopology ℝ V]
    [Module.Finite ℝ V] (g : LinearMap.BilinForm ℝ V) :
    IsIRCSafe (fun s : Multiset V => g s.sum s.sum) := by
  have : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℝ V
  exact isIRCSafe_bilinForm_sum_sum g (IsModuleTopology.continuous_bilinear_of_finite_left g)

end TotalMomentum

end EpsilonEridani.QFT.Jets
