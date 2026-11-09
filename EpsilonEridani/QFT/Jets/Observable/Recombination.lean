/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Jets.Observable.Basic
import Mathlib.Algebra.Module.Torsion.Field

/-!
# Recombination schemes

A sequential-recombination jet algorithm repeatedly replaces a pair of pseudojets by a single
one. The rule it uses to do so is a *recombination scheme*: a symmetric map `V → V → V` on the
momentum space. This file defines the schemes, the conditions a scheme can satisfy, and the
property of a scheme that a safety proof for an algorithm consumes.

* `RecombinationScheme V` carries the merge map and its symmetry, symmetry being structural
  because the pair an algorithm selects is unordered.
* `eScheme V` is the `E` scheme, which merges by adding momenta.
* `RecombinationScheme.IsAdditive`, `.IsPosHomogeneous` and `.IsUnital` are additivity of the
  merge map in the pair, positive homogeneity of degree one, and the normalisation that merging a
  vanishing momentum changes nothing. Additivity and homogeneity together say exactly that the
  merge map is `ℝ`-linear on the pair (`RecombinationScheme.isLinearMap_uncurry_merge_iff`).
* `RecombinationScheme.IsCollinearExact` is the property that merging the two fragments
  `z • p`, `(1 - z) • p` of a collinear splitting returns `p`, and `.IsCollinearExactOn S` is the
  same property for the momenta `p` of a set `S` only.

Collinear exactness is what the scheme contributes to collinear safety. An observable that is
unchanged when a pair of parallel momenta is replaced by its merged pseudojet, which is what a
jet algorithm whose distance measure vanishes on parallel pairs delivers, is invariant under the
collinear splittings of every momentum on which the scheme is exact
(`RecombinationScheme.IsCollinearExactOn.apply_smul_cons_one_sub_smul_cons`), and collinear safe
when the scheme is exact on all of `V` (`RecombinationScheme.IsCollinearExact.isCollinearSafe`).
On the infrared side, for a scheme that leaves a pseudojet `a` unchanged when a vanishing momentum
is merged into it and is continuous there, an observable that is unchanged near `p = 0` when the
added momentum `p` is merged into `a`, and is continuous at `a`, absorbs a vanishingly soft
momentum added next to `a` (`RecombinationScheme.tendsto_cons_of_merge_zero`). With a unital
scheme continuous at a vanishing momentum, these hypotheses on the observable at every pseudojet,
and the corresponding limit at the empty final state, the observable is infrared safe
(`RecombinationScheme.IsUnital.isInfraredSafe`).

Additivity, homogeneity and symmetry do not by themselves give collinear exactness: on a
nontrivial `V`, `smulScheme V c`, which adds the momenta and rescales the sum by a fixed factor
`c ≠ 1`, has all three and merges a collinear pair into `c • p`
(`not_isCollinearExact_smulScheme`). What pins the `E` scheme down is
additivity together with the normalisation `IsUnital`, and those two characterise it exactly
(`RecombinationScheme.eq_eScheme_iff`). A scheme that is *not* additive can still be exact, and
`RecombinationScheme.IsPosHomogeneous.isCollinearExactOn_iff` isolates what it takes: a homogeneous
scheme is exact on a set closed under positive rescaling precisely when it merges parallel momenta
of that set additively. A scheme that rescales a merged pair to make it massless for a Minkowski
bilinear form `g` cannot be exact on all of `V`, but can be exact on the momenta with `g p p = 0`
(cf. `invariantMassSq`), a set closed under positive rescaling, which is what
`IsCollinearExactOn` and `RecombinationScheme.IsPosHomogeneous.isCollinearExactOn_iff` are for.

## References

* M. Cacciari, G. P. Salam and G. Soyez, *The anti-k_t jet clustering algorithm*,
  JHEP 04 (2008) 063, §1.
* G. P. Salam, *Towards jetography*, Eur. Phys. J. C 67 (2010) 637, §5.4.
-/

public section

namespace EpsilonEridani.QFT.Jets

open Filter Topology

variable {V X : Type*}

/-- A recombination scheme: the rule by which a jet algorithm merges two pseudojets into one.
The merged momentum does not depend on the order of the pair, because the pair a
sequential-recombination algorithm selects is unordered. -/
@[ext]
structure RecombinationScheme (V : Type*) where
  /-- The momentum of the pseudojet obtained by merging the pseudojets `a` and `b`. -/
  merge : V → V → V
  /-- The merged momentum does not depend on the order of the pair. -/
  merge_comm (a b : V) : merge a b = merge b a

namespace RecombinationScheme

section Additive

variable [AddCommMonoid V] (R : RecombinationScheme V)

/-- A scheme is *additive* if merging the sums of two pairs is the sum of the merged momenta. -/
def IsAdditive : Prop :=
  ∀ a₁ a₂ b₁ b₂ : V, R.merge (a₁ + a₂) (b₁ + b₂) = R.merge a₁ b₁ + R.merge a₂ b₂

variable {R}

theorem isAdditive_def :
    R.IsAdditive ↔ ∀ a₁ a₂ b₁ b₂ : V,
      R.merge (a₁ + a₂) (b₁ + b₂) = R.merge a₁ b₁ + R.merge a₂ b₂ :=
  Iff.rfl

/-- The defining property of an additive scheme: merging the sums of two pairs is the sum of the
merged momenta. -/
theorem IsAdditive.merge_add_add (hadd : R.IsAdditive) (a₁ a₂ b₁ b₂ : V) :
    R.merge (a₁ + a₂) (b₁ + b₂) = R.merge a₁ b₁ + R.merge a₂ b₂ :=
  hadd a₁ a₂ b₁ b₂

end Additive

section AdditiveCancel

variable [AddCancelCommMonoid V] {R : RecombinationScheme V}

/-- An additive scheme merges two vanishing momenta into a vanishing momentum. -/
theorem IsAdditive.merge_zero_zero (hadd : R.IsAdditive) : R.merge 0 0 = 0 := by
  simpa using hadd.merge_add_add 0 0 0 0

end AdditiveCancel

section AdditiveGroup

variable [AddCommGroup V] {R : RecombinationScheme V}

/-- An additive scheme merges the negatives of a pair into the negative of the merged momentum. -/
theorem IsAdditive.merge_neg_neg (hadd : R.IsAdditive) (a b : V) :
    R.merge (-a) (-b) = -R.merge a b := by
  have h := hadd.merge_add_add a (-a) b (-b)
  rw [add_neg_cancel, add_neg_cancel, hadd.merge_zero_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

end AdditiveGroup

section Unital

variable [Zero V] (R : RecombinationScheme V)

/-- A scheme is *unital* if merging a vanishing momentum into a pseudojet leaves it unchanged.
With `merge_comm` this makes `0` a two-sided identity for the merge, so a scheme that is not
unital changes the momentum of some pseudojet when an infinitely soft particle is merged into
it. -/
def IsUnital : Prop := ∀ a : V, R.merge a 0 = a

variable {R}

theorem isUnital_def : R.IsUnital ↔ ∀ a : V, R.merge a 0 = a :=
  Iff.rfl

theorem IsUnital.merge_zero (hR : R.IsUnital) (a : V) : R.merge a 0 = a :=
  hR a

theorem IsUnital.zero_merge (hR : R.IsUnital) (a : V) : R.merge 0 a = a := by
  rw [R.merge_comm, hR.merge_zero a]

end Unital

section Homogeneous

variable [AddCommGroup V] [Module ℝ V] (R : RecombinationScheme V)

/-- A scheme is *positively homogeneous of degree one* if rescaling both momenta of a pair by a
positive factor rescales the merged momentum by the same factor. -/
def IsPosHomogeneous : Prop :=
  ∀ c : ℝ, 0 < c → ∀ a b : V, R.merge (c • a) (c • b) = c • R.merge a b

/-- A scheme is *collinear exact* if merging the two fragments `z • p` and `(1 - z) • p` of a
collinear splitting returns the momentum `p` that was split. This is the property of a scheme
that a collinear-safety proof for a jet algorithm consumes. -/
def IsCollinearExact : Prop :=
  ∀ p : V, ∀ z ∈ Set.Icc (0 : ℝ) 1, R.merge (z • p) ((1 - z) • p) = p

/-- A scheme is *collinear exact on* a set `S` of momenta if the two fragments of a collinear
splitting of a member of `S` merge back into it. -/
def IsCollinearExactOn (S : Set V) : Prop :=
  ∀ p ∈ S, ∀ z ∈ Set.Icc (0 : ℝ) 1, R.merge (z • p) ((1 - z) • p) = p

variable {R}

/-- The second fragment of a collinear splitting is a rescaling of the first. -/
private theorem one_sub_smul_eq_div_smul_smul {z : ℝ} (hz : 0 < z) (p : V) :
    (1 - z) • p = ((1 - z) / z) • (z • p) := by
  match_scalars
  field_simp

theorem isPosHomogeneous_def :
    R.IsPosHomogeneous ↔ ∀ c : ℝ, 0 < c → ∀ a b : V, R.merge (c • a) (c • b) = c • R.merge a b :=
  Iff.rfl

/-- The defining property of a positively homogeneous scheme: rescaling both momenta of a pair by
a positive factor rescales the merged momentum by the same factor. -/
theorem IsPosHomogeneous.merge_smul_smul (hhom : R.IsPosHomogeneous) {c : ℝ} (hc : 0 < c)
    (a b : V) : R.merge (c • a) (c • b) = c • R.merge a b :=
  hhom c hc a b

theorem isCollinearExact_def :
    R.IsCollinearExact ↔ ∀ p : V, ∀ z ∈ Set.Icc (0 : ℝ) 1, R.merge (z • p) ((1 - z) • p) = p :=
  Iff.rfl

theorem isCollinearExactOn_def {S : Set V} :
    R.IsCollinearExactOn S ↔ ∀ p ∈ S, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      R.merge (z • p) ((1 - z) • p) = p :=
  Iff.rfl

/-- The defining property of a collinear exact scheme: the two fragments of a collinear splitting
merge back into the momentum that was split. -/
theorem IsCollinearExact.merge_smul_one_sub_smul (hR : R.IsCollinearExact) (p : V) (z : ℝ)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) : R.merge (z • p) ((1 - z) • p) = p :=
  hR p z hz

/-- The defining property of a scheme collinear exact on `S`: the two fragments of a collinear
splitting of a member of `S` merge back into it. -/
theorem IsCollinearExactOn.merge_smul_one_sub_smul {S : Set V} (hR : R.IsCollinearExactOn S)
    {p : V} (hp : p ∈ S) (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    R.merge (z • p) ((1 - z) • p) = p :=
  hR p hp z hz

/-- A scheme collinear exact on `S` leaves a member of `S` unchanged when a vanishing momentum is
merged into it. -/
theorem IsCollinearExactOn.merge_zero {S : Set V} (hR : R.IsCollinearExactOn S) {a : V}
    (ha : a ∈ S) : R.merge a 0 = a := by
  simpa using hR.merge_smul_one_sub_smul ha 1 ⟨zero_le_one, le_rfl⟩

/-- A collinear exact scheme is unital. -/
theorem IsCollinearExact.isUnital (hR : R.IsCollinearExact) : R.IsUnital := fun a => by
  simpa using hR.merge_smul_one_sub_smul a 1 ⟨zero_le_one, le_rfl⟩

/-- Collinear exactness on a set passes to its subsets. -/
theorem IsCollinearExactOn.mono {S T : Set V} (hST : S ⊆ T) (hR : R.IsCollinearExactOn T) :
    R.IsCollinearExactOn S :=
  fun _ hp => hR.merge_smul_one_sub_smul (hST hp)

/-- A collinear exact scheme is collinear exact on every set of momenta. -/
theorem IsCollinearExact.isCollinearExactOn (hR : R.IsCollinearExact) (S : Set V) :
    R.IsCollinearExactOn S :=
  fun p _ => hR.merge_smul_one_sub_smul p

/-- Collinear exactness is collinear exactness on the whole momentum space. -/
@[simp]
theorem isCollinearExactOn_univ : R.IsCollinearExactOn Set.univ ↔ R.IsCollinearExact :=
  ⟨fun h p => h.merge_smul_one_sub_smul (Set.mem_univ p), fun h => h.isCollinearExactOn _⟩

/-- Additivity and positive homogeneity of degree one together say exactly that the merge map is
an `ℝ`-linear map of the pair of momenta: additivity extends the positive homogeneity to negative
scalars. -/
theorem isLinearMap_uncurry_merge_iff :
    IsLinearMap ℝ (Function.uncurry R.merge) ↔ R.IsAdditive ∧ R.IsPosHomogeneous := by
  refine ⟨fun h => ⟨fun a₁ a₂ b₁ b₂ => by simpa using h.map_add (a₁, b₁) (a₂, b₂),
    fun c _ a b => by simpa using h.map_smul c (a, b)⟩,
    fun ⟨hadd, hhom⟩ => ?_⟩
  refine ⟨fun x y => hadd.merge_add_add x.1 y.1 x.2 y.2, fun c x => ?_⟩
  simp only [Function.uncurry_def, Prod.smul_fst, Prod.smul_snd]
  rcases lt_trichotomy 0 c with hc | rfl | hc
  · exact hhom.merge_smul_smul hc x.1 x.2
  · simp [hadd.merge_zero_zero]
  · calc R.merge (c • x.1) (c • x.2)
        = R.merge (-c • -x.1) (-c • -x.2) := by rw [neg_smul_neg, neg_smul_neg]
      _ = -c • R.merge (-x.1) (-x.2) := hhom.merge_smul_smul (by linarith) _ _
      _ = -c • -R.merge x.1 x.2 := by rw [hadd.merge_neg_neg]
      _ = c • R.merge x.1 x.2 := neg_smul_neg c _

/-- On a set closed under positive rescaling, a scheme collinear exact there merges parallel
momenta of the set additively. -/
theorem IsCollinearExactOn.merge_smul_eq_one_add_smul {S : Set V}
    (hS : ∀ c : ℝ, 0 < c → ∀ p ∈ S, c • p ∈ S) (hR : R.IsCollinearExactOn S) {t : ℝ} (ht : 0 ≤ t)
    {p : V} (hp : p ∈ S) : R.merge p (t • p) = (1 + t) • p := by
  have ht1 : (0 : ℝ) < 1 + t := by linarith
  have hz := hR.merge_smul_one_sub_smul (hS _ ht1 p hp) (1 + t)⁻¹
    ⟨inv_nonneg.2 ht1.le, inv_le_one_of_one_le₀ (by linarith)⟩
  have hdiv : (1 - (1 + t)⁻¹) / (1 + t)⁻¹ = t := by field_simp; ring
  rwa [one_sub_smul_eq_div_smul_smul (inv_pos.2 ht1), inv_smul_smul₀ ht1.ne', hdiv] at hz

/-- A positively homogeneous scheme that merges parallel momenta of a set `S` additively is
collinear exact on `S`. -/
theorem IsPosHomogeneous.isCollinearExactOn_of_merge_smul (hhom : R.IsPosHomogeneous)
    {S : Set V} (hpar : ∀ t : ℝ, 0 ≤ t → ∀ p ∈ S, R.merge p (t • p) = (1 + t) • p) :
    R.IsCollinearExactOn S := by
  intro p hp z hz
  obtain ⟨hz0, hz1⟩ := hz
  rcases hz0.eq_or_lt with rfl | hzpos
  · have h0 := hpar 0 le_rfl p hp
    simp only [zero_smul, add_zero, one_smul] at h0
    simpa [R.merge_comm 0 p] using h0
  · have hmul : z * (1 + (1 - z) / z) = 1 := by field_simp; ring
    rw [one_sub_smul_eq_div_smul_smul hzpos, smul_comm ((1 - z) / z) z p,
      hhom.merge_smul_smul hzpos, hpar ((1 - z) / z) (div_nonneg (by linarith) hz0) p hp,
      smul_smul, hmul, one_smul]

/-- A positively homogeneous scheme is collinear exact on a set closed under positive rescaling
exactly when it merges parallel momenta of that set additively. This is the criterion a scheme
that is not additive has to meet. -/
theorem IsPosHomogeneous.isCollinearExactOn_iff (hhom : R.IsPosHomogeneous) {S : Set V}
    (hS : ∀ c : ℝ, 0 < c → ∀ p ∈ S, c • p ∈ S) :
    R.IsCollinearExactOn S ↔ ∀ t : ℝ, 0 ≤ t → ∀ p ∈ S, R.merge p (t • p) = (1 + t) • p :=
  ⟨fun hR _ ht _ hp => hR.merge_smul_eq_one_add_smul hS ht hp,
    hhom.isCollinearExactOn_of_merge_smul⟩

/-- A positively homogeneous scheme is collinear exact exactly when it merges parallel momenta
additively. -/
theorem IsPosHomogeneous.isCollinearExact_iff (hhom : R.IsPosHomogeneous) :
    R.IsCollinearExact ↔ ∀ t : ℝ, 0 ≤ t → ∀ p : V, R.merge p (t • p) = (1 + t) • p := by
  rw [← isCollinearExactOn_univ, hhom.isCollinearExactOn_iff fun _ _ _ _ => Set.mem_univ _]
  simp

end Homogeneous

end RecombinationScheme

/-! ### The `E` scheme -/

variable (V) in
/-- The `E` scheme: two pseudojets are merged by adding their momenta. -/
def eScheme [AddCommMonoid V] : RecombinationScheme V where
  merge := (· + ·)
  merge_comm := add_comm

@[simp]
theorem eScheme_merge [AddCommMonoid V] (a b : V) : (eScheme V).merge a b = a + b := (rfl)

/-- Merging a fixed pseudojet by the `E` scheme is continuous in the other momentum. -/
theorem continuous_eScheme_merge [AddCommMonoid V] [TopologicalSpace V] [ContinuousAdd V]
    (a : V) : Continuous ((eScheme V).merge a) :=
  continuous_const_add a

section EScheme

variable [AddCommMonoid V]

/-- The `E` scheme is additive. -/
theorem isAdditive_eScheme : (eScheme V).IsAdditive := fun a₁ a₂ b₁ b₂ => by
  simp only [eScheme_merge]
  abel

/-- The `E` scheme is unital: a vanishing momentum merges into nothing. -/
theorem isUnital_eScheme : (eScheme V).IsUnital := fun a => by simp

end EScheme

section ESchemeModule

variable [AddCommGroup V] [Module ℝ V]

/-- The `E` scheme is positively homogeneous of degree one. -/
theorem isPosHomogeneous_eScheme : (eScheme V).IsPosHomogeneous := fun c _ a b => by
  simp [smul_add]

/-- The `E` scheme is collinear exact: the two fragments of a collinear splitting add back up to
the momentum that was split. -/
theorem isCollinearExact_eScheme : (eScheme V).IsCollinearExact := fun p z _ => by
  simp [smul_add_one_sub_smul]

end ESchemeModule

namespace RecombinationScheme

section Rigidity

variable [AddCommMonoid V] {R : RecombinationScheme V}

/-- An additive unital scheme merges by adding momenta. -/
theorem IsAdditive.merge_eq_add_of_isUnital (hadd : R.IsAdditive) (hunit : R.IsUnital)
    (a b : V) : R.merge a b = a + b := by
  have h := hadd.merge_add_add a 0 0 b
  rwa [add_zero, zero_add, hunit a, hunit.zero_merge b] at h

/-- The `E` scheme is the only additive unital scheme. -/
theorem IsAdditive.eq_eScheme_of_isUnital (hadd : R.IsAdditive) (hunit : R.IsUnital) :
    R = eScheme V := by
  ext a b
  exact hadd.merge_eq_add_of_isUnital hunit a b

/-- Additivity and the normalisation that a vanishing momentum merges into nothing characterise
the `E` scheme. -/
theorem eq_eScheme_iff : R = eScheme V ↔ R.IsAdditive ∧ R.IsUnital :=
  ⟨by rintro rfl; exact ⟨isAdditive_eScheme, isUnital_eScheme⟩,
    fun h => h.1.eq_eScheme_of_isUnital h.2⟩

end Rigidity

section RigidityModule

variable [AddCommGroup V] [Module ℝ V] {R : RecombinationScheme V}

/-- An additive unital scheme is collinear exact. -/
theorem IsAdditive.isCollinearExact_of_isUnital (hadd : R.IsAdditive) (hunit : R.IsUnital) :
    R.IsCollinearExact := by
  rw [hadd.eq_eScheme_of_isUnital hunit]
  exact isCollinearExact_eScheme

end RigidityModule

end RecombinationScheme

/-! ### A scheme that is additive, homogeneous and symmetric but not exact -/

section SmulScheme

variable [AddCommGroup V] [Module ℝ V]

variable (V) in
/-- The scheme that adds the momenta of a pair and rescales the sum by a fixed factor `c`.
It is additive, positively homogeneous of degree one and symmetric, and for `c ≠ 1` on a
nontrivial `V` it is not collinear exact, so those three conditions alone do not give collinear
exactness. -/
def smulScheme (c : ℝ) : RecombinationScheme V where
  merge a b := c • (a + b)
  merge_comm a b := by rw [add_comm a b]

@[simp]
theorem smulScheme_merge (c : ℝ) (a b : V) : (smulScheme V c).merge a b = c • (a + b) := (rfl)

/-- Rescaling by one is the `E` scheme. -/
@[simp]
theorem smulScheme_one : smulScheme V 1 = eScheme V := by
  ext a b
  simp

/-- Rescaling the sum by a fixed factor is additive. -/
theorem isAdditive_smulScheme (c : ℝ) : (smulScheme V c).IsAdditive := fun a₁ a₂ b₁ b₂ => by
  simp only [smulScheme_merge]
  module

/-- Rescaling the sum by a fixed factor is positively homogeneous of degree one. -/
theorem isPosHomogeneous_smulScheme (c : ℝ) : (smulScheme V c).IsPosHomogeneous :=
    fun d _ a b => by
  simp only [smulScheme_merge, ← smul_add]
  exact smul_comm c d (a + b)

/-- Rescaling by a factor other than one merges a collinear pair into the wrong momentum, so the
scheme is not collinear exact although it is additive, homogeneous and symmetric. -/
theorem not_isCollinearExact_smulScheme [Nontrivial V] {c : ℝ} (hc : c ≠ 1) :
    ¬ (smulScheme V c).IsCollinearExact := by
  intro hR
  obtain ⟨p, hp⟩ := exists_ne (0 : V)
  have h : c • p = p := by
    simpa using hR.merge_smul_one_sub_smul p 0 ⟨le_rfl, zero_le_one⟩
  have hsub : (c - 1) • p = 0 := by rw [sub_smul, one_smul, h, sub_self]
  exact hp ((smul_eq_zero.1 hsub).resolve_left (sub_ne_zero.2 hc))

/-- Rescaling by a factor other than one is not unital: a vanishing momentum does not merge into
nothing. -/
theorem not_isUnital_smulScheme [Nontrivial V] {c : ℝ} (hc : c ≠ 1) :
    ¬ (smulScheme V c).IsUnital := fun hunit =>
  not_isCollinearExact_smulScheme hc
    ((isAdditive_smulScheme c).isCollinearExact_of_isUnital hunit)

end SmulScheme

/-! ### Safety of the observables built from the merged pseudojets -/

section CollinearSafety

variable [AddCommGroup V] [Module ℝ V] {R : RecombinationScheme V}

/-- An observable that is unchanged when a pair of parallel momenta `a`, `t • a` is replaced by
its merged pseudojet is invariant under the collinear splittings of every momentum on which the
scheme is collinear exact. -/
theorem RecombinationScheme.IsCollinearExactOn.apply_smul_cons_one_sub_smul_cons {S : Set V}
    (hR : R.IsCollinearExactOn S) {J : Multiset V → X}
    (hJ : ∀ (s : Multiset V) (a : V) (t : ℝ), 0 ≤ t →
      J (a ::ₘ t • a ::ₘ s) = J (R.merge a (t • a) ::ₘ s))
    (s : Multiset V) {p : V} (hp : p ∈ S) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    J (z • p ::ₘ (1 - z) • p ::ₘ s) = J (p ::ₘ s) := by
  obtain ⟨hz0, hz1⟩ := hz
  rcases hz0.eq_or_lt with rfl | hzpos
  · rw [zero_smul, sub_zero, one_smul, Multiset.cons_swap, ← zero_smul ℝ p, hJ s p 0 le_rfl,
      zero_smul, hR.merge_zero hp]
  · rw [one_sub_smul_eq_div_smul_smul hzpos, hJ s _ _ (div_nonneg (by linarith) hz0),
      ← one_sub_smul_eq_div_smul_smul hzpos, hR.merge_smul_one_sub_smul hp z ⟨hz0, hz1⟩]

/-- For a collinear exact scheme, an observable that is unchanged when a pair of parallel momenta
is replaced by its merged pseudojet is collinear safe. -/
theorem RecombinationScheme.IsCollinearExact.isCollinearSafe (hR : R.IsCollinearExact)
    {J : Multiset V → X}
    (hJ : ∀ (s : Multiset V) (a : V) (t : ℝ), 0 ≤ t →
      J (a ::ₘ t • a ::ₘ s) = J (R.merge a (t • a) ::ₘ s)) :
    IsCollinearSafe J :=
  isCollinearSafe_def.2 fun s p _ hz =>
    (hR.isCollinearExactOn Set.univ).apply_smul_cons_one_sub_smul_cons hJ s (Set.mem_univ p) hz

end CollinearSafety

section InfraredSafety

variable [Zero V] {R : RecombinationScheme V}

/-- An observable `J` that is unchanged near `p = 0` when the added momentum `p` of the final state
`p ::ₘ a ::ₘ t` is merged into the pseudojet `a` tends to `J (a ::ₘ t)` as `p` tends to `0`, for a
scheme that leaves `a` unchanged when a vanishing momentum is merged into it and whose merge map
is continuous there. The hypothesis `hJ` is required only near `p = 0`, and the continuity of `J`
only at `a`, so an observable that jumps elsewhere is covered at the states away from the jump.
This is infrared safety at the states that have a pseudojet to merge into; the empty final state
has none. -/
theorem RecombinationScheme.tendsto_cons_of_merge_zero [TopologicalSpace V] [TopologicalSpace X]
    {J : Multiset V → X} {a : V} {t : Multiset V} (hR : R.merge a 0 = a)
    (hRc : ContinuousAt (R.merge a) 0) (hJc : ContinuousAt (fun v : V => J (v ::ₘ t)) a)
    (hJ : ∀ᶠ p : V in 𝓝 0, J (p ::ₘ a ::ₘ t) = J (R.merge a p ::ₘ t)) :
    Tendsto (fun p : V => J (p ::ₘ a ::ₘ t)) (𝓝 0) (𝓝 (J (a ::ₘ t))) := by
  refine Tendsto.congr' (hJ.mono fun p hp => hp.symm) ?_
  simpa [Function.comp_def, hR] using (hJc.comp_of_eq hRc hR).tendsto

/-- For a unital scheme whose merge map is continuous at a vanishing momentum, an observable that
is unchanged near `p = 0` when an added momentum `p` is merged into a pseudojet, that is continuous
in the pseudojet it is merged into, and that absorbs a vanishingly soft momentum added to the empty
final state, is infrared safe. -/
theorem RecombinationScheme.IsUnital.isInfraredSafe [TopologicalSpace V] [TopologicalSpace X]
    (hR : R.IsUnital) (hRc : ∀ a : V, ContinuousAt (R.merge a) 0) {J : Multiset V → X}
    (hJc : ∀ (a : V) (t : Multiset V), ContinuousAt (fun v : V => J (v ::ₘ t)) a)
    (hJ : ∀ (a : V) (t : Multiset V), ∀ᶠ p : V in 𝓝 0, J (p ::ₘ a ::ₘ t) = J (R.merge a p ::ₘ t))
    (h0 : Tendsto (fun p : V => J (p ::ₘ 0)) (𝓝 0) (𝓝 (J 0))) : IsInfraredSafe J := by
  refine isInfraredSafe_def.2 fun s => ?_
  induction s using Multiset.induction_on with
  | empty => exact h0
  | cons a t _ =>
    exact RecombinationScheme.tendsto_cons_of_merge_zero (hR.merge_zero a) (hRc a) (hJc a t)
      (hJ a t)

end InfraredSafety

end EpsilonEridani.QFT.Jets
