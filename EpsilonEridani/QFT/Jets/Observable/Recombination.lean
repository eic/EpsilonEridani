/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Jets.Observable.Basic

/-!
# Recombination schemes

A sequential-recombination jet algorithm repeatedly replaces a pair of pseudojets by a single
one. The rule it uses to do so is a *recombination scheme*: a symmetric map `V → V → V` on the
momentum space. This file defines the schemes, the conditions a scheme can satisfy, and the
property of a scheme that a safety proof for an algorithm consumes.

* `RecombinationScheme V` carries the merge map and its symmetry, symmetry being structural
  because the pair an algorithm selects is unordered.
* `eScheme V` is the `E` scheme, which merges by adding momenta; the merged pseudojet is massive
  even when its constituents are massless.
* `RecombinationScheme.IsAdditive`, `.IsHomogeneous` and `.IsUnital` are additivity of the merge
  map in the pair, positive homogeneity of degree one, and the normalisation that merging a
  vanishing momentum changes nothing. Additivity and homogeneity together say exactly that the
  merge map is `ℝ`-linear on the pair (`RecombinationScheme.isLinearMap_uncurry_iff`).
* `RecombinationScheme.IsCollinearExact` is the property that merging the two fragments
  `z • p`, `(1 - z) • p` of a collinear splitting returns `p`, and `.IsCollinearExactOn S` is the
  same property for the momenta `p` of a set `S` only.

Collinear exactness is what reduces the safety of a clustering to the behaviour of the clustering
itself: for an exact scheme, a clustering is collinear safe exactly when it treats a collinear
pair as the merged pseudojet (`RecombinationScheme.IsCollinearExact.isCollinearSafe_iff`), which
is what a distance measure vanishing on collinear pairs has to deliver, and a unital scheme
continuous at `0` absorbs a vanishingly soft momentum
(`RecombinationScheme.IsUnital.tendsto_cons`).

Additivity, homogeneity and symmetry do not by themselves give collinear exactness: `smulScheme`,
which adds the momenta and rescales the sum by a fixed factor `c`, has all three and merges a
collinear pair into `c • p` (`not_isCollinearExact_smulScheme`). What pins the `E` scheme down is
additivity together with the normalisation `IsUnital`, and those two characterise it exactly
(`RecombinationScheme.eq_eScheme_iff`). A scheme that is *not* additive can still be exact, and
`RecombinationScheme.IsHomogeneous.isCollinearExactOn_iff` isolates what it takes: a homogeneous
scheme is exact on a set closed under positive rescaling precisely when it merges parallel momenta
of that set additively. The schemes rescaling a merged pair to make it massless with respect to a
frame are not exact on all of `V`, since they rescale the sum of a massive pair, and the set is
what lets them meet the criterion: on the massless momenta, two parallel momenta sum to a massless
momentum and nothing is rescaled. Those schemes are frame-dependent data and are stated where the
frame is, not here.

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

variable [AddCommGroup V] (R : RecombinationScheme V)

/-- A scheme is *additive* if merging the sums of two pairs is the sum of the merged momenta. -/
def IsAdditive : Prop :=
  ∀ a₁ a₂ b₁ b₂ : V, R.merge (a₁ + a₂) (b₁ + b₂) = R.merge a₁ b₁ + R.merge a₂ b₂

/-- A scheme is *unital* if merging a vanishing momentum into a pseudojet leaves it unchanged.
With `merge_comm` this makes `0` a two-sided identity for the merge, so a scheme that is not
unital manufactures momentum out of an infinitely soft particle. -/
def IsUnital : Prop := ∀ a : V, R.merge a 0 = a

variable {R}

theorem isAdditive_def :
    R.IsAdditive ↔ ∀ a₁ a₂ b₁ b₂ : V,
      R.merge (a₁ + a₂) (b₁ + b₂) = R.merge a₁ b₁ + R.merge a₂ b₂ :=
  Iff.rfl

theorem isUnital_def : R.IsUnital ↔ ∀ a : V, R.merge a 0 = a :=
  Iff.rfl

theorem IsUnital.merge_zero (hR : R.IsUnital) (a : V) : R.merge a 0 = a :=
  hR a

theorem IsUnital.zero_merge (hR : R.IsUnital) (a : V) : R.merge 0 a = a := by
  rw [R.merge_comm, hR.merge_zero a]

end Additive

section Homogeneous

variable [AddCommGroup V] [Module ℝ V] (R : RecombinationScheme V)

/-- A scheme is *positively homogeneous of degree one* if rescaling both momenta of a pair by a
nonnegative factor rescales the merged momentum by the same factor. -/
def IsHomogeneous : Prop :=
  ∀ c : ℝ, 0 ≤ c → ∀ a b : V, R.merge (c • a) (c • b) = c • R.merge a b

/-- A scheme is *collinear exact* if merging the two fragments `z • p` and `(1 - z) • p` of a
collinear splitting returns the momentum `p` that was split. This is the property of a scheme
that a collinear-safety proof for a jet algorithm consumes. -/
def IsCollinearExact : Prop :=
  ∀ p : V, ∀ z ∈ Set.Icc (0 : ℝ) 1, R.merge (z • p) ((1 - z) • p) = p

/-- A scheme is *collinear exact on* a set `S` of momenta if the two fragments of a collinear
splitting of a member of `S` merge back into it. A scheme that rescales a merged pair to make it
massless can only have this for a set of massless momenta, not on all of `V`. -/
def IsCollinearExactOn (S : Set V) : Prop :=
  ∀ p ∈ S, ∀ z ∈ Set.Icc (0 : ℝ) 1, R.merge (z • p) ((1 - z) • p) = p

variable {R}

theorem isHomogeneous_def :
    R.IsHomogeneous ↔ ∀ c : ℝ, 0 ≤ c → ∀ a b : V, R.merge (c • a) (c • b) = c • R.merge a b :=
  Iff.rfl

theorem isCollinearExact_def :
    R.IsCollinearExact ↔ ∀ p : V, ∀ z ∈ Set.Icc (0 : ℝ) 1, R.merge (z • p) ((1 - z) • p) = p :=
  Iff.rfl

theorem isCollinearExactOn_def {S : Set V} :
    R.IsCollinearExactOn S ↔ ∀ p ∈ S, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      R.merge (z • p) ((1 - z) • p) = p :=
  Iff.rfl

/-- Collinear exactness is collinear exactness on the whole momentum space. -/
theorem isCollinearExactOn_univ : R.IsCollinearExactOn Set.univ ↔ R.IsCollinearExact :=
  ⟨fun h p => h p (Set.mem_univ p), fun h p _ => h p⟩

/-- The defining property of a collinear exact scheme: the two fragments of a collinear splitting
merge back into the momentum that was split. -/
theorem IsCollinearExact.merge_smul_one_sub_smul (hR : R.IsCollinearExact) (p : V) (z : ℝ)
    (hz : z ∈ Set.Icc (0 : ℝ) 1) : R.merge (z • p) ((1 - z) • p) = p :=
  hR p z hz

/-- Additivity and positive homogeneity of degree one together say exactly that the merge map is
an `ℝ`-linear map of the pair of momenta: additivity already forces homogeneity at negative
scalars. -/
theorem isLinearMap_uncurry_iff :
    IsLinearMap ℝ (fun x : V × V => R.merge x.1 x.2) ↔ R.IsAdditive ∧ R.IsHomogeneous := by
  refine ⟨fun h => ⟨fun a₁ a₂ b₁ b₂ => by simpa using h.map_add (a₁, b₁) (a₂, b₂),
    fun c _ a b => by simpa using h.map_smul c (a, b)⟩,
    fun ⟨hadd, hhom⟩ => ?_⟩
  let f : V × V →+ V := AddMonoidHom.mk' (fun x => R.merge x.1 x.2) fun x y => by
    simpa using hadd x.1 y.1 x.2 y.2
  refine ⟨f.map_add, fun c x => ?_⟩
  simp only [Prod.smul_fst, Prod.smul_snd]
  rcases le_or_gt 0 c with hc | hc
  · exact hhom c hc x.1 x.2
  · calc R.merge (c • x.1) (c • x.2)
        = R.merge (-c • -x.1) (-c • -x.2) := by rw [neg_smul_neg, neg_smul_neg]
      _ = -c • R.merge (-x.1) (-x.2) := hhom (-c) (by linarith) _ _
      _ = -c • -R.merge x.1 x.2 := congrArg _ (f.map_neg x)
      _ = c • R.merge x.1 x.2 := by rw [smul_neg, neg_smul, neg_neg]

/-- A positively homogeneous scheme is collinear exact on a set closed under positive rescaling
exactly when it merges parallel momenta of that set additively. This is the criterion a scheme
that is not additive has to meet, and a scheme that rescales a merged pair to make it massless
with respect to a frame meets it on the massless momenta: two parallel massless momenta already
sum to a massless momentum, so no rescaling occurs there. -/
theorem IsHomogeneous.isCollinearExactOn_iff (hhom : R.IsHomogeneous) {S : Set V}
    (hS : ∀ c : ℝ, 0 < c → ∀ p ∈ S, c • p ∈ S) :
    R.IsCollinearExactOn S ↔ ∀ t : ℝ, 0 ≤ t → ∀ p ∈ S, R.merge p (t • p) = (1 + t) • p := by
  constructor
  · intro hR t ht p hp
    have ht1 : (0 : ℝ) < 1 + t := by linarith
    have ht1' : (1 + t) ≠ 0 := ht1.ne'
    have hz := hR ((1 + t) • p) (hS _ ht1 p hp) (1 + t)⁻¹
      ⟨inv_nonneg.2 ht1.le, inv_le_one_of_one_le₀ (by linarith)⟩
    have hmul : (1 - (1 + t)⁻¹) * (1 + t) = t := by field_simp; ring
    rwa [inv_smul_smul₀ ht1', smul_smul, hmul] at hz
  · intro hpar p hp z hz
    obtain ⟨hz0, hz1⟩ := hz
    rcases hz0.eq_or_lt with rfl | hzpos
    · have h0 := hpar 0 le_rfl p hp
      simp only [zero_smul, add_zero, one_smul] at h0
      simpa [R.merge_comm 0 p] using h0
    · have hzne : z ≠ 0 := hzpos.ne'
      have hsplit : (1 - z) • p = z • (((1 - z) / z) • p) := by
        rw [smul_smul]
        congr 1
        field_simp
      have hmul : z * (1 + (1 - z) / z) = 1 := by field_simp; ring
      rw [hsplit, hhom z hz0, hpar ((1 - z) / z) (div_nonneg (by linarith) hz0) p hp, smul_smul,
        hmul, one_smul]

/-- A positively homogeneous scheme is collinear exact exactly when it merges parallel momenta
additively. -/
theorem IsHomogeneous.isCollinearExact_iff (hhom : R.IsHomogeneous) :
    R.IsCollinearExact ↔ ∀ t : ℝ, 0 ≤ t → ∀ p : V, R.merge p (t • p) = (1 + t) • p := by
  rw [← isCollinearExactOn_univ, hhom.isCollinearExactOn_iff fun _ _ _ _ => Set.mem_univ _]
  simp

end Homogeneous

end RecombinationScheme

/-! ### The `E` scheme -/

variable (V) in
/-- The `E` scheme: two pseudojets are merged by adding their momenta. The merged pseudojet is
massive even when both of its constituents are massless, which is why a scheme that rescales to
restore masslessness is a different scheme and inherits none of the theorems proved here. -/
@[expose] def eScheme [AddCommMonoid V] : RecombinationScheme V where
  merge := (· + ·)
  merge_comm := add_comm

@[simp]
theorem eScheme_merge [AddCommMonoid V] (a b : V) : (eScheme V).merge a b = a + b := (rfl)

section EScheme

variable [AddCommGroup V]

/-- The `E` scheme is additive. -/
theorem isAdditive_eScheme : (eScheme V).IsAdditive := fun a₁ a₂ b₁ b₂ => by
  simp only [eScheme_merge]
  abel

/-- The `E` scheme is unital: a vanishing momentum merges into nothing. -/
theorem isUnital_eScheme : (eScheme V).IsUnital := fun a => by simp

variable [Module ℝ V]

/-- The `E` scheme is positively homogeneous of degree one. -/
theorem isHomogeneous_eScheme : (eScheme V).IsHomogeneous := fun c _ a b => by simp [smul_add]

/-- The `E` scheme is collinear exact: the two fragments of a collinear splitting add back up to
the momentum that was split. -/
theorem isCollinearExact_eScheme : (eScheme V).IsCollinearExact := fun p z _ => by
  simp [smul_add_one_sub_smul]

end EScheme

namespace RecombinationScheme

section Rigidity

variable [AddCommGroup V] {R : RecombinationScheme V}

/-- An additive unital scheme merges by adding momenta. -/
theorem IsAdditive.merge_eq_add (hadd : R.IsAdditive) (hunit : R.IsUnital) (a b : V) :
    R.merge a b = a + b := by
  have h := hadd a 0 0 b
  rwa [add_zero, zero_add, hunit a, hunit.zero_merge b] at h

/-- The `E` scheme is the only additive unital scheme. -/
theorem IsAdditive.eq_eScheme (hadd : R.IsAdditive) (hunit : R.IsUnital) : R = eScheme V := by
  ext a b
  exact hadd.merge_eq_add hunit a b

/-- Additivity and the normalisation that a vanishing momentum merges into nothing characterise
the `E` scheme. -/
theorem eq_eScheme_iff : R = eScheme V ↔ R.IsAdditive ∧ R.IsUnital :=
  ⟨by rintro rfl; exact ⟨isAdditive_eScheme, isUnital_eScheme⟩, fun h => h.1.eq_eScheme h.2⟩

variable [Module ℝ V]

/-- An additive unital scheme is collinear exact. -/
theorem IsAdditive.isCollinearExact (hadd : R.IsAdditive) (hunit : R.IsUnital) :
    R.IsCollinearExact := by
  rw [hadd.eq_eScheme hunit]
  exact isCollinearExact_eScheme

end Rigidity

end RecombinationScheme

/-! ### A scheme that is additive, homogeneous and symmetric but not exact -/

section SmulScheme

variable [AddCommGroup V] [Module ℝ V]

variable (V) in
/-- The scheme that adds the momenta of a pair and rescales the sum by a fixed factor `c`.
For `c ≠ 1` it is additive, positively homogeneous of degree one and symmetric and still not
collinear exact, so those three conditions alone do not make the observables built from the
merged pseudojets safe. -/
def smulScheme (c : ℝ) : RecombinationScheme V where
  merge a b := c • (a + b)
  merge_comm a b := by rw [add_comm]

@[simp]
theorem smulScheme_merge (c : ℝ) (a b : V) : (smulScheme V c).merge a b = c • (a + b) := (rfl)

/-- Rescaling by one is the `E` scheme. -/
@[simp]
theorem smulScheme_one : smulScheme V 1 = eScheme V := by
  ext a b
  simp

/-- Rescaling the sum by a fixed factor is additive. -/
theorem isAdditive_smulScheme (c : ℝ) : (smulScheme V c).IsAdditive := fun a₁ a₂ b₁ b₂ => by
  simp only [smulScheme_merge, ← smul_add]
  congr 1
  abel

/-- Rescaling the sum by a fixed factor is positively homogeneous of degree one. -/
theorem isHomogeneous_smulScheme (c : ℝ) : (smulScheme V c).IsHomogeneous := fun d _ a b => by
  simp only [smulScheme_merge, ← smul_add, smul_smul, mul_comm]

/-- Rescaling by a factor other than one merges a collinear pair into the wrong momentum, so the
scheme is not collinear exact although it is additive, homogeneous and symmetric. -/
theorem not_isCollinearExact_smulScheme [Nontrivial V] {c : ℝ} (hc : c ≠ 1) :
    ¬ (smulScheme V c).IsCollinearExact := by
  intro hR
  obtain ⟨p, hp⟩ := exists_ne (0 : V)
  have h : c • p = p := by
    simpa using hR.merge_smul_one_sub_smul p 0 ⟨le_rfl, zero_le_one⟩
  have hsub : (c - 1) • p = 0 := by rw [sub_smul, one_smul, h, sub_self]
  refine hp ?_
  have := congrArg (fun v : V => (c - 1)⁻¹ • v) hsub
  simpa [inv_smul_smul₀ (sub_ne_zero.2 hc)] using this

/-- The rescaling scheme is not unital, which by `RecombinationScheme.eq_eScheme_iff` is the only
one of the conditions it can fail, being additive. -/
theorem not_isUnital_smulScheme [Nontrivial V] {c : ℝ} (hc : c ≠ 1) :
    ¬ (smulScheme V c).IsUnital := fun hunit =>
  not_isCollinearExact_smulScheme hc ((isAdditive_smulScheme c).isCollinearExact hunit)

end SmulScheme

/-! ### Safety of the observables built from the merged pseudojets -/

section CollinearSafety

variable [AddCommGroup V] [Module ℝ V] {R : RecombinationScheme V}

/-- For a collinear exact scheme, a clustering is collinear safe exactly when it gives the same
output on the pair produced by a collinear splitting as on the merged pseudojet: the merged pair
is the momentum that was split. This proves nothing about a clustering by itself; it isolates what
a clustering has to deliver, which is what a distance measure vanishing on collinear pairs is for,
and the scheme contributes only the exactness. Every observable of a safe clustering is then
collinear safe by `IsCollinearSafe.map`. -/
theorem RecombinationScheme.IsCollinearExact.isCollinearSafe_iff (hR : R.IsCollinearExact)
    {J : Multiset V → X} :
    IsCollinearSafe J ↔ ∀ p : V, ∀ z ∈ Set.Icc (0 : ℝ) 1, ∀ s : Multiset V,
      J (z • p ::ₘ (1 - z) • p ::ₘ s) = J (R.merge (z • p) ((1 - z) • p) ::ₘ s) :=
  isCollinearSafe_def.trans
    ⟨fun h p z hz s => by rw [hR.merge_smul_one_sub_smul p z hz, h s p z hz],
      fun h s p z hz => by rw [h p z hz s, hR.merge_smul_one_sub_smul p z hz]⟩

end CollinearSafety

section InfraredSafety

variable [AddCommGroup V] {R : RecombinationScheme V}

/-- A clustering that merges a soft enough added momentum into the pseudojet `a` of the final
state `a ::ₘ t` absorbs it in the limit, for a unital scheme whose merge map is continuous at `0`:
the merged pseudojet tends to `a` itself. The hypothesis `hJ` is required only near `p = 0`, which
is all a distance measure delivers — a hard momentum need not cluster with `a` at all — and the
continuity of `J` only at `a`, so an observable that jumps elsewhere, as jet multiplicity does at
a tie, is covered at the states away from the jump. This is infrared safety at the states that
have a pseudojet to merge into; the empty final state has none, and there no scheme can supply the
hypothesis. -/
theorem RecombinationScheme.IsUnital.tendsto_cons [TopologicalSpace V] [TopologicalSpace X]
    (hR : R.IsUnital) {J : Multiset V → X} {a : V} {t : Multiset V}
    (hRc : ContinuousAt (R.merge a) 0) (hJc : ContinuousAt (fun v : V => J (v ::ₘ t)) a)
    (hJ : ∀ᶠ p : V in 𝓝 0, J (p ::ₘ a ::ₘ t) = J (R.merge a p ::ₘ t)) :
    Tendsto (fun p : V => J (p ::ₘ a ::ₘ t)) (𝓝 0) (𝓝 (J (a ::ₘ t))) := by
  have h0 : J (R.merge a 0 ::ₘ t) = J (a ::ₘ t) := by rw [hR.merge_zero a]
  rw [← h0]
  refine Tendsto.congr' (hJ.mono fun p hp => hp.symm) ?_
  simpa [Function.comp_def, hR.merge_zero a] using (hJc.comp_of_eq hRc (hR.merge_zero a)).tendsto

end InfraredSafety

end EpsilonEridani.QFT.Jets
