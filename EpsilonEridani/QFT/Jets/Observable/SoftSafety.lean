/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Normed.Operator.Asymptotics
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import EpsilonEridani.QFT.Jets.Observable.Counterexamples

/-!
# Soft safety of a given order

Infrared safety (`IsInfraredSafe`) asks only that adding a momentum `p` to a final state and
letting `p → 0` recover the value on the original state; it says nothing about how fast. The
quantitative version used in the literature asks for a rate: an observable `O` is *soft safe of
order `k`* (`IsSoftSafe k O`) if, for every final state `s`,

`O (p ::ₘ s) - O s = O(‖p‖ ^ k)` as `p → 0`,

in the sense of Mathlib's `Asymptotics.IsBigO`. Momenta live in a seminormed group `V`. When `V`
is a finite-dimensional real normed space all norms on it are equivalent, so the condition does not
depend on the norm chosen; for a general seminormed `V` it depends on the seminorm. Observables
may take values in any seminormed group, so the vector-valued total momentum is covered by the
same definition.

## Main results

* `IsSoftSafe.isInfraredSafe`: soft safety of a positive order implies infrared safety.
* `IsSoftSafe.of_le`: soft safety of order `k` implies soft safety of every lower order.
* `isSoftSafe_const`, `IsSoftSafe.add`, `IsSoftSafe.neg`, `IsSoftSafe.sub`: closure under the
  additive operations, and `IsSoftSafe.map₂`, with its instances `IsSoftSafe.bilinear` and
  `IsSoftSafe.mul`: closure under a bounded biadditive map, such as a continuous bilinear map or
  multiplication.
* `isSoftSafe_sum_map_iff`: a sum `∑_{q ∈ s} f q` over the particles is soft safe of order `k`
  exactly when `f p = O(‖p‖ ^ k)` as `p → 0`. Consequently the total momentum
  (`isSoftSafe_one_multisetSum`) and every sum of a continuous linear function of the momenta,
  such as the total energy in a frame (`isSoftSafe_one_sum_map`), are soft safe of order `1`, and
  so is the square `B P P` of the total momentum `P` under a continuous bilinear form `B`
  (`isSoftSafe_one_bilinear_multisetSum`), in particular the invariant mass squared on a
  finite-dimensional space (`isSoftSafe_one_invariantMassSq_of_finite`).
* `not_isSoftSafe_particleMultiplicity_of_ne_zero`: the particle multiplicity is not soft safe of
  any positive order, while `isSoftSafe_zero_particleMultiplicity` shows that it is soft safe of
  order `0`. Order-`0` soft safety only bounds the jump caused by a soft momentum, so it does not
  imply infrared safety, and the positivity hypothesis of `IsSoftSafe.isInfraredSafe` cannot be
  dropped.
* `isSoftSafe_leadingEnergy`: the leading-particle energy is soft safe of order `k` whenever the
  energy function is `O(‖p‖ ^ k)`; for a continuous linear energy it is soft safe of order `1`
  (`isSoftSafe_one_leadingEnergy`). Since for a nonzero energy functional it is not collinear safe
  (`not_isCollinearSafe_leadingEnergy`), soft safety of any order says nothing about collinear
  safety.

## References

* G. P. Salam, *Towards jetography*, Eur. Phys. J. C 67 (2010) 637, §2.
-/

public section

namespace EpsilonEridani.QFT.Jets

open Filter Topology Asymptotics

variable {V X Y Z : Type*}

section Basic

variable [SeminormedAddCommGroup V] [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
  [SeminormedAddCommGroup Z] {j k : ℕ}

/-- An observable is *soft safe of order `k`* if adding a momentum `p` to any final state `s`
changes its value by `O(‖p‖ ^ k)` as `p → 0`. For `k ≠ 0` this is a quantitative form of infrared
safety (`IsSoftSafe.isInfraredSafe`); for `k = 0` it only bounds the change near `p = 0`. -/
def IsSoftSafe (k : ℕ) (O : Multiset V → X) : Prop :=
  ∀ s : Multiset V, (fun p : V => O (p ::ₘ s) - O s) =O[𝓝 0] fun p => ‖p‖ ^ k

theorem isSoftSafe_def {O : Multiset V → X} :
    IsSoftSafe k O ↔
      ∀ s : Multiset V, (fun p : V => O (p ::ₘ s) - O s) =O[𝓝 0] fun p => ‖p‖ ^ k :=
  Iff.rfl

/-- Soft safety of a positive order implies infrared safety. -/
theorem IsSoftSafe.isInfraredSafe {O : Multiset V → X} (hO : IsSoftSafe k O) (hk : k ≠ 0) :
    IsInfraredSafe O := isInfraredSafe_def.2 fun s => by
  have h : Tendsto (fun p : V => ‖p‖ ^ k) (𝓝 0) (𝓝 0) := by
    simpa [zero_pow hk] using (tendsto_norm_zero (E := V)).pow k
  exact tendsto_iff_norm_sub_tendsto_zero.2 ((hO s).norm_left.trans_tendsto h)

/-- Soft safety of order `k` implies soft safety of every order `j ≤ k`, since `‖p‖ ^ k ≤ ‖p‖ ^ j`
for `‖p‖ ≤ 1`. -/
theorem IsSoftSafe.of_le {O : Multiset V → X} (hO : IsSoftSafe k O) (hjk : j ≤ k) :
    IsSoftSafe j O := by
  obtain rfl | h := hjk.eq_or_lt
  · exact hO
  · exact fun s => (hO s).trans (isLittleO_norm_pow_norm_pow h).isBigO

theorem isSoftSafe_const (k : ℕ) (x : X) : IsSoftSafe k (fun _ : Multiset V => x) :=
  fun _ => by simpa using isBigO_zero (fun p : V => ‖p‖ ^ k) (𝓝 0)

/-- The sum of two observables soft safe of order `k` is soft safe of order `k`. -/
theorem IsSoftSafe.add {O₁ O₂ : Multiset V → X} (h₁ : IsSoftSafe k O₁) (h₂ : IsSoftSafe k O₂) :
    IsSoftSafe k (fun s => O₁ s + O₂ s) :=
  fun s => ((h₁ s).add (h₂ s)).congr_left fun _ => (add_sub_add_comm _ _ _ _).symm

/-- The negation of an observable soft safe of order `k` is soft safe of order `k`. -/
theorem IsSoftSafe.neg {O : Multiset V → X} (h : IsSoftSafe k O) :
    IsSoftSafe k (fun s => -O s) :=
  fun s => (h s).neg_left.congr_left fun _ => (neg_sub _ _).trans (neg_sub_neg _ _).symm

/-- The difference of two observables soft safe of order `k` is soft safe of order `k`. -/
theorem IsSoftSafe.sub {O₁ O₂ : Multiset V → X} (h₁ : IsSoftSafe k O₁) (h₂ : IsSoftSafe k O₂) :
    IsSoftSafe k (fun s => O₁ s - O₂ s) :=
  fun s => ((h₁ s).sub (h₂ s)).congr_left fun _ => sub_sub_sub_comm _ _ _ _

/-- A sum `∑_{q ∈ s} f q` over the particles of the final state is soft safe of order `k` if and
only if `f p = O(‖p‖ ^ k)` as `p → 0`: adding `p` changes the sum by exactly `f p`. -/
theorem isSoftSafe_sum_map_iff {f : V → X} :
    IsSoftSafe k (fun s => (s.map f).sum) ↔ f =O[𝓝 0] fun p => ‖p‖ ^ k := by
  simp only [isSoftSafe_def, Multiset.map_cons, Multiset.sum_cons, add_sub_cancel_right]
  exact ⟨fun h => h 0, fun h _ => h⟩

/-- The total momentum of a final state is soft safe of order `1`. -/
theorem isSoftSafe_one_multisetSum : IsSoftSafe 1 (Multiset.sum : Multiset V → V) := by
  simpa using (isSoftSafe_sum_map_iff (k := 1) (f := id)).2 <| by
    simpa using (isBigO_refl (id : V → V) (𝓝 0)).norm_right

/-- An observable soft safe of any order stays bounded under the addition of a soft momentum. -/
theorem IsSoftSafe.isBigO_one_cons {O : Multiset V → X} (h : IsSoftSafe k O) (s : Multiset V) :
    (fun p : V => O (p ::ₘ s)) =O[𝓝 0] fun _ => (1 : ℝ) := by
  have h₀ : (fun p : V => ‖p‖ ^ k) =O[𝓝 0] fun _ => (1 : ℝ) :=
    ((continuous_norm.pow k).tendsto 0).isBigO_one ℝ
  simpa using ((h s).trans h₀).add (isBigO_const_const (O s) one_ne_zero (𝓝 (0 : V)))

/-- A map `f` that is additive in each argument and bounded, `‖f a b‖ ≤ C * ‖a‖ * ‖b‖`, sends two
observables soft safe of order `k` to an observable soft safe of order `k`. This is the common
core of `IsSoftSafe.mul` and `IsSoftSafe.bilinear`. -/
theorem IsSoftSafe.map₂ {O₁ : Multiset V → X} {O₂ : Multiset V → Y} {f : X → Y → Z} {C : ℝ}
    (hf₁ : ∀ a a' b, f a' b - f a b = f (a' - a) b) (hf₂ : ∀ a b b', f a b' - f a b = f a (b' - b))
    (hf : ∀ a b, ‖f a b‖ ≤ C * ‖a‖ * ‖b‖) (h₁ : IsSoftSafe k O₁) (h₂ : IsSoftSafe k O₂) :
    IsSoftSafe k (fun s => f (O₁ s) (O₂ s)) := by
  intro s
  -- `f a' b' - f a b = f (a' - a) b' + f a (b' - b)`, and `b'` stays bounded as `p → 0`.
  have e : ∀ p : V, f (O₁ (p ::ₘ s) - O₁ s) (O₂ (p ::ₘ s)) + f (O₁ s) (O₂ (p ::ₘ s) - O₂ s) =
      f (O₁ (p ::ₘ s)) (O₂ (p ::ₘ s)) - f (O₁ s) (O₂ s) := fun p => by
    rw [← hf₁, ← hf₂, sub_add_sub_cancel]
  have hO (u : V → X) (v : V → Y) : (fun p => f (u p) (v p)) =O[𝓝 0] fun p => ‖u p‖ * ‖v p‖ :=
    isBigO_of_le' (c := C) _ fun p => by
      simpa only [norm_mul, norm_norm, mul_assoc] using hf (u p) (v p)
  refine (IsBigO.add ((hO _ _).trans ?_) ((hO _ _).trans ?_)).congr_left e
  · simpa using (h₁ s).norm_left.mul (h₂.isBigO_one_cons s).norm_left
  · simpa using (isBigO_const_const ‖O₁ s‖ one_ne_zero (𝓝 (0 : V))).mul (h₂ s).norm_left

/-- The product of two observables soft safe of order `k` with values in a seminormed ring is soft
safe of order `k`. -/
theorem IsSoftSafe.mul {R : Type*} [SeminormedRing R] {O₁ O₂ : Multiset V → R}
    (h₁ : IsSoftSafe k O₁) (h₂ : IsSoftSafe k O₂) : IsSoftSafe k (fun s => O₁ s * O₂ s) :=
  h₁.map₂ (C := 1) (fun a a' b => (sub_mul a' a b).symm) (fun a b b' => (mul_sub a b' b).symm)
    (fun a b => by simpa using norm_mul_le a b) h₂

end Basic

/-! ### Bilinear maps -/

section Bilinear

variable [SeminormedAddCommGroup V] [SeminormedAddCommGroup X] [NormedSpace ℝ X]
  [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]
  {k : ℕ}

/-- A continuous bilinear map applied to two observables soft safe of order `k` gives an
observable soft safe of order `k`. -/
theorem IsSoftSafe.bilinear (B : X →L[ℝ] Y →L[ℝ] Z) {O₁ : Multiset V → X} {O₂ : Multiset V → Y}
    (h₁ : IsSoftSafe k O₁) (h₂ : IsSoftSafe k O₂) :
    IsSoftSafe k (fun s => B (O₁ s) (O₂ s)) :=
  h₁.map₂ (f := fun a b => B a b) (fun _ _ _ => by simp) (fun _ _ _ => (map_sub _ _ _).symm)
    B.le_opNorm₂ h₂

end Bilinear

/-! ### Energy sums and the invariant mass -/

section Linear

variable [SeminormedAddCommGroup V] [NormedSpace ℝ V] [SeminormedAddCommGroup X] [NormedSpace ℝ X]

/-- The sum over the particles of a continuous linear function of their momenta, such as their
total energy in a frame, is soft safe of order `1`. -/
theorem isSoftSafe_one_sum_map (E : V →L[ℝ] X) : IsSoftSafe 1 (fun s => (s.map E).sum) :=
  isSoftSafe_sum_map_iff.2 <| by simpa using (E.isBigO_id _).norm_right

/-- The square `B P P` of the total momentum `P` of a final state under a continuous bilinear form
`B` is soft safe of order `1`. -/
theorem isSoftSafe_one_bilinear_multisetSum (B : V →L[ℝ] V →L[ℝ] ℝ) :
    IsSoftSafe 1 (fun s => B s.sum s.sum) :=
  isSoftSafe_one_multisetSum.bilinear B isSoftSafe_one_multisetSum

end Linear

/-- The invariant mass squared of a final state is soft safe of order `1` for every bilinear form
on a finite-dimensional normed space of momenta. -/
theorem isSoftSafe_one_invariantMassSq_of_finite [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (g : LinearMap.BilinForm ℝ V) :
    IsSoftSafe 1 (invariantMassSq g) := fun s => by
  simpa [invariantMassSq_def] using isSoftSafe_one_bilinear_multisetSum g.toContinuousBilinearMap s

/-! ### Particle multiplicity and the leading-particle energy -/

section Examples

variable [SeminormedAddCommGroup V] {k : ℕ}

/-- The particle multiplicity is not soft safe of any positive order: adding a momentum, however
soft, adds one particle. -/
theorem not_isSoftSafe_particleMultiplicity_of_ne_zero (hk : k ≠ 0) :
    ¬ IsSoftSafe k (particleMultiplicity : Observable V) :=
  fun h => not_isInfraredSafe_particleMultiplicity (h.isInfraredSafe hk)

/-- The particle multiplicity is soft safe of order `0`, since adding a momentum changes it by
exactly `1`. Together with `not_isInfraredSafe_particleMultiplicity`, this shows that soft safety
of order `0` does not imply infrared safety. -/
theorem isSoftSafe_zero_particleMultiplicity :
    IsSoftSafe 0 (particleMultiplicity : Observable V) := fun s => by
  simp only [particleMultiplicity_cons, add_sub_cancel_left, pow_zero]
  exact isBigO_refl _ _

/-- The leading-particle energy is soft safe of order `k` whenever the energy function is
`O(‖p‖ ^ k)` as `p → 0`: adding `p` changes it by at most `|E p|`. -/
theorem isSoftSafe_leadingEnergy {E : V → ℝ} (hE : E =O[𝓝 0] fun p => ‖p‖ ^ k) :
    IsSoftSafe k (leadingEnergy E) := fun s => by
  refine (isBigO_of_le _ fun p => ?_).trans hE
  have := abs_max_sub_max_le_abs (E p) 0 (leadingEnergy E s)
  rw [max_eq_right (leadingEnergy_nonneg E s), sub_zero, ← leadingEnergy_cons] at this
  simpa only [Real.norm_eq_abs] using this

/-- The leading-particle energy of a continuous linear energy functional is soft safe of order `1`,
although for a nonzero functional it is not collinear safe (`not_isCollinearSafe_leadingEnergy`). -/
theorem isSoftSafe_one_leadingEnergy [NormedSpace ℝ V] (E : V →L[ℝ] ℝ) :
    IsSoftSafe 1 (leadingEnergy E) :=
  isSoftSafe_leadingEnergy <| by simpa using (E.isBigO_id _).norm_right

end Examples

end EpsilonEridani.QFT.Jets
