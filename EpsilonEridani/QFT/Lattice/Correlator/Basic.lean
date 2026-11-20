/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Ground-state matrix elements from Euclidean two- and three-point correlators

A Euclidean calculation does not compute the forward matrix element `⟨0|O|0⟩` of an operator `O`
in a hadron state `|0⟩` directly. It computes correlators of an interpolating operator `χ` that
creates every state `|n⟩` of the given quantum numbers and momentum, and the matrix element has to
be extracted from their dependence on the Euclidean time separations. This file states the
spectral decomposition those correlators have and proves that, under a spectral gap, the standard
ratio of the three-point to the two-point correlator converges to the ground-state matrix element,
with a remainder exponentially small in the gap times the time separations.

The spectral decomposition is recorded as data, `SpectralData ι`: energies `E n` and overlaps
`Z n = ⟨Ω|χ|n⟩`, indexed by a type `ι` of states. The inserted operator enters only the
three-point correlator, through its matrix elements `O n m = ⟨n|O|m⟩`, which are passed as a
separate argument `O : ι → ι → ℂ`. In terms of these, the two-point correlator at sink time `t`
and the three-point correlator with the operator inserted at time `τ` are

* `twoPoint t = ∑ₙ |Z n|² e^{-E n t}`,
* `threePoint O t τ = ∑ₙ,ₘ Z n · O n m · conj (Z m) · e^{-E n (t - τ)} e^{-E m τ}`.

These are the forms the transfer matrix gives at infinite time extent, with the vacuum
contribution already removed; a lattice construction is not built here, and the decomposition is
the hypothesis on the data that it would supply. The *spectral gap* hypothesis
`HasSpectralGap S n₀ Δ` says that every state other than the ground state `n₀` lies at least
`Δ > 0` above it. Both correlators are `tsum`s, so they take the junk value `0` where the spectral
sum does not converge; `hasSum_twoPoint` and `hasSum_threePoint` give conditions under which it
does.

Convergence is only ever assumed at reference time separations: the two-point sum at a time `t₀`,
the three-point sum (absolutely) at sink-operator separation `s₀` and operator time `τ₀`. The
results then hold at all later separations. No convergence at zero separation is assumed, so a
tower of states with `∑ₙ |Z n|² = ∞` whose correlators converge at every positive time is covered.

## Main results

* `SpectralData.hasSum_twoPoint` and `SpectralData.hasSum_threePoint`: once the energies are
  bounded below, the two-point sum converges at every `t ≥ t₀` if it converges at `t₀`, and the
  three-point sum converges whenever `t - τ ≥ s₀` and `τ ≥ τ₀` if it converges absolutely at
  `(s₀, τ₀)`.
* `SpectralData.twoPoint_mul_exp_sub_le` and `SpectralData.sq_norm_overlap_le_twoPoint_mul_exp`:
  `0 ≤ C₂(t) e^{E₀ t} - |Z₀|² ≤ K₂(t₀) e^{-Δ (t - t₀)}` for `t ≥ t₀`, where
  `K₂(t₀) = ∑_{n ≠ n₀} |Z n|² e^{-(E n - E₀) t₀}` is the excited-state weight
  `SpectralData.twoPointExcitedWeight` of the two-point correlator. A convergent two-point
  correlator is positive once some overlap is nonzero (`SpectralData.twoPoint_pos`), and
  `C₂(t) e^{E₀ t} → |Z₀|²` (`SpectralData.tendsto_twoPoint_mul_exp`).
* `SpectralData.norm_threePoint_mul_exp_sub_le`: `‖C₃(t, τ) e^{E₀ t} - |Z₀|² O₀₀‖` is at most
  `K₃(s₀, τ₀) (e^{-Δ (τ - τ₀)} + e^{-Δ (t - τ - s₀)})` for `t - τ ≥ s₀` and `τ ≥ τ₀`, where
  `K₃(s₀, τ₀)` is the excited-state weight `SpectralData.threePointExcitedWeight` of the
  three-point correlator.
* `SpectralData.norm_threePoint_div_twoPoint_sub_le`: for `t - τ ≥ s₀`, `τ ≥ τ₀` and `Z₀ ≠ 0`, the
  ratio `C₃(t, τ) / C₂(t)` differs from the ground-state matrix element `O₀₀` by at most
  `(K₃(s₀, τ₀) + ‖O₀₀‖ K₂(s₀ + τ₀)) / |Z₀|²` times `e^{-Δ (τ - τ₀)} + e^{-Δ (t - τ - s₀)}`.
* `SpectralData.tendsto_threePoint_div_twoPoint`: for `Z₀ ≠ 0`, the ratio converges to `O₀₀` along
  any filter on which both `τ` and `t - τ` tend to infinity.

The constant `K₂` is fixed by the overlaps of the interpolating operator with the excited states,
and `K₃` also by the matrix elements of `O` involving them; about these nothing beyond convergence
at the reference separations is assumed: the gap alone determines the rate, not the size, of the
excited-state contamination.

## References

* C. Gattringer and C. B. Lang, *Quantum Chromodynamics on the Lattice*, Lecture Notes in
  Physics 788, Springer (2010), Chapter 6.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Lattice
namespace Correlator

open Complex ComplexConjugate Filter Topology

/-- The spectral data of an interpolating operator `χ` over a type `ι` of intermediate states of
fixed momentum: the energies of the states and the overlaps of `χ` with them. -/
@[ext]
structure SpectralData (ι : Type*) where
  /-- The energy `E n` of the state `n`. -/
  energy : ι → ℝ
  /-- The overlap `Z n = ⟨Ω|χ|n⟩` of the interpolating operator with the state `n`. -/
  overlap : ι → ℂ

namespace SpectralData

variable {ι : Type*} (S : SpectralData ι)

/-- The Euclidean two-point correlator `C₂(t) = ∑ₙ |Z n|² e^{-E n t}` at time separation `t`. As a
`tsum` it is `0` where the spectral sum does not converge (see `hasSum_twoPoint`). -/
noncomputable def twoPoint (t : ℝ) : ℝ :=
  ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t))

/-- The two-point correlator as its spectral sum. -/
theorem twoPoint_def (t : ℝ) :
    S.twoPoint t = ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t)) :=
  (rfl)

/-- The two-point correlator is nonnegative at every time: its summands are, and where they are
not summable it takes the junk value `0`. -/
@[simp]
theorem twoPoint_nonneg (t : ℝ) : 0 ≤ S.twoPoint t := by
  rw [twoPoint_def]
  exact tsum_nonneg fun _ => by positivity

/-- The Euclidean three-point correlator with source at time `0`, sink at time `t` and the
operator with matrix elements `O n m = ⟨n|O|m⟩` inserted at time `τ`:
`C₃(t, τ) = ∑ₙ,ₘ Z n · ⟨n|O|m⟩ · conj (Z m) · e^{-E n (t - τ)} e^{-E m τ}`. As a `tsum` it is `0`
where the spectral sum does not converge (see `hasSum_threePoint`). -/
noncomputable def threePoint (O : ι → ι → ℂ) (t τ : ℝ) : ℂ :=
  ∑' p : ι × ι, S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) *
    (Real.exp (-(S.energy p.1 * (t - τ))) * Real.exp (-(S.energy p.2 * τ)) : ℝ)

/-- The three-point correlator as its spectral sum. -/
theorem threePoint_def (O : ι → ι → ℂ) (t τ : ℝ) :
    S.threePoint O t τ = ∑' p : ι × ι, S.overlap p.1 * O p.1 p.2 *
      conj (S.overlap p.2) *
        (Real.exp (-(S.energy p.1 * (t - τ))) * Real.exp (-(S.energy p.2 * τ)) : ℝ) :=
  (rfl)

/-- The weight `|Z n| ‖⟨n|O|m⟩‖ |Z m|` of the pair of states `p = (n, m)` in the three-point
correlator: the norm of its summand before the Euclidean time dependence. -/
noncomputable def threePointWeight (O : ι → ι → ℂ) (p : ι × ι) : ℝ :=
  ‖S.overlap p.1‖ * ‖O p.1 p.2‖ * ‖S.overlap p.2‖

/-- The weight of a pair of states as a product of norms. -/
theorem threePointWeight_def (O : ι → ι → ℂ) (p : ι × ι) :
    S.threePointWeight O p = ‖S.overlap p.1‖ * ‖O p.1 p.2‖ * ‖S.overlap p.2‖ :=
  (rfl)

/-- The weight of a pair of states is nonnegative. -/
@[simp]
theorem threePointWeight_nonneg (O : ι → ι → ℂ) (p : ι × ι) : 0 ≤ S.threePointWeight O p := by
  rw [threePointWeight_def]
  positivity

/-- The weight of a pair of equal states `(n, n)` is `|Z n|² ‖⟨n|O|n⟩‖`. -/
theorem threePointWeight_self (O : ι → ι → ℂ) (n : ι) :
    S.threePointWeight O (n, n) = ‖S.overlap n‖ ^ 2 * ‖O n n‖ := by
  rw [threePointWeight_def]
  ring

/-- The excited-state weight `K₂(t₀) = ∑ₙ |Z n|² e^{-(E n - E₀) t₀} - |Z₀|²` of the two-point
correlator relative to the state `n₀`, at the reference time `t₀`: the contribution of the states
other than `n₀` to `C₂(t₀) e^{E₀ t₀}` (see `hasSum_twoPointExcitedWeight`). -/
noncomputable def twoPointExcitedWeight (n₀ : ι) (t₀ : ℝ) : ℝ :=
  ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - S.energy n₀) * t₀)) - ‖S.overlap n₀‖ ^ 2

/-- The excited-state weight of the two-point correlator as a difference of sums. -/
theorem twoPointExcitedWeight_def (n₀ : ι) (t₀ : ℝ) :
    S.twoPointExcitedWeight n₀ t₀ =
      ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - S.energy n₀) * t₀)) -
        ‖S.overlap n₀‖ ^ 2 :=
  (rfl)

/-- The excited-state weight
`K₃(s₀, τ₀) = ∑ₙ,ₘ |Z n| ‖⟨n|O|m⟩‖ |Z m| e^{-(E n - E₀) s₀} e^{-(E m - E₀) τ₀} - |Z₀|² ‖⟨0|O|0⟩‖`
of the three-point correlator relative to the state `n₀`, at the reference sink-operator
separation `s₀` and operator time `τ₀`: the weight of the pairs of states other than `(n₀, n₀)`
(see `hasSum_threePointExcitedWeight`). -/
noncomputable def threePointExcitedWeight (O : ι → ι → ℂ) (n₀ : ι) (s₀ τ₀ : ℝ) : ℝ :=
  ∑' p, S.threePointWeight O p * (Real.exp (-((S.energy p.1 - S.energy n₀) * s₀)) *
    Real.exp (-((S.energy p.2 - S.energy n₀) * τ₀))) - ‖S.overlap n₀‖ ^ 2 * ‖O n₀ n₀‖

/-- The excited-state weight of the three-point correlator as a difference of sums. -/
theorem threePointExcitedWeight_def (O : ι → ι → ℂ) (n₀ : ι) (s₀ τ₀ : ℝ) :
    S.threePointExcitedWeight O n₀ s₀ τ₀ =
      ∑' p, S.threePointWeight O p * (Real.exp (-((S.energy p.1 - S.energy n₀) * s₀)) *
        Real.exp (-((S.energy p.2 - S.energy n₀) * τ₀))) - ‖S.overlap n₀‖ ^ 2 * ‖O n₀ n₀‖ :=
  (rfl)

/-- The *spectral gap* hypothesis: every state other than the ground state `n₀` has energy at
least `Δ > 0` above the ground-state energy. -/
structure HasSpectralGap (n₀ : ι) (Δ : ℝ) : Prop where
  /-- The gap is positive. -/
  pos : 0 < Δ
  /-- Every excited state lies at least `Δ` above the ground state. -/
  add_le_energy : ∀ n, n ≠ n₀ → S.energy n₀ + Δ ≤ S.energy n

variable {S} {O : ι → ι → ℂ} {n₀ : ι} {Δ : ℝ}

/-- Relative to an energy `E` not above that of the state `n`, the state `n` does not grow in
Euclidean time. -/
private theorem exp_neg_sub_mul_le_one {E : ℝ} {n : ι} (hE : E ≤ S.energy n) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-((S.energy n - E) * s)) ≤ 1 :=
  Real.exp_le_one_iff.2 <| neg_nonpos.2 <| mul_nonneg (sub_nonneg.2 hE) hs

namespace HasSpectralGap

/-- Under a spectral gap, `n₀` is a state of lowest energy. -/
theorem energy_le (h : S.HasSpectralGap n₀ Δ) (n : ι) : S.energy n₀ ≤ S.energy n := by
  rcases eq_or_ne n n₀ with rfl | hn
  · exact le_rfl
  · linarith [h.add_le_energy n hn, h.pos]

/-- Relative to the ground state, an excited state is suppressed by at least `e^{-Δ s}`. -/
theorem exp_neg_sub_mul_le (h : S.HasSpectralGap n₀ Δ) {n : ι} (hn : n ≠ n₀) {s : ℝ}
    (hs : 0 ≤ s) :
    Real.exp (-((S.energy n - S.energy n₀) * s)) ≤ Real.exp (-(Δ * s)) :=
  Real.exp_le_exp.2 <| neg_le_neg <|
    mul_le_mul_of_nonneg_right (by linarith [h.add_le_energy n hn]) hs

/-- A pair of states other than the ground state twice is suppressed, relative to the ground
state, by `e^{-Δ τ}` or by `e^{-Δ s}`. -/
private theorem exp_mul_exp_le (h : S.HasSpectralGap n₀ Δ) {p : ι × ι} (hp : p ≠ (n₀, n₀))
    {s τ : ℝ} (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    Real.exp (-((S.energy p.1 - S.energy n₀) * s)) *
        Real.exp (-((S.energy p.2 - S.energy n₀) * τ)) ≤
      Real.exp (-(Δ * τ)) + Real.exp (-(Δ * s)) := by
  obtain ⟨n, m⟩ := p
  by_cases hm : m = n₀
  · have hn : n ≠ n₀ := by rintro rfl; exact hp (by rw [hm])
    calc _ ≤ Real.exp (-(Δ * s)) * 1 :=
          mul_le_mul (h.exp_neg_sub_mul_le hn hs) (exp_neg_sub_mul_le_one (h.energy_le m) hτ)
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact le_add_of_nonneg_left (Real.exp_pos _).le
  · calc _ ≤ 1 * Real.exp (-(Δ * τ)) :=
          mul_le_mul (exp_neg_sub_mul_le_one (h.energy_le n) hs) (h.exp_neg_sub_mul_le hm hτ)
            (Real.exp_pos _).le zero_le_one
      _ ≤ _ := by rw [one_mul]; exact le_add_of_nonneg_right (Real.exp_pos _).le

end HasSpectralGap

/-! ### The two-point correlator -/

/-- A summand of the two-point correlator, multiplied by a reference growth `e^{E t}`. -/
private theorem twoPoint_term_mul_exp (n : ι) (E t : ℝ) :
    ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t)) * Real.exp (E * t) =
      ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - E) * t)) := by
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/-- The two-point correlator measured in units of a reference decay `e^{-E t}`: each state then
decays with its energy relative to `E`. -/
theorem twoPoint_mul_exp (E t : ℝ) :
    S.twoPoint t * Real.exp (E * t) =
      ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - E) * t)) := by
  rw [twoPoint_def, ← tsum_mul_right]
  exact tsum_congr fun n => twoPoint_term_mul_exp n E t

/-- For energies bounded below, the spectral sum of the two-point correlator converges at every
time `t` after a reference time `t₀` at which it converges. -/
theorem hasSum_twoPoint {E : ℝ} (hE : ∀ n, E ≤ S.energy n) {t₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t₀))) {t : ℝ}
    (ht : t₀ ≤ t) :
    HasSum (fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t))) (S.twoPoint t) := by
  rw [twoPoint_def]
  refine (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (hZ.mul_right (Real.exp (-(E * (t - t₀)))))).hasSum
  rw [mul_assoc, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_right (hE n) (sub_nonneg.2 ht)]

/-- For energies bounded below by `E`, the summands `|Z n|² e^{-(E n - E) t}`, each state decaying
with its energy above `E`, sum to `C₂(t) e^{E t}` at every time `t` after a reference time `t₀` at
which the two-point correlator converges. -/
theorem hasSum_twoPoint_mul_exp {E : ℝ} (hE : ∀ n, E ≤ S.energy n) {t₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t₀))) {t : ℝ}
    (ht : t₀ ≤ t) :
    HasSum (fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - E) * t)))
      (S.twoPoint t * Real.exp (E * t)) :=
  ((hasSum_twoPoint hE hZ ht).mul_right _).congr_fun fun n => (twoPoint_term_mul_exp n E t).symm

/-- The excited-state weight `K₂(t₀)` of a two-point correlator converging at `t₀` is the sum over
the states other than `n₀` of their weights `|Z n|² e^{-(E n - E₀) t₀}`. -/
theorem hasSum_twoPointExcitedWeight [DecidableEq ι] {t₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t₀))) (n₀ : ι) :
    HasSum (fun n => if n = n₀ then 0 else
        ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - S.energy n₀) * t₀)))
      (S.twoPointExcitedWeight n₀ t₀) := by
  have h := (hZ.mul_right (Real.exp (S.energy n₀ * t₀))).congr fun n =>
    twoPoint_term_mul_exp n (S.energy n₀) t₀
  convert hasSum_ite_sub_hasSum h.hasSum n₀ using 1
  simp [twoPointExcitedWeight_def]

/-- The excited-state weight of a two-point correlator converging at `t₀` is nonnegative. -/
theorem twoPointExcitedWeight_nonneg {t₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t₀))) (n₀ : ι) :
    0 ≤ S.twoPointExcitedWeight n₀ t₀ := by
  classical
  exact (hasSum_twoPointExcitedWeight hZ n₀).nonneg fun n => by split_ifs <;> positivity

/-- Any state `n₀` saturates the two-point correlator from below: after its decay `e^{-E₀ t}` is
divided out, a convergent two-point correlator is at least its weight `|Z₀|²`. -/
theorem sq_norm_overlap_le_twoPoint_mul_exp {t : ℝ}
    (hs : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t))) (n₀ : ι) :
    ‖S.overlap n₀‖ ^ 2 ≤ S.twoPoint t * Real.exp (S.energy n₀ * t) := by
  have := le_hasSum (hs.hasSum.mul_right (Real.exp (S.energy n₀ * t))) n₀
    fun n _ => by positivity
  rw [twoPoint_def]
  simpa [twoPoint_term_mul_exp] using this

/-- **Excited-state contamination of the two-point correlator.** After the ground-state decay
`e^{-E₀ t}` is divided out, the two-point correlator at a time `t` after a reference time `t₀` at
which it converges exceeds the ground-state weight `|Z₀|²` by at most the excited-state weight
`K₂(t₀)` times `e^{-Δ (t - t₀)}`. -/
theorem twoPoint_mul_exp_sub_le (h : S.HasSpectralGap n₀ Δ) {t₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t₀))) {t : ℝ}
    (ht : t₀ ≤ t) :
    S.twoPoint t * Real.exp (S.energy n₀ * t) - ‖S.overlap n₀‖ ^ 2 ≤
      S.twoPointExcitedWeight n₀ t₀ * Real.exp (-(Δ * (t - t₀))) := by
  classical
  -- each excited state is suppressed by at least `e^{-Δ (t - t₀)}` relative to its weight at `t₀`
  have hle : ∀ n, (if n = n₀ then 0 else
        ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - S.energy n₀) * t))) ≤
      (if n = n₀ then 0 else
        ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - S.energy n₀) * t₀))) *
          Real.exp (-(Δ * (t - t₀))) := fun n => by
    split_ifs with hn
    · simp
    · rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (sq_nonneg _)
      nlinarith [mul_nonneg (sub_nonneg.2 (h.add_le_energy n hn)) (sub_nonneg.2 ht)]
  have h₁ := hasSum_ite_sub_hasSum (hasSum_twoPoint_mul_exp h.energy_le hZ ht) n₀
  have h₂ := (hasSum_twoPointExcitedWeight hZ n₀).mul_right (Real.exp (-(Δ * (t - t₀))))
  simpa only [sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one] using hasSum_le hle h₁ h₂

/-- A convergent two-point correlator is positive once the interpolating operator overlaps with
some state. -/
theorem twoPoint_pos {t : ℝ}
    (hs : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t)))
    (h₀ : S.overlap n₀ ≠ 0) : 0 < S.twoPoint t := by
  rw [twoPoint_def]
  exact hs.tsum_pos (fun _ => by positivity) n₀
    (mul_pos (pow_pos (norm_pos_iff.2 h₀) 2) (Real.exp_pos _))

/-- **Ground-state dominance.** After the ground-state decay `e^{-E₀ t}` is divided out, a
two-point correlator converging at some time `t₀` tends to the ground-state weight `|Z₀|²` at large
Euclidean time. -/
theorem tendsto_twoPoint_mul_exp (h : S.HasSpectralGap n₀ Δ) {t₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t₀))) :
    Tendsto (fun t => S.twoPoint t * Real.exp (S.energy n₀ * t)) atTop
      (𝓝 (‖S.overlap n₀‖ ^ 2)) := by
  have hsub : Tendsto (fun t : ℝ => t - t₀) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-t₀) tendsto_id
  have hK : Tendsto (fun t => ‖S.overlap n₀‖ ^ 2 +
      S.twoPointExcitedWeight n₀ t₀ * Real.exp (-(Δ * (t - t₀)))) atTop
        (𝓝 (‖S.overlap n₀‖ ^ 2)) := by
    simpa using tendsto_const_nhds.add <| tendsto_const_nhds.mul <|
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (hsub.const_mul_atTop h.pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK ?_ ?_
  · filter_upwards [eventually_ge_atTop t₀] with t ht
    exact sq_norm_overlap_le_twoPoint_mul_exp (hasSum_twoPoint h.energy_le hZ ht).summable n₀
  · filter_upwards [eventually_ge_atTop t₀] with t ht
    linarith [twoPoint_mul_exp_sub_le h hZ ht]

/-! ### The three-point correlator -/

/-- A summand of the three-point correlator, multiplied by a reference growth `e^{E t}`. -/
private theorem threePoint_term_mul_exp (p : ι × ι) (E t τ : ℝ) :
    S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) *
        (Real.exp (-(S.energy p.1 * (t - τ))) * Real.exp (-(S.energy p.2 * τ)) : ℝ) *
        (Real.exp (E * t) : ℂ) =
      S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) *
        (Real.exp (-((S.energy p.1 - E) * (t - τ))) * Real.exp (-((S.energy p.2 - E) * τ)) :
          ℝ) := by
  simp only [mul_assoc, ← ofReal_mul, ← Real.exp_add]
  ring_nf

/-- The norm of a summand of the three-point correlator with a nonnegative time dependence `r`
is the weight of its pair of states times `r`. -/
private theorem norm_threePoint_term (p : ι × ι) {r : ℝ} (hr : 0 ≤ r) :
    ‖S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) * (r : ℂ)‖ =
      S.threePointWeight O p * r := by
  simp only [threePointWeight_def, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg hr]

/-- The three-point correlator measured in units of a reference decay `e^{-E t}`: each pair of
states then decays with its energies relative to `E`. -/
theorem threePoint_mul_exp (E t τ : ℝ) :
    S.threePoint O t τ * (Real.exp (E * t) : ℂ) =
      ∑' p : ι × ι, S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) *
        (Real.exp (-((S.energy p.1 - E) * (t - τ))) *
          Real.exp (-((S.energy p.2 - E) * τ)) : ℝ) := by
  rw [threePoint_def, ← tsum_mul_right]
  exact tsum_congr fun p => threePoint_term_mul_exp p E t τ

/-- For energies bounded below, the spectral sum of the three-point correlator converges whenever
the sink-operator separation `t - τ` is at least `s₀` and the operator time `τ` at least `τ₀`, once
it converges absolutely at sink-operator separation `s₀` and operator time `τ₀`. -/
theorem hasSum_threePoint {E : ℝ} (hE : ∀ n, E ≤ S.energy n) {s₀ τ₀ : ℝ}
    (hO : Summable fun p => S.threePointWeight O p *
      (Real.exp (-(S.energy p.1 * s₀)) * Real.exp (-(S.energy p.2 * τ₀))))
    {t τ : ℝ} (hτ : τ₀ ≤ τ) (hs : s₀ ≤ t - τ) :
    HasSum (fun p : ι × ι => S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) *
        (Real.exp (-(S.energy p.1 * (t - τ))) * Real.exp (-(S.energy p.2 * τ)) : ℝ))
      (S.threePoint O t τ) := by
  rw [threePoint_def]
  refine (Summable.of_norm_bounded (hO.mul_right
    (Real.exp (-(E * (t - τ - s₀))) * Real.exp (-(E * (τ - τ₀))))) fun p => ?_).hasSum
  rw [norm_threePoint_term p (by positivity), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (S.threePointWeight_nonneg O p)
  simp only [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  nlinarith [mul_le_mul_of_nonneg_right (hE p.1) (sub_nonneg.2 hs),
    mul_le_mul_of_nonneg_right (hE p.2) (sub_nonneg.2 hτ)]

/-- For energies bounded below by `E`, the summands of the three-point correlator with each pair
of states decaying with its energies above `E` sum to `C₃(t, τ) e^{E t}` whenever `t - τ ≥ s₀` and
`τ ≥ τ₀`, once the three-point correlator converges absolutely at `(s₀, τ₀)`. -/
theorem hasSum_threePoint_mul_exp {E : ℝ} (hE : ∀ n, E ≤ S.energy n) {s₀ τ₀ : ℝ}
    (hO : Summable fun p => S.threePointWeight O p *
      (Real.exp (-(S.energy p.1 * s₀)) * Real.exp (-(S.energy p.2 * τ₀))))
    {t τ : ℝ} (hτ : τ₀ ≤ τ) (hs : s₀ ≤ t - τ) :
    HasSum (fun p : ι × ι => S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) *
        (Real.exp (-((S.energy p.1 - E) * (t - τ))) * Real.exp (-((S.energy p.2 - E) * τ)) :
          ℝ))
      (S.threePoint O t τ * (Real.exp (E * t) : ℂ)) :=
  ((hasSum_threePoint hE hO hτ hs).mul_right _).congr_fun fun p =>
    (threePoint_term_mul_exp p E t τ).symm

/-- The excited-state weight `K₃(s₀, τ₀)` of a three-point correlator converging absolutely at
`(s₀, τ₀)` is the sum over the pairs of states other than `(n₀, n₀)` of their weights
`|Z n| ‖⟨n|O|m⟩‖ |Z m| e^{-(E n - E₀) s₀} e^{-(E m - E₀) τ₀}`. -/
theorem hasSum_threePointExcitedWeight [DecidableEq ι] {s₀ τ₀ : ℝ}
    (hO : Summable fun p => S.threePointWeight O p *
      (Real.exp (-(S.energy p.1 * s₀)) * Real.exp (-(S.energy p.2 * τ₀))))
    (n₀ : ι) :
    HasSum (fun p => if p = (n₀, n₀) then 0 else S.threePointWeight O p *
        (Real.exp (-((S.energy p.1 - S.energy n₀) * s₀)) *
          Real.exp (-((S.energy p.2 - S.energy n₀) * τ₀))))
      (S.threePointExcitedWeight O n₀ s₀ τ₀) := by
  have h : Summable fun p => S.threePointWeight O p *
      (Real.exp (-((S.energy p.1 - S.energy n₀) * s₀)) *
        Real.exp (-((S.energy p.2 - S.energy n₀) * τ₀))) :=
    (hO.mul_right (Real.exp (S.energy n₀ * (s₀ + τ₀)))).congr fun p => by
      rw [mul_assoc]
      congr 1
      simp only [← Real.exp_add]
      ring_nf
  convert hasSum_ite_sub_hasSum h.hasSum (n₀, n₀) using 1
  simp [threePointExcitedWeight_def, threePointWeight_self]

/-- The excited-state weight of a three-point correlator converging absolutely at `(s₀, τ₀)` is
nonnegative. -/
theorem threePointExcitedWeight_nonneg {s₀ τ₀ : ℝ}
    (hO : Summable fun p => S.threePointWeight O p *
      (Real.exp (-(S.energy p.1 * s₀)) * Real.exp (-(S.energy p.2 * τ₀))))
    (n₀ : ι) :
    0 ≤ S.threePointExcitedWeight O n₀ s₀ τ₀ := by
  classical
  refine (hasSum_threePointExcitedWeight hO n₀).nonneg fun p => ?_
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (S.threePointWeight_nonneg O p) (by positivity)

/-- **Excited-state contamination of the three-point correlator.** For `t - τ ≥ s₀` and `τ ≥ τ₀`,
after the ground-state decay `e^{-E₀ t}` is divided out, the three-point correlator differs from
its ground-state term `|Z₀|² ⟨0|O|0⟩` by at most the excited-state weight `K₃(s₀, τ₀)` times
`e^{-Δ (τ - τ₀)} + e^{-Δ (t - τ - s₀)}`, once it converges absolutely at `(s₀, τ₀)`. -/
theorem norm_threePoint_mul_exp_sub_le (h : S.HasSpectralGap n₀ Δ) {s₀ τ₀ : ℝ}
    (hO : Summable fun p => S.threePointWeight O p *
      (Real.exp (-(S.energy p.1 * s₀)) * Real.exp (-(S.energy p.2 * τ₀))))
    {t τ : ℝ} (hτ : τ₀ ≤ τ) (hs : s₀ ≤ t - τ) :
    ‖S.threePoint O t τ * (Real.exp (S.energy n₀ * t) : ℂ) -
        (‖S.overlap n₀‖ : ℂ) ^ 2 * O n₀ n₀‖ ≤
      S.threePointExcitedWeight O n₀ s₀ τ₀ *
        (Real.exp (-(Δ * (τ - τ₀))) + Real.exp (-(Δ * (t - τ - s₀)))) := by
  classical
  set e : ι × ι → ℝ := fun p => Real.exp (-((S.energy p.1 - S.energy n₀) * (t - τ))) *
    Real.exp (-((S.energy p.2 - S.energy n₀) * τ))
  set g : ι × ι → ℂ := fun p => S.overlap p.1 * O p.1 p.2 * conj (S.overlap p.2) *
    (e p : ℂ)
  have hg : ∀ p, ‖g p‖ = S.threePointWeight O p * e p := fun p =>
    norm_threePoint_term p (by positivity)
  have hB : HasSum g (S.threePoint O t τ * (Real.exp (S.energy n₀ * t) : ℂ)) :=
    hasSum_threePoint_mul_exp h.energy_le hO hτ hs
  have hg₀ : g (n₀, n₀) = (‖S.overlap n₀‖ : ℂ) ^ 2 * O n₀ n₀ := by
    simp only [g, e, sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one, ofReal_one]
    rw [mul_right_comm, Complex.mul_conj']
  set c := Real.exp (-(Δ * (τ - τ₀))) + Real.exp (-(Δ * (t - τ - s₀)))
  have hK := (hasSum_threePointExcitedWeight hO n₀).mul_right c
  rw [← hg₀, ← (hasSum_ite_sub_hasSum hB (n₀, n₀)).tsum_eq]
  refine tsum_of_norm_bounded hK fun p => ?_
  split_ifs with hp
  · simp
  · rw [hg, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (S.threePointWeight_nonneg O p)
    -- relative to its weight at `(s₀, τ₀)`, the pair is suppressed by `e^{-Δ (τ - τ₀)}` or by
    -- `e^{-Δ (t - τ - s₀)}`
    calc e p = (Real.exp (-((S.energy p.1 - S.energy n₀) * s₀)) *
            Real.exp (-((S.energy p.2 - S.energy n₀) * τ₀))) *
          (Real.exp (-((S.energy p.1 - S.energy n₀) * (t - τ - s₀))) *
            Real.exp (-((S.energy p.2 - S.energy n₀) * (τ - τ₀)))) := by
          simp only [e, ← Real.exp_add]
          ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left
          (h.exp_mul_exp_le hp (sub_nonneg.2 (le_sub_iff_add_le.2 (by linarith)))
            (sub_nonneg.2 hτ)) (by positivity)

/-! ### The ratio and the ground-state matrix element -/

/-- **The ratio method, quantitatively.** Under a spectral gap, for `t - τ ≥ s₀` and `τ ≥ τ₀`, the
ratio of the three-point to the two-point correlator differs from the ground-state matrix element
`⟨0|O|0⟩` by at most `(K₃(s₀, τ₀) + ‖⟨0|O|0⟩‖ K₂(s₀ + τ₀)) / |Z₀|²` times
`e^{-Δ (τ - τ₀)} + e^{-Δ (t - τ - s₀)}`, where `K₂` and `K₃` are the excited-state weights
`twoPointExcitedWeight` and `threePointExcitedWeight`, once the two-point correlator converges at
`s₀ + τ₀` and the three-point correlator converges absolutely at `(s₀, τ₀)`. -/
theorem norm_threePoint_div_twoPoint_sub_le (h : S.HasSpectralGap n₀ Δ) {s₀ τ₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * (s₀ + τ₀))))
    (hO : Summable fun p => S.threePointWeight O p *
      (Real.exp (-(S.energy p.1 * s₀)) * Real.exp (-(S.energy p.2 * τ₀))))
    (h₀ : S.overlap n₀ ≠ 0) {t τ : ℝ} (hτ : τ₀ ≤ τ) (hs : s₀ ≤ t - τ) :
    ‖S.threePoint O t τ / S.twoPoint t - O n₀ n₀‖ ≤
      (S.threePointExcitedWeight O n₀ s₀ τ₀ +
          ‖O n₀ n₀‖ * S.twoPointExcitedWeight n₀ (s₀ + τ₀)) /
        ‖S.overlap n₀‖ ^ 2 * (Real.exp (-(Δ * (τ - τ₀))) + Real.exp (-(Δ * (t - τ - s₀)))) := by
  have ht : s₀ + τ₀ ≤ t := by linarith
  set E₀ := S.energy n₀
  set z := ‖S.overlap n₀‖ ^ 2
  set O₀ := O n₀ n₀
  set K₂ := S.twoPointExcitedWeight n₀ (s₀ + τ₀)
  set K₃ := S.threePointExcitedWeight O n₀ s₀ τ₀
  set c := Real.exp (-(Δ * (τ - τ₀))) + Real.exp (-(Δ * (t - τ - s₀)))
  set A := S.twoPoint t * Real.exp (E₀ * t)
  set B := S.threePoint O t τ * (Real.exp (E₀ * t) : ℂ)
  have hz : 0 < z := pow_pos (norm_pos_iff.2 h₀) 2
  have hzA : z ≤ A :=
    sq_norm_overlap_le_twoPoint_mul_exp (hasSum_twoPoint h.energy_le hZ ht).summable n₀
  have hA₂ : A - z ≤ K₂ * Real.exp (-(Δ * (t - (s₀ + τ₀)))) := twoPoint_mul_exp_sub_le h hZ ht
  have hB₃ : ‖B - (z : ℂ) * O₀‖ ≤ K₃ * c := by
    rw [show ((z : ℝ) : ℂ) = (‖S.overlap n₀‖ : ℂ) ^ 2 by simp only [z, ofReal_pow]]
    exact norm_threePoint_mul_exp_sub_le h hO hτ hs
  have hK₂ : 0 ≤ K₂ := twoPointExcitedWeight_nonneg hZ n₀
  have hK₃ : 0 ≤ K₃ := threePointExcitedWeight_nonneg hO n₀
  have hc : 0 < c := by positivity
  -- the decay `e^{-Δ (t - s₀ - τ₀)}` of the two-point remainder is dominated by `c`
  have htc : Real.exp (-(Δ * (t - (s₀ + τ₀)))) ≤ c :=
    le_add_of_le_of_nonneg
      (Real.exp_le_exp.2 (by nlinarith [mul_nonneg h.pos.le (sub_nonneg.2 hs)]))
      (Real.exp_pos _).le
  -- dividing both correlators by the ground-state decay does not change their ratio
  have hratio : S.threePoint O t τ / S.twoPoint t = B / (A : ℂ) := by
    simp only [B, A, ofReal_mul]
    rw [mul_div_mul_right _ _ (by exact_mod_cast (Real.exp_pos _).ne')]
  have hA : (A : ℂ) ≠ 0 := by exact_mod_cast (hz.trans_le hzA).ne'
  have hdecomp : B / (A : ℂ) - O₀ = ((B - (z : ℂ) * O₀) - O₀ * ((A : ℂ) - z)) / A := by
    field_simp
    ring
  rw [hratio, hdecomp, norm_div, Complex.norm_real, Real.norm_of_nonneg (hz.le.trans hzA)]
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (hz.trans_le hzA) hz]
  calc ‖B - (z : ℂ) * O₀ - O₀ * ((A : ℂ) - z)‖ * z
      ≤ (K₃ * c + ‖O₀‖ * (K₂ * c)) * z := by
        gcongr
        refine (norm_sub_le _ _).trans (add_le_add hB₃ ?_)
        rw [norm_mul, ← ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        gcongr
        exact hA₂.trans (mul_le_mul_of_nonneg_left htc hK₂)
    _ ≤ (K₃ * c + ‖O₀‖ * (K₂ * c)) * A := by gcongr
    _ = (K₃ + ‖O₀‖ * K₂) * c * A := by ring

/-- **The ratio method.** Under a spectral gap, the ratio of the three-point to the two-point
correlator converges to the ground-state matrix element `⟨0|O|0⟩` along any filter on which both
the operator time `τ` and the sink-operator separation `t - τ` tend to infinity, once the
two-point correlator converges at `s₀ + τ₀` and the three-point correlator converges absolutely at
some sink-operator separation `s₀` and operator time `τ₀`. -/
theorem tendsto_threePoint_div_twoPoint (h : S.HasSpectralGap n₀ Δ) {s₀ τ₀ : ℝ}
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * (s₀ + τ₀))))
    (hO : Summable fun p => S.threePointWeight O p *
      (Real.exp (-(S.energy p.1 * s₀)) * Real.exp (-(S.energy p.2 * τ₀))))
    (h₀ : S.overlap n₀ ≠ 0) {α : Type*} {l : Filter α} {t τ : α → ℝ}
    (hτ : Tendsto τ l atTop) (htτ : Tendsto (fun a => t a - τ a) l atTop) :
    Tendsto (fun a => S.threePoint O (t a) (τ a) / S.twoPoint (t a)) l
      (𝓝 (O n₀ n₀)) := by
  set C := (S.threePointExcitedWeight O n₀ s₀ τ₀ +
    ‖O n₀ n₀‖ * S.twoPointExcitedWeight n₀ (s₀ + τ₀)) / ‖S.overlap n₀‖ ^ 2
  have hexp : ∀ {f : α → ℝ}, Tendsto f l atTop → ∀ r : ℝ,
      Tendsto (fun a => Real.exp (-(Δ * (f a - r)))) l (𝓝 0) := fun hf r =>
    Real.tendsto_exp_neg_atTop_nhds_zero.comp <|
      (by simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-r) hf :
        Tendsto (fun a => _ - r) l atTop).const_mul_atTop h.pos
  have hbound : Tendsto (fun a => C * (Real.exp (-(Δ * (τ a - τ₀))) +
      Real.exp (-(Δ * (t a - τ a - s₀))))) l (𝓝 0) := by
    simpa using ((hexp hτ τ₀).add (hexp htτ s₀)).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hbound
  filter_upwards [hτ.eventually_ge_atTop τ₀, htτ.eventually_ge_atTop s₀] with a ha hta
  exact norm_threePoint_div_twoPoint_sub_le h hZ hO h₀ ha hta

end SpectralData

end Correlator
end Lattice
end QFT
end EpsilonEridani
