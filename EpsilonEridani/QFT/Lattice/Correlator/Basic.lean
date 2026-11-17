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

The spectral decomposition is recorded as data, `SpectralData ι`: energies `E n`, overlaps
`Z n = ⟨Ω|χ|n⟩` and matrix elements `O n m = ⟨n|O|m⟩`, indexed by a type `ι` of states. In terms
of these, the two-point correlator at sink time `t` and the three-point correlator with the
operator inserted at time `τ` are

* `twoPoint t = ∑ₙ |Z n|² e^{-E n t}`,
* `threePoint t τ = ∑ₙ,ₘ Z n · O n m · conj (Z m) · e^{-E n (t - τ)} e^{-E m τ}`.

These are the forms the transfer matrix gives at infinite time extent, with the vacuum
contribution already removed; a lattice construction is not built here, and the decomposition is
the hypothesis on the data that it would supply. The *spectral gap* hypothesis
`HasSpectralGap S n₀ Δ` says that every state other than the ground state `n₀` lies at least
`Δ > 0` above it.

## Main results

* `SpectralData.twoPoint_mul_exp_sub_le` and `SpectralData.sq_norm_overlap_le_twoPoint_mul_exp`:
  `0 ≤ C₂(t) e^{E₀ t} - |Z₀|² ≤ K₂ e^{-Δ t}`, where `K₂ = ∑ₙ |Z n|² - |Z₀|²` is the excited-state
  weight of the two-point correlator. Consequently the two-point correlator is positive
  (`SpectralData.twoPoint_pos`) and `C₂(t) e^{E₀ t} → |Z₀|²`
  (`SpectralData.tendsto_twoPoint_mul_exp`).
* `SpectralData.norm_threePoint_mul_exp_sub_le`: `‖C₃(t, τ) e^{E₀ t} - |Z₀|² O₀₀‖` is at most
  `K₃ (e^{-Δ τ} + e^{-Δ (t - τ)})` for `0 ≤ τ ≤ t`, where `K₃` is the excited-state weight of the
  three-point correlator.
* `SpectralData.norm_threePoint_div_twoPoint_sub_le`: the ratio `C₃(t, τ) / C₂(t)` differs from
  the ground-state matrix element `O₀₀` by at most `(K₃ + ‖O₀₀‖ K₂) / |Z₀|²` times
  `e^{-Δ τ} + e^{-Δ (t - τ)}`.
* `SpectralData.tendsto_threePoint_div_twoPoint`: the ratio converges to `O₀₀` along any filter on
  which both `τ` and `t - τ` tend to infinity.

The constants `K₂` and `K₃` are fixed by the overlaps of the interpolating operator with the
excited states, about which nothing beyond summability is assumed: the gap alone determines the
rate, not the size, of the excited-state contamination.

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

/-- The spectral decomposition of the Euclidean correlators of an interpolating operator `χ` and
an inserted operator `O`, over a type `ι` of intermediate states of fixed momentum. -/
@[ext]
structure SpectralData (ι : Type*) where
  /-- The energy `E n` of the state `n`. -/
  energy : ι → ℝ
  /-- The overlap `Z n = ⟨Ω|χ|n⟩` of the interpolating operator with the state `n`. -/
  overlap : ι → ℂ
  /-- The matrix element `⟨n|O|m⟩` of the inserted operator between the states `n` and `m`. -/
  matrixElement : ι → ι → ℂ

namespace SpectralData

variable {ι : Type*} (S : SpectralData ι)

/-- The Euclidean two-point correlator `C₂(t) = ∑ₙ |Z n|² e^{-E n t}` at time separation `t`. -/
noncomputable def twoPoint (t : ℝ) : ℝ :=
  ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t))

/-- The two-point correlator as its spectral sum. -/
theorem twoPoint_def (t : ℝ) :
    S.twoPoint t = ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-(S.energy n * t)) :=
  (rfl)

/-- The Euclidean three-point correlator with source at time `0`, sink at time `t` and the
operator inserted at time `τ`:
`C₃(t, τ) = ∑ₙ,ₘ Z n · ⟨n|O|m⟩ · conj (Z m) · e^{-E n (t - τ)} e^{-E m τ}`. -/
noncomputable def threePoint (t τ : ℝ) : ℂ :=
  ∑' p : ι × ι, S.overlap p.1 * S.matrixElement p.1 p.2 * conj (S.overlap p.2) *
    (Real.exp (-(S.energy p.1 * (t - τ))) * Real.exp (-(S.energy p.2 * τ)) : ℝ)

/-- The three-point correlator as its spectral sum. -/
theorem threePoint_def (t τ : ℝ) :
    S.threePoint t τ = ∑' p : ι × ι, S.overlap p.1 * S.matrixElement p.1 p.2 *
      conj (S.overlap p.2) *
        (Real.exp (-(S.energy p.1 * (t - τ))) * Real.exp (-(S.energy p.2 * τ)) : ℝ) :=
  (rfl)

/-- The *spectral gap* hypothesis: every state other than the ground state `n₀` has energy at
least `Δ > 0` above the ground-state energy. -/
structure HasSpectralGap (n₀ : ι) (Δ : ℝ) : Prop where
  /-- The gap is positive. -/
  pos : 0 < Δ
  /-- Every excited state lies at least `Δ` above the ground state. -/
  add_le_energy : ∀ n, n ≠ n₀ → S.energy n₀ + Δ ≤ S.energy n

variable {S} {n₀ : ι} {Δ : ℝ}

namespace HasSpectralGap

/-- Under a spectral gap, `n₀` is a state of lowest energy. -/
theorem energy_le (h : S.HasSpectralGap n₀ Δ) (n : ι) : S.energy n₀ ≤ S.energy n := by
  rcases eq_or_ne n n₀ with rfl | hn
  · exact le_rfl
  · linarith [h.add_le_energy n hn, h.pos]

/-- Relative to the ground state, no state grows in Euclidean time. -/
theorem exp_neg_sub_mul_le_one (h : S.HasSpectralGap n₀ Δ) (n : ι) {s : ℝ} (hs : 0 ≤ s) :
    Real.exp (-((S.energy n - S.energy n₀) * s)) ≤ 1 :=
  Real.exp_le_one_iff.2 <| neg_nonpos.2 <| mul_nonneg (sub_nonneg.2 (h.energy_le n)) hs

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
          mul_le_mul (h.exp_neg_sub_mul_le hn hs) (h.exp_neg_sub_mul_le_one m hτ)
            (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact le_add_of_nonneg_left (Real.exp_pos _).le
  · calc _ ≤ 1 * Real.exp (-(Δ * τ)) :=
          mul_le_mul (h.exp_neg_sub_mul_le_one n hs) (h.exp_neg_sub_mul_le hm hτ)
            (Real.exp_pos _).le zero_le_one
      _ ≤ _ := by rw [one_mul]; exact le_add_of_nonneg_right (Real.exp_pos _).le

end HasSpectralGap

/-! ### The two-point correlator -/

/-- The two-point correlator measured in units of a reference decay `e^{-E t}`: each state then
decays with its energy relative to `E`. -/
theorem twoPoint_mul_exp (E t : ℝ) :
    S.twoPoint t * Real.exp (E * t) =
      ∑' n, ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - E) * t)) := by
  rw [twoPoint, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [mul_assoc, ← Real.exp_add]
  ring_nf

/-- The terms of the two-point correlator relative to the ground state, summed by
`twoPoint_mul_exp`, form a summable family. -/
private theorem hasSum_twoPoint_mul_exp (h : S.HasSpectralGap n₀ Δ)
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    HasSum (fun n => ‖S.overlap n‖ ^ 2 * Real.exp (-((S.energy n - S.energy n₀) * t)))
      (S.twoPoint t * Real.exp (S.energy n₀ * t)) := by
  rw [twoPoint_mul_exp]
  refine (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hZ).hasSum
  exact mul_le_of_le_one_right (sq_nonneg _) (h.exp_neg_sub_mul_le_one n ht)

/-- The ground state saturates the two-point correlator from below: after the ground-state decay
`e^{-E₀ t}` is divided out, the correlator is at least the ground-state weight `|Z₀|²`. -/
theorem sq_norm_overlap_le_twoPoint_mul_exp (h : S.HasSpectralGap n₀ Δ)
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    ‖S.overlap n₀‖ ^ 2 ≤ S.twoPoint t * Real.exp (S.energy n₀ * t) := by
  classical
  have := (hasSum_ite_sub_hasSum (hasSum_twoPoint_mul_exp h hZ ht) n₀).nonneg
    fun n => by split_ifs <;> positivity
  simpa using this

/-- **Excited-state contamination of the two-point correlator.** After the ground-state decay
`e^{-E₀ t}` is divided out, the two-point correlator exceeds the ground-state weight `|Z₀|²` by at
most the excited-state weight `∑ₙ |Z n|² - |Z₀|²` times `e^{-Δ t}`. -/
theorem twoPoint_mul_exp_sub_le (h : S.HasSpectralGap n₀ Δ)
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2) {t : ℝ} (ht : 0 ≤ t) :
    S.twoPoint t * Real.exp (S.energy n₀ * t) - ‖S.overlap n₀‖ ^ 2 ≤
      (∑' n, ‖S.overlap n‖ ^ 2 - ‖S.overlap n₀‖ ^ 2) * Real.exp (-(Δ * t)) := by
  classical
  have h₁ := hasSum_ite_sub_hasSum (hasSum_twoPoint_mul_exp h hZ ht) n₀
  have h₂ := hasSum_ite_sub_hasSum (hZ.hasSum.mul_right (Real.exp (-(Δ * t)))) n₀
  have := hasSum_le (fun n => ?_) h₁ h₂
  · simpa [sub_mul] using this
  · split_ifs with hn
    · exact le_rfl
    · exact mul_le_mul_of_nonneg_left (h.exp_neg_sub_mul_le hn ht) (sq_nonneg _)

/-- Under a spectral gap, the two-point correlator is positive at every nonnegative time once the
interpolating operator overlaps with the ground state. -/
theorem twoPoint_pos (h : S.HasSpectralGap n₀ Δ) (hZ : Summable fun n => ‖S.overlap n‖ ^ 2)
    (h₀ : S.overlap n₀ ≠ 0) {t : ℝ} (ht : 0 ≤ t) : 0 < S.twoPoint t := by
  have := (pow_pos (norm_pos_iff.2 h₀) 2).trans_le (sq_norm_overlap_le_twoPoint_mul_exp h hZ ht)
  exact pos_of_mul_pos_left this (Real.exp_pos _).le

/-- **Ground-state dominance.** After the ground-state decay `e^{-E₀ t}` is divided out, the
two-point correlator tends to the ground-state weight `|Z₀|²` at large Euclidean time. -/
theorem tendsto_twoPoint_mul_exp (h : S.HasSpectralGap n₀ Δ)
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2) :
    Tendsto (fun t => S.twoPoint t * Real.exp (S.energy n₀ * t)) atTop
      (𝓝 (‖S.overlap n₀‖ ^ 2)) := by
  have hK : Tendsto (fun t => ‖S.overlap n₀‖ ^ 2 +
      (∑' n, ‖S.overlap n‖ ^ 2 - ‖S.overlap n₀‖ ^ 2) * Real.exp (-(Δ * t))) atTop
        (𝓝 (‖S.overlap n₀‖ ^ 2)) := by
    simpa using tendsto_const_nhds.add <| tendsto_const_nhds.mul <|
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop h.pos)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hK ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with t ht
    exact sq_norm_overlap_le_twoPoint_mul_exp h hZ ht
  · filter_upwards [eventually_ge_atTop 0] with t ht
    linarith [twoPoint_mul_exp_sub_le h hZ ht]

/-! ### The three-point correlator -/

/-- The three-point correlator measured in units of a reference decay `e^{-E t}`: each pair of
states then decays with its energies relative to `E`. -/
theorem threePoint_mul_exp (E t τ : ℝ) :
    S.threePoint t τ * (Real.exp (E * t) : ℂ) =
      ∑' p : ι × ι, S.overlap p.1 * S.matrixElement p.1 p.2 * conj (S.overlap p.2) *
        (Real.exp (-((S.energy p.1 - E) * (t - τ))) *
          Real.exp (-((S.energy p.2 - E) * τ)) : ℝ) := by
  rw [threePoint, ← tsum_mul_right]
  refine tsum_congr fun p => ?_
  rw [mul_assoc, ← ofReal_mul]
  congr 2
  simp only [← Real.exp_add]
  ring_nf

/-- **Excited-state contamination of the three-point correlator.** For `0 ≤ τ ≤ t`, after the
ground-state decay `e^{-E₀ t}` is divided out, the three-point correlator differs from its
ground-state term `|Z₀|² ⟨0|O|0⟩` by at most the excited-state weight
`∑ₙ,ₘ |Z n| ‖⟨n|O|m⟩‖ |Z m| - |Z₀|² ‖⟨0|O|0⟩‖` times `e^{-Δ τ} + e^{-Δ (t - τ)}`. -/
theorem norm_threePoint_mul_exp_sub_le (h : S.HasSpectralGap n₀ Δ)
    (hO : Summable fun p : ι × ι =>
      ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖)
    {t τ : ℝ} (hτ : 0 ≤ τ) (hτt : τ ≤ t) :
    ‖S.threePoint t τ * (Real.exp (S.energy n₀ * t) : ℂ) -
        (‖S.overlap n₀‖ : ℂ) ^ 2 * S.matrixElement n₀ n₀‖ ≤
      (∑' p : ι × ι, ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖ -
          ‖S.overlap n₀‖ * ‖S.matrixElement n₀ n₀‖ * ‖S.overlap n₀‖) *
        (Real.exp (-(Δ * τ)) + Real.exp (-(Δ * (t - τ)))) := by
  classical
  have hs : 0 ≤ t - τ := sub_nonneg.2 hτt
  set w : ι × ι → ℝ := fun p => ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖
  set e : ι × ι → ℝ := fun p => Real.exp (-((S.energy p.1 - S.energy n₀) * (t - τ))) *
    Real.exp (-((S.energy p.2 - S.energy n₀) * τ))
  set g : ι × ι → ℂ := fun p => S.overlap p.1 * S.matrixElement p.1 p.2 * conj (S.overlap p.2) *
    (e p : ℂ)
  have he : ∀ p, 0 ≤ e p := fun p => by positivity
  have hg : ∀ p, ‖g p‖ = w p * e p := fun p => by
    simp only [g, w, norm_mul, Complex.norm_conj, Complex.norm_of_nonneg (he p)]
  have hgw : ∀ p, ‖g p‖ ≤ w p := fun p => by
    rw [hg]
    exact mul_le_of_le_one_right (by positivity)
      ((mul_le_mul (h.exp_neg_sub_mul_le_one _ hs) (h.exp_neg_sub_mul_le_one _ hτ)
        (Real.exp_pos _).le zero_le_one).trans_eq (one_mul 1))
  have hB : HasSum g (S.threePoint t τ * (Real.exp (S.energy n₀ * t) : ℂ)) := by
    rw [threePoint_mul_exp]
    exact (hO.of_norm_bounded hgw).hasSum
  have hg₀ : g (n₀, n₀) = (‖S.overlap n₀‖ : ℂ) ^ 2 * S.matrixElement n₀ n₀ := by
    simp only [g, e, sub_self, zero_mul, neg_zero, Real.exp_zero, mul_one, ofReal_one]
    rw [mul_right_comm, Complex.mul_conj']
  set c := Real.exp (-(Δ * τ)) + Real.exp (-(Δ * (t - τ)))
  have hK := hasSum_ite_sub_hasSum (hO.hasSum.mul_right c) (n₀, n₀)
  rw [← hg₀, ← (hasSum_ite_sub_hasSum hB (n₀, n₀)).tsum_eq]
  refine (tsum_of_norm_bounded hK fun p => ?_).trans_eq (by simp only [w, sub_mul])
  split_ifs with hp
  · simp
  · rw [hg]
    exact mul_le_mul_of_nonneg_left (h.exp_mul_exp_le hp hs hτ) (by positivity)

/-! ### The ratio and the ground-state matrix element -/

/-- **The ratio method, quantitatively.** Under a spectral gap, for `0 ≤ τ ≤ t`, the ratio of the
three-point to the two-point correlator differs from the ground-state matrix element `⟨0|O|0⟩` by
at most `(K₃ + ‖⟨0|O|0⟩‖ K₂) / |Z₀|²` times `e^{-Δ τ} + e^{-Δ (t - τ)}`, where `K₂` and `K₃` are
the excited-state weights of `twoPoint_mul_exp_sub_le` and `norm_threePoint_mul_exp_sub_le`. -/
theorem norm_threePoint_div_twoPoint_sub_le (h : S.HasSpectralGap n₀ Δ)
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2)
    (hO : Summable fun p : ι × ι =>
      ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖)
    (h₀ : S.overlap n₀ ≠ 0) {t τ : ℝ} (hτ : 0 ≤ τ) (hτt : τ ≤ t) :
    ‖S.threePoint t τ / S.twoPoint t - S.matrixElement n₀ n₀‖ ≤
      ((∑' p : ι × ι, ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖ -
          ‖S.overlap n₀‖ * ‖S.matrixElement n₀ n₀‖ * ‖S.overlap n₀‖) +
        ‖S.matrixElement n₀ n₀‖ * (∑' n, ‖S.overlap n‖ ^ 2 - ‖S.overlap n₀‖ ^ 2)) /
          ‖S.overlap n₀‖ ^ 2 * (Real.exp (-(Δ * τ)) + Real.exp (-(Δ * (t - τ)))) := by
  have ht : 0 ≤ t := hτ.trans hτt
  set E₀ := S.energy n₀
  set z := ‖S.overlap n₀‖ ^ 2
  set O₀ := S.matrixElement n₀ n₀
  set K₂ := ∑' n, ‖S.overlap n‖ ^ 2 - z
  set K₃ := ∑' p : ι × ι, ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖ -
    ‖S.overlap n₀‖ * ‖O₀‖ * ‖S.overlap n₀‖
  set c := Real.exp (-(Δ * τ)) + Real.exp (-(Δ * (t - τ)))
  set A := S.twoPoint t * Real.exp (E₀ * t)
  set B := S.threePoint t τ * (Real.exp (E₀ * t) : ℂ)
  have hz : 0 < z := pow_pos (norm_pos_iff.2 h₀) 2
  have hzA : z ≤ A := sq_norm_overlap_le_twoPoint_mul_exp h hZ ht
  have hA₂ : A - z ≤ K₂ * Real.exp (-(Δ * t)) := twoPoint_mul_exp_sub_le h hZ ht
  have hB₃ : ‖B - (z : ℂ) * O₀‖ ≤ K₃ * c := by
    rw [show ((z : ℝ) : ℂ) = (‖S.overlap n₀‖ : ℂ) ^ 2 by simp only [z, ofReal_pow]]
    exact norm_threePoint_mul_exp_sub_le h hO hτ hτt
  have hK₂ : 0 ≤ K₂ := by
    have := Real.exp_pos (-(Δ * t))
    nlinarith
  have hc : 0 < c := by positivity
  -- the decay `e^{-Δ t}` of the two-point remainder is dominated by `c`
  have htc : Real.exp (-(Δ * t)) ≤ c :=
    le_add_of_le_of_nonneg (Real.exp_le_exp.2 (by nlinarith [h.pos])) (Real.exp_pos _).le
  -- dividing both correlators by the ground-state decay does not change their ratio
  have hratio : S.threePoint t τ / S.twoPoint t = B / (A : ℂ) := by
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
    _ ≤ (K₃ * c + ‖O₀‖ * (K₂ * c)) * A := by
        gcongr
        exact add_nonneg (le_trans (norm_nonneg _) hB₃) (by positivity)
    _ = (K₃ + ‖O₀‖ * K₂) * c * A := by ring

/-- **The ratio method.** Under a spectral gap, the ratio of the three-point to the two-point
correlator converges to the ground-state matrix element `⟨0|O|0⟩` along any filter on which both
the operator time `τ` and the sink-operator separation `t - τ` tend to infinity. -/
theorem tendsto_threePoint_div_twoPoint (h : S.HasSpectralGap n₀ Δ)
    (hZ : Summable fun n => ‖S.overlap n‖ ^ 2)
    (hO : Summable fun p : ι × ι =>
      ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖)
    (h₀ : S.overlap n₀ ≠ 0) {α : Type*} {l : Filter α} {t τ : α → ℝ}
    (hτ : Tendsto τ l atTop) (htτ : Tendsto (fun a => t a - τ a) l atTop) :
    Tendsto (fun a => S.threePoint (t a) (τ a) / S.twoPoint (t a)) l
      (𝓝 (S.matrixElement n₀ n₀)) := by
  set C := ((∑' p : ι × ι, ‖S.overlap p.1‖ * ‖S.matrixElement p.1 p.2‖ * ‖S.overlap p.2‖ -
      ‖S.overlap n₀‖ * ‖S.matrixElement n₀ n₀‖ * ‖S.overlap n₀‖) +
    ‖S.matrixElement n₀ n₀‖ * (∑' n, ‖S.overlap n‖ ^ 2 - ‖S.overlap n₀‖ ^ 2)) /
      ‖S.overlap n₀‖ ^ 2
  have hexp : ∀ {f : α → ℝ}, Tendsto f l atTop →
      Tendsto (fun a => Real.exp (-(Δ * f a))) l (𝓝 0) := fun hf =>
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hf.const_mul_atTop h.pos)
  have hbound : Tendsto (fun a => C * (Real.exp (-(Δ * τ a)) + Real.exp (-(Δ * (t a - τ a)))))
      l (𝓝 0) := by
    simpa using ((hexp hτ).add (hexp htτ)).const_mul C
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hbound
  filter_upwards [hτ.eventually_ge_atTop 0, htτ.eventually_ge_atTop 0] with a ha hta
  exact norm_threePoint_div_twoPoint_sub_le h hZ hO h₀ ha (sub_nonneg.1 hta)

end SpectralData

end Correlator
end Lattice
end QFT
end EpsilonEridani
