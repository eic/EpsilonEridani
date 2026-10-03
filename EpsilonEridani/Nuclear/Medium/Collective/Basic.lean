/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Azimuthal harmonics of an event at finite multiplicity

An *event* is a finite family `φ : ι → AddCircle T` of azimuthal angles; its multiplicity is
`M = Fintype.card ι`. For the physical period `T = 2π` the Fourier monomial `fourier n` of
Mathlib is `φ ↦ e^{i n φ}`, and every definition below is stated through it, so the
normalisation of the harmonics is Mathlib's.

* The `Q`-vector of harmonic `n` is `Q_n = ∑ⱼ e^{i n φⱼ}` (`qVector`).
* The anisotropy coefficient of harmonic `n` of a single-particle distribution `μ` on the circle
  is `V_n = ∫ e^{i n φ} dμ` (`anisotropyCoeff`). Its modulus is the coefficient usually written
  `vₙ`, and its phase is `n` times the symmetry-plane angle. When `μ` has a density `f` with
  respect to the normalised Haar measure, `V_n` is the Fourier coefficient of `f` of index `-n`
  (`anisotropyCoeff_withDensity`). The coefficient is a parameter of the distribution, not an
  observable of a single event.

The squared modulus of the `Q`-vector contains the *self-correlation* `M` of every particle with
itself (`norm_qVector_sq`). For particles drawn independently from `μ`, its expectation is
`M + M (M - 1) |V_n|²` (`integral_norm_qVector_sq`). The naive estimator `|Q_n|² / M²` is
therefore biased by `(1 - |V_n|²) / M` (`integral_norm_qVector_sq_div_card_sq`). Subtracting the
self-correlation and normalising by the number `M (M - 1)` of ordered pairs of distinct particles
gives the two-particle correlation `⟨2⟩` (`twoParticleCorrelation`). Its expectation is exactly
`|V_n|²` at every multiplicity `M ≥ 2` (`integral_twoParticleCorrelation`). This is the sense in
which `|V_n|` is well posed at finite multiplicity.

Independence enters only through pairs of particles, so the expectations are stated under
pairwise independence. `iIndepFun.indepFun` supplies that from mutual independence, and the
product measure `Measure.pi` is the canonical model (`integral_twoParticleCorrelation_pi`).

A common rotation `φⱼ ↦ φⱼ + ψ` of all angles multiplies `Q_n` and `V_n` by the phase
`e^{i n ψ}`, so their moduli and `⟨2⟩` are invariant (`norm_qVector_add_const`,
`twoParticleCorrelation_add_const`, `norm_anisotropyCoeff_map_add`). The coefficient itself
is not: it is unchanged exactly when it vanishes or `e^{i n ψ} = 1`
(`anisotropyCoeff_map_add_eq_self_iff`). An anisotropy coefficient is therefore only defined
relative to a reference angle, and only its modulus is a rotation-invariant property of the
distribution.

## Main definitions

* `EpsilonEridani.Nuclear.Medium.Collective.qVector n φ`: the `Q`-vector `∑ⱼ e^{i n φⱼ}`.
* `EpsilonEridani.Nuclear.Medium.Collective.twoParticleCorrelation n φ`: the single-event
  two-particle correlation `⟨2⟩ = (|Q_n|² - M) / (M (M - 1))`.
* `EpsilonEridani.Nuclear.Medium.Collective.anisotropyCoeff μ n`: the coefficient
  `∫ e^{i n φ} dμ` of a distribution `μ` on the circle.

## Main statements

* `norm_qVector_sq`: `|Q_n|² = M + ∑_{j ≠ k} e^{i n φⱼ} conj (e^{i n φₖ})`.
* `integral_norm_qVector_sq`: `E |Q_n|² = M + M (M - 1) |V_n|²` for independent draws.
* `integral_twoParticleCorrelation`: `E ⟨2⟩ = |V_n|²` for independent draws and `M ≥ 2`.
* `anisotropyCoeff_map_add`: rotating the distribution by `ψ` multiplies `V_n` by `e^{i n ψ}`.

## References

* A. Bilandzic, R. Snellings and S. Voloshin, *Flow analysis with cumulants: direct
  calculations*, Phys. Rev. C 83 (2011) 044913, arXiv:1010.0233, §II.
* N. Borghini, P. M. Dinh and J.-Y. Ollitrault, *Flow analysis from multiparticle azimuthal
  correlations*, Phys. Rev. C 64 (2001) 054901, arXiv:nucl-th/0105040.
* S. Voloshin and Y. Zhang, *Flow study in relativistic nuclear collisions by Fourier expansion
  of azimuthal particle distributions*, Z. Phys. C 70 (1996) 665, arXiv:hep-ph/9407282.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Finset AddCircle
open scoped ComplexConjugate

namespace EpsilonEridani.Nuclear.Medium.Collective

variable {T : ℝ} {ι : Type*} [Fintype ι]

/-! ### The `Q`-vector and the two-particle correlation of one event -/

/-- The `Q`-vector of harmonic `n` of an event `φ`, `Q_n = ∑ⱼ e^{i n φⱼ}`, with the Fourier
monomial `fourier n` of Mathlib as the harmonic. -/
def qVector (n : ℤ) (φ : ι → AddCircle T) : ℂ :=
  ∑ j, fourier n (φ j)

theorem qVector_def (n : ℤ) (φ : ι → AddCircle T) : qVector n φ = ∑ j, fourier n (φ j) :=
  (rfl)

/-- The zeroth harmonic counts the particles: `Q_0 = M`. -/
@[simp]
theorem qVector_zero (φ : ι → AddCircle T) : qVector 0 φ = Fintype.card ι := by
  simp [qVector]

/-- The `Q`-vector of harmonic `-n` is the complex conjugate of that of harmonic `n`. -/
@[simp]
theorem qVector_neg (n : ℤ) (φ : ι → AddCircle T) : qVector (-n) φ = conj (qVector n φ) := by
  simp [qVector]

/-- A common rotation of all angles by `ψ` multiplies the `Q`-vector by `e^{i n ψ}`. -/
theorem qVector_add_const (n : ℤ) (φ : ι → AddCircle T) (ψ : AddCircle T) :
    qVector n (fun j => φ j + ψ) = fourier n ψ * qVector n φ := by
  simp [qVector, Finset.mul_sum, smul_add, toCircle_add, mul_comm]

/-- The modulus of the `Q`-vector is invariant under a common rotation of all angles. -/
@[simp]
theorem norm_qVector_add_const (n : ℤ) (φ : ι → AddCircle T) (ψ : AddCircle T) :
    ‖qVector n (fun j => φ j + ψ)‖ = ‖qVector n φ‖ := by
  simp [qVector_add_const]

/-- The `Q`-vector depends continuously on the angles. -/
@[fun_prop]
theorem continuous_qVector (n : ℤ) : Continuous (qVector (T := T) (ι := ι) n) :=
  continuous_finsetSum _ fun j _ => (fourier n).continuous.comp (continuous_apply j)

/-- The modulus of the `Q`-vector is at most the multiplicity. -/
theorem norm_qVector_le (n : ℤ) (φ : ι → AddCircle T) : ‖qVector n φ‖ ≤ Fintype.card ι := by
  refine (norm_sum_le _ _).trans ?_
  simp

/-- The squared modulus of the `Q`-vector is the self-correlation `M` plus the sum over ordered
pairs of distinct particles of `e^{i n φⱼ} conj (e^{i n φₖ}) = e^{i n (φⱼ - φₖ)}`. -/
theorem norm_qVector_sq [DecidableEq ι] (n : ℤ) (φ : ι → AddCircle T) :
    (‖qVector n φ‖ : ℂ) ^ 2 =
      Fintype.card ι + ∑ j, ∑ k ∈ univ.erase j, fourier n (φ j) * conj (fourier n (φ k)) := by
  simp only [← Complex.mul_conj', qVector, map_sum, Finset.sum_mul_sum]
  refine (Finset.sum_congr rfl fun j _ => (Finset.add_sum_erase _ _ (mem_univ j)).symm).trans ?_
  simp [Complex.mul_conj', Finset.card_univ]

/-- The single-event two-particle correlation `⟨2⟩ = (|Q_n|² - M) / (M (M - 1))`: the squared
modulus of the `Q`-vector with the self-correlation removed, averaged over the `M (M - 1)` ordered
pairs of distinct particles. -/
def twoParticleCorrelation (n : ℤ) (φ : ι → AddCircle T) : ℝ :=
  (‖qVector n φ‖ ^ 2 - Fintype.card ι) / (Fintype.card ι * (Fintype.card ι - 1))

theorem twoParticleCorrelation_def (n : ℤ) (φ : ι → AddCircle T) :
    twoParticleCorrelation n φ =
      (‖qVector n φ‖ ^ 2 - Fintype.card ι) / (Fintype.card ι * (Fintype.card ι - 1)) :=
  (rfl)

/-- The two-particle correlation is the average of `e^{i n (φⱼ - φₖ)}` over ordered pairs of
distinct particles. -/
theorem twoParticleCorrelation_eq_sum [DecidableEq ι] (n : ℤ) (φ : ι → AddCircle T) :
    (twoParticleCorrelation n φ : ℂ) =
      (∑ j, ∑ k ∈ univ.erase j, fourier n (φ j) * conj (fourier n (φ k))) /
        (Fintype.card ι * (Fintype.card ι - 1)) := by
  rw [twoParticleCorrelation]
  push_cast
  rw [norm_qVector_sq]
  ring

/-- The two-particle correlations of harmonics `n` and `-n` coincide. -/
@[simp]
theorem twoParticleCorrelation_neg (n : ℤ) (φ : ι → AddCircle T) :
    twoParticleCorrelation (-n) φ = twoParticleCorrelation n φ := by
  simp [twoParticleCorrelation]

/-- The two-particle correlation is invariant under a common rotation of all angles. -/
@[simp]
theorem twoParticleCorrelation_add_const (n : ℤ) (φ : ι → AddCircle T) (ψ : AddCircle T) :
    twoParticleCorrelation n (fun j => φ j + ψ) = twoParticleCorrelation n φ := by
  simp [twoParticleCorrelation]

/-! ### The anisotropy coefficient of a distribution on the circle -/

/-- The anisotropy coefficient of harmonic `n` of a single-particle distribution `μ` on the
circle, `V_n = ∫ e^{i n φ} dμ`. Its modulus is the coefficient `vₙ` and its argument is `n` times
the symmetry-plane angle. -/
def anisotropyCoeff (μ : Measure (AddCircle T)) (n : ℤ) : ℂ :=
  ∫ x, fourier n x ∂μ

theorem anisotropyCoeff_def (μ : Measure (AddCircle T)) (n : ℤ) :
    anisotropyCoeff μ n = ∫ x, fourier n x ∂μ :=
  (rfl)

/-- The zeroth coefficient of a probability distribution is `1`. -/
@[simp]
theorem anisotropyCoeff_zero (μ : Measure (AddCircle T)) [IsProbabilityMeasure μ] :
    anisotropyCoeff μ 0 = 1 := by
  simp [anisotropyCoeff]

/-- The coefficient of harmonic `-n` is the complex conjugate of that of harmonic `n`. -/
@[simp]
theorem anisotropyCoeff_neg (μ : Measure (AddCircle T)) (n : ℤ) :
    anisotropyCoeff μ (-n) = conj (anisotropyCoeff μ n) := by
  simp_rw [anisotropyCoeff, fourier_neg, integral_conj]

/-- The coefficients of a probability distribution have modulus at most `1`. -/
theorem norm_anisotropyCoeff_le_one (μ : Measure (AddCircle T)) [IsProbabilityMeasure μ]
    (n : ℤ) : ‖anisotropyCoeff μ n‖ ≤ 1 := by
  refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall
    fun x => ?_)).trans ?_
  · simp
  · simp

/-- For a distribution with density `f` with respect to the normalised Haar measure, the
anisotropy coefficient of harmonic `n` is the Fourier coefficient of `f` of index `-n`. -/
theorem anisotropyCoeff_withDensity [Fact (0 < T)] {f : AddCircle T → NNReal}
    (hf : Measurable f) (n : ℤ) :
    anisotropyCoeff (haarAddCircle.withDensity fun x => f x) n =
      fourierCoeff (fun x => (f x : ℂ)) (-n) := by
  simp [anisotropyCoeff, integral_withDensity_eq_integral_smul hf, fourierCoeff, NNReal.smul_def,
    mul_comm]

/-- Rotating a distribution by `ψ` multiplies its anisotropy coefficient by `e^{i n ψ}`. -/
theorem anisotropyCoeff_map_add (μ : Measure (AddCircle T)) (n : ℤ) (ψ : AddCircle T) :
    anisotropyCoeff (μ.map (· + ψ)) n = fourier n ψ * anisotropyCoeff μ n := by
  simp only [anisotropyCoeff, ← integral_const_mul]
  rw [integral_map (measurable_add_const ψ).aemeasurable
    (fourier n).continuous.aestronglyMeasurable]
  congr 1 with x
  simp [smul_add, toCircle_add, mul_comm]

/-- The modulus of the anisotropy coefficient is invariant under rotations. -/
@[simp]
theorem norm_anisotropyCoeff_map_add (μ : Measure (AddCircle T)) (n : ℤ) (ψ : AddCircle T) :
    ‖anisotropyCoeff (μ.map (· + ψ)) n‖ = ‖anisotropyCoeff μ n‖ := by
  simp [anisotropyCoeff_map_add]

/-- The anisotropy coefficient itself is not rotation invariant: rotating by `ψ` leaves it
unchanged exactly when it vanishes or `e^{i n ψ} = 1`. -/
theorem anisotropyCoeff_map_add_eq_self_iff (μ : Measure (AddCircle T)) (n : ℤ)
    (ψ : AddCircle T) :
    anisotropyCoeff (μ.map (· + ψ)) n = anisotropyCoeff μ n ↔
      anisotropyCoeff μ n = 0 ∨ fourier n ψ = 1 := by
  simp [anisotropyCoeff_map_add, mul_left_eq_self₀, or_comm]

/-! ### Expectations for independent draws -/

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {μ : Measure (AddCircle T)} {φ : ι → Ω → AddCircle T}

omit [IsProbabilityMeasure P] in
/-- The expectation of `e^{i n φ}` for a particle with distribution `μ` is `V_n`. -/
theorem integral_fourier_comp {X : Ω → AddCircle T} (hX : AEMeasurable X P) (hμ : P.map X = μ)
    (n : ℤ) : ∫ ω, fourier n (X ω) ∂P = anisotropyCoeff μ n := by
  subst hμ
  exact (integral_map hX (fourier n).continuous.aestronglyMeasurable).symm

omit [IsProbabilityMeasure P] in
/-- For two independent particles with distribution `μ`, the expectation of
`e^{i n φ} conj (e^{i n φ'}) = e^{i n (φ - φ')}` is `|V_n|²`. -/
theorem integral_fourier_mul_conj_fourier {X Y : Ω → AddCircle T} (hXY : IndepFun X Y P)
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (hμX : P.map X = μ) (hμY : P.map Y = μ)
    (n : ℤ) :
    ∫ ω, fourier n (X ω) * conj (fourier n (Y ω)) ∂P = (‖anisotropyCoeff μ n‖ : ℂ) ^ 2 := by
  rw [hXY.integral_fun_comp_mul_comp (f := fun x => fourier n x)
      (g := fun y => conj (fourier n y)) hX hY
      (fourier n).continuous.aestronglyMeasurable
      (Complex.continuous_conj.comp (fourier n).continuous).aestronglyMeasurable]
  simp only [integral_conj, integral_fourier_comp hX hμX, integral_fourier_comp hY hμY,
    Complex.mul_conj']

variable (hφ : ∀ j, AEMeasurable (φ j) P) (hμ : ∀ j, P.map (φ j) = μ)
  (hind : Pairwise fun j k => IndepFun (φ j) (φ k) P)
include hφ hμ

/-- The expectation of the `Q`-vector of `M` particles with distribution `μ` is `M V_n`. -/
theorem integral_qVector (n : ℤ) :
    ∫ ω, qVector n (fun j => φ j ω) ∂P = Fintype.card ι * anisotropyCoeff μ n := by
  simp_rw [qVector]
  rw [integral_finsetSum _ fun j _ => Integrable.of_bound (f := fun ω => fourier n (φ j ω))
      ((fourier n).continuous.measurable.comp_aemeasurable (hφ j)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by simp)]
  simp only [integral_fourier_comp (hφ _) (hμ _), sum_const, card_univ, nsmul_eq_mul]

include hind

/-- **Expectation of the squared `Q`-vector.** For `M` pairwise independent particles with
distribution `μ`, `E |Q_n|² = M + M (M - 1) |V_n|²`. The term `M` is the self-correlation. -/
theorem integral_norm_qVector_sq (n : ℤ) :
    ∫ ω, ‖qVector n (fun j => φ j ω)‖ ^ 2 ∂P =
      Fintype.card ι + Fintype.card ι * (Fintype.card ι - 1) * ‖anisotropyCoeff μ n‖ ^ 2 := by
  classical
  have hcount : ∑ j : ι, ∑ k ∈ univ.erase j, (‖anisotropyCoeff μ n‖ : ℂ) ^ 2 =
      Fintype.card ι * (Fintype.card ι - 1) * (‖anisotropyCoeff μ n‖ : ℂ) ^ 2 := by
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
    · simp [Finset.univ_eq_empty_iff.2 (Fintype.card_eq_zero_iff.1 h), h]
    · simp [Finset.card_erase_of_mem, Finset.card_univ, Nat.cast_sub h]
      ring
  have hpair : ∀ j, ∀ k ∈ univ.erase j,
      Integrable (fun ω => fourier n (φ j ω) * conj (fourier n (φ k ω))) P := fun j k _ =>
    .of_bound (((fourier n).continuous.measurable.comp_aemeasurable (hφ j)).mul
      ((Complex.continuous_conj.comp (fourier n).continuous).measurable.comp_aemeasurable
        (hφ k))).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun ω => by simp)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  simp_rw [norm_qVector_sq]
  simp only [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ (hpair j)), integral_finsetSum _ fun j _ =>
      integrable_finsetSum _ (hpair j)]
  simp_rw [fun j => integral_finsetSum _ (hpair j)]
  have hjk : ∀ j, ∀ k ∈ univ.erase j,
      ∫ ω, fourier n (φ j ω) * conj (fourier n (φ k ω)) ∂P =
        (‖anisotropyCoeff μ n‖ : ℂ) ^ 2 := fun j k hk =>
    integral_fourier_mul_conj_fourier (hind (Finset.ne_of_mem_erase hk).symm) (hφ j) (hφ k)
      (hμ j) (hμ k) n
  simp only [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl (hjk j), hcount]
  simp

/-- **The naive estimator is biased.** For `M ≥ 1` pairwise independent particles with
distribution `μ`, the expectation of `|Q_n|² / M²` exceeds `|V_n|²` by the self-correlation term
`(1 - |V_n|²) / M`. -/
theorem integral_norm_qVector_sq_div_card_sq [Nonempty ι] (n : ℤ) :
    ∫ ω, ‖qVector n (fun j => φ j ω)‖ ^ 2 / (Fintype.card ι : ℝ) ^ 2 ∂P =
      ‖anisotropyCoeff μ n‖ ^ 2 + (1 - ‖anisotropyCoeff μ n‖ ^ 2) / Fintype.card ι := by
  have hM : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [integral_div, integral_norm_qVector_sq hφ hμ hind]
  field_simp
  ring

/-- **The two-particle correlation is unbiased.** For `M ≥ 2` pairwise independent particles
with distribution `μ`, the expectation of `⟨2⟩` is exactly `|V_n|²`. -/
theorem integral_twoParticleCorrelation (hM : 1 < Fintype.card ι) (n : ℤ) :
    ∫ ω, twoParticleCorrelation n (fun j => φ j ω) ∂P = ‖anisotropyCoeff μ n‖ ^ 2 := by
  have h1 : (1 : ℝ) < Fintype.card ι := by exact_mod_cast hM
  have hM0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have hM1 : (Fintype.card ι : ℝ) - 1 ≠ 0 := by linarith
  have hint : Integrable (fun ω => ‖qVector n (fun j => φ j ω)‖ ^ 2) P :=
    .of_bound ((((continuous_qVector n).norm.pow 2).measurable.comp_aemeasurable
      (AEMeasurable.of_eval hφ))).aestronglyMeasurable
      ((Fintype.card ι : ℝ) ^ 2) (Filter.Eventually.of_forall fun ω => by
        simp only [norm_pow, norm_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_qVector_le n _) 2)
  simp_rw [twoParticleCorrelation]
  simp [integral_div, integral_sub hint (integrable_const _), integral_norm_qVector_sq hφ hμ hind]
  field_simp

end Expectation

/-- **Independent draws.** For `M ≥ 2` particles drawn independently from a probability
distribution `μ` on the circle, the expectation of `⟨2⟩` is `|V_n|²`. -/
theorem integral_twoParticleCorrelation_pi (μ : Measure (AddCircle T)) [IsProbabilityMeasure μ]
    (hM : 1 < Fintype.card ι) (n : ℤ) :
    ∫ φ, twoParticleCorrelation n φ ∂(Measure.pi fun _ : ι => μ) = ‖anisotropyCoeff μ n‖ ^ 2 := by
  have hind : iIndepFun (fun (j : ι) (φ : ι → AddCircle T) => φ j)
      (Measure.pi fun _ : ι => μ) :=
    iIndepFun_pi (X := fun (_ : ι) (x : AddCircle T) => x) fun _ => aemeasurable_id
  exact integral_twoParticleCorrelation (P := Measure.pi fun _ : ι => μ)
    (φ := fun j (x : ι → AddCircle T) => x j) (fun j => (measurable_pi_apply j).aemeasurable)
    (fun j => (measurePreserving_eval (fun _ : ι => μ) j).map_eq)
    (fun _ _ hjk => hind.indepFun hjk) hM n

end EpsilonEridani.Nuclear.Medium.Collective
