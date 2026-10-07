/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The pocket formula for double parton scattering

In double parton scattering two hard processes `A` and `B` take place in one collision of two
hadrons. In collinear factorisation the cross section is an integral of two double parton
distributions, one for each hadron, against the two partonic cross sections:

`σ_DPS = (m/2) ∫ F(p₁, p₂, y) F'(p₁', p₂', y) σ̂_A(p₁, p₁') σ̂_B(p₂, p₂')`,

integrated over the parton labels `pᵢ`, `pᵢ'` (flavour and momentum fraction) and the transverse
separation `y` of the two partons in each hadron. Here `m = 1` when the two processes are
identical and `m = 2` otherwise.

If the double parton distributions factorise into single-parton densities times a transverse
profile, `F(p₁, p₂, y) = f(p₁) f(p₂) G(y)`, the cross section collapses to the *pocket formula*
`σ_DPS = (m/2) σ_A σ_B / σ_eff`, with `1/σ_eff = ∫ G(y) G'(y) dy`. This file proves that
statement with the factorisation as an explicit hypothesis: it is a model assumption, not a
property of QCD.

The parton labels form an arbitrary measure space `(P, ν)` and the transverse separation an
arbitrary measure space `(T, μ)`. For physical applications `P` is `Flavour × ℝ`, with counting
measure on the flavours and Lebesgue measure on the momentum fraction, and `T` is the transverse
plane `EuclideanSpace ℝ (Fin 2)`.

## Main definitions

* `singleScatteringCrossSection ν f f' σ`: the collinear single-scattering cross section
  `∫ f(p) f'(p') σ(p, p')`.
* `orderedDPSIntegral ν μ F F' σ₁ σ₂`: the double-scattering integral in which the first parton
  of each hadron enters `σ₁` and the second enters `σ₂`.
* `dpsCrossSection ν μ F F' σ A B`: the double-parton-scattering cross section, half the sum of
  the ordered integrals over the ordered assignments `{(A, B), (B, A)}` of the two processes to
  the two labelled parton pairs.
* `effectiveCrossSection μ G G'`: the effective cross section `(∫ G G')⁻¹` of two transverse
  profiles.
* `gaussianProfile w`: the normalised Gaussian transverse profile of width `w`.

## Main results

* `dpsCrossSection_eq_mul_orderedDPSIntegral`: for double parton distributions symmetric under
  exchange of their two partons, `σ_DPS = (m/2) × (ordered integral)`, where `m` is `1` for
  identical processes and `2` otherwise.
* `dpsCrossSection_eq_mul_div_effectiveCrossSection`: the pocket formula under the factorisation
  hypothesis.
* `effectiveCrossSection_le_measureReal`: the Cauchy-Schwarz bound: a normalised profile
  vanishing outside a set `S` has `σ_eff ≤ |S|`.
* `effectiveCrossSection_indicator`: the uniform profile on `S` saturates that bound.
* `effectiveCrossSection_gaussianProfile`: two Gaussian profiles of widths `w`, `w'` have
  `σ_eff = 2π(w² + w'²)`, so `4πw²` for equal widths.

## References

* N. Paver and D. Treleani, *Multi-quark scattering and large-pT jet production in hadronic
  collisions*, Nuovo Cim. A70 (1982) 215.
* M. Diehl, D. Ostermeier and A. Schäfer, *Elements of a theory for multiparton interactions in
  QCD*, JHEP 1203 (2012) 089, arXiv:1111.0910.
* J. R. Gaunt and W. J. Stirling, *Double parton distributions incorporating perturbative QCD
  evolution and momentum and quark number sum rules*, JHEP 1003 (2010) 005, arXiv:0910.4347.
-/

public section

noncomputable section

open MeasureTheory Real

namespace EpsilonEridani.Particles.Parton.DoubleParton

variable {P T Proc : Type*} [MeasurableSpace P] [MeasurableSpace T]

/-! ### The single- and double-scattering cross sections -/

/-- The collinear single-scattering cross section `∫ f(p) f'(p') σ(p, p') dν(p) dν(p')`, for
parton densities `f` and `f'` of the two hadrons and a partonic cross section `σ`. -/
def singleScatteringCrossSection (ν : Measure P) (f f' : P → ℝ) (σ : P → P → ℝ) : ℝ :=
  ∫ q : P × P, f q.1 * f' q.2 * σ q.1 q.2 ∂ν.prod ν

/-- The ordered double-scattering integral. A point of the domain is
`(((p₁, p₁'), (p₂, p₂')), y)`: the first parton of each hadron, `p₁` and `p₁'`, enter the partonic
cross section `σ₁`, the second partons `p₂` and `p₂'` enter `σ₂`, and `y` is the transverse
separation shared by the two double parton distributions `F` and `F'`. -/
def orderedDPSIntegral (ν : Measure P) (μ : Measure T) (F F' : P → P → T → ℝ)
    (σ₁ σ₂ : P → P → ℝ) : ℝ :=
  ∫ z : ((P × P) × (P × P)) × T,
    F z.1.1.1 z.1.2.1 z.2 * F' z.1.1.2 z.1.2.2 z.2 * (σ₁ z.1.1.1 z.1.1.2 * σ₂ z.1.2.1 z.1.2.2)
    ∂((ν.prod ν).prod (ν.prod ν)).prod μ

/-- The double-parton-scattering cross section for the two processes `A` and `B`, with partonic
cross sections `σ A` and `σ B`. The final state `{A, B}` is reached by every ordered assignment
of the processes to the two labelled parton pairs, `(A, B)` and `(B, A)` (which coincide when the
processes do), whence the sum over `{(A, B), (B, A)}`, and relabelling the two parton pairs
describes the same collision, whence the overall `1/2`. -/
def dpsCrossSection [DecidableEq Proc] (ν : Measure P) (μ : Measure T) (F F' : P → P → T → ℝ)
    (σ : Proc → P → P → ℝ) (A B : Proc) : ℝ :=
  (1 / 2) * ∑ q ∈ ({(A, B), (B, A)} : Finset (Proc × Proc)),
    orderedDPSIntegral ν μ F F' (σ q.1) (σ q.2)

theorem singleScatteringCrossSection_def (ν : Measure P) (f f' : P → ℝ) (σ : P → P → ℝ) :
    singleScatteringCrossSection ν f f' σ = ∫ q : P × P, f q.1 * f' q.2 * σ q.1 q.2 ∂ν.prod ν :=
  (rfl)

theorem orderedDPSIntegral_def (ν : Measure P) (μ : Measure T) (F F' : P → P → T → ℝ)
    (σ₁ σ₂ : P → P → ℝ) :
    orderedDPSIntegral ν μ F F' σ₁ σ₂ =
      ∫ z : ((P × P) × (P × P)) × T,
        F z.1.1.1 z.1.2.1 z.2 * F' z.1.1.2 z.1.2.2 z.2 *
          (σ₁ z.1.1.1 z.1.1.2 * σ₂ z.1.2.1 z.1.2.2)
        ∂((ν.prod ν).prod (ν.prod ν)).prod μ :=
  (rfl)

theorem dpsCrossSection_def [DecidableEq Proc] (ν : Measure P) (μ : Measure T)
    (F F' : P → P → T → ℝ) (σ : Proc → P → P → ℝ) (A B : Proc) :
    dpsCrossSection ν μ F F' σ A B =
      (1 / 2) * ∑ q ∈ ({(A, B), (B, A)} : Finset (Proc × Proc)),
        orderedDPSIntegral ν μ F F' (σ q.1) (σ q.2) :=
  (rfl)

/-- The double-parton-scattering cross section does not depend on the order in which the two
processes are named. -/
theorem dpsCrossSection_comm [DecidableEq Proc] (ν : Measure P) (μ : Measure T)
    (F F' : P → P → T → ℝ) (σ : Proc → P → P → ℝ) (A B : Proc) :
    dpsCrossSection ν μ F F' σ B A = dpsCrossSection ν μ F F' σ A B := by
  rw [dpsCrossSection, dpsCrossSection, Finset.pair_comm]

/-! ### The symmetry factor -/

section Symmetry

variable {ν : Measure P} {μ : Measure T} [SFinite ν] [SFinite μ]

/-- For double parton distributions symmetric under exchange of their two partons, the ordered
integral does not depend on which parton pair enters which partonic cross section. -/
theorem orderedDPSIntegral_comm {F F' : P → P → T → ℝ} (hF : ∀ p₁ p₂ y, F p₂ p₁ y = F p₁ p₂ y)
    (hF' : ∀ p₁ p₂ y, F' p₂ p₁ y = F' p₁ p₂ y) (σ₁ σ₂ : P → P → ℝ) :
    orderedDPSIntegral ν μ F F' σ₂ σ₁ = orderedDPSIntegral ν μ F F' σ₁ σ₂ := by
  -- Exchange the two parton pairs, a measure-preserving equivalence of the domain.
  let e : ((P × P) × (P × P)) × T ≃ᵐ ((P × P) × (P × P)) × T :=
    MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl T)
  have he : MeasurePreserving e (((ν.prod ν).prod (ν.prod ν)).prod μ)
      (((ν.prod ν).prod (ν.prod ν)).prod μ) :=
    Measure.measurePreserving_swap.prod (MeasurePreserving.id μ)
  rw [orderedDPSIntegral, orderedDPSIntegral, ← he.integral_comp']
  congr 1 with z
  -- `MeasurableEquiv.prodCongr` and `MeasurableEquiv.prodComm` have no application `simp` lemmas;
  -- `e` swaps the two parton pairs by construction.
  have he_apply : e z = ((z.1.2, z.1.1), z.2) := rfl
  rw [he_apply, hF, hF']
  ring

/-- **The factor `m/2`.** For double parton distributions symmetric under exchange of their two
partons, the double-parton-scattering cross section is `m/2` times the ordered integral, where
`m` is `1` for identical processes and `2` otherwise: the number of distinct assignments of the
processes to the two parton pairs. -/
theorem dpsCrossSection_eq_mul_orderedDPSIntegral [DecidableEq Proc] {F F' : P → P → T → ℝ}
    (hF : ∀ p₁ p₂ y, F p₂ p₁ y = F p₁ p₂ y) (hF' : ∀ p₁ p₂ y, F' p₂ p₁ y = F' p₁ p₂ y)
    (σ : Proc → P → P → ℝ) (A B : Proc) :
    dpsCrossSection ν μ F F' σ A B =
      ((if A = B then 1 else 2) / 2 : ℝ) * orderedDPSIntegral ν μ F F' (σ A) (σ B) := by
  rw [dpsCrossSection]
  split_ifs with h
  · subst h
    simp
  · rw [Finset.sum_pair (by simp [h]), orderedDPSIntegral_comm hF hF' (σ A) (σ B)]
    ring

end Symmetry

/-! ### The effective cross section and the pocket formula -/

/-- The effective cross section `σ_eff = (∫ G(y) G'(y) dμ(y))⁻¹` of two transverse profiles. Its
inverse is the overlap of the profiles, the probability density for the two pairs of partons to
meet at the same transverse separation. -/
def effectiveCrossSection (μ : Measure T) (G G' : T → ℝ) : ℝ :=
  (∫ y, G y * G' y ∂μ)⁻¹

theorem effectiveCrossSection_def (μ : Measure T) (G G' : T → ℝ) :
    effectiveCrossSection μ G G' = (∫ y, G y * G' y ∂μ)⁻¹ :=
  (rfl)

theorem effectiveCrossSection_comm (μ : Measure T) (G G' : T → ℝ) :
    effectiveCrossSection μ G' G = effectiveCrossSection μ G G' := by
  simp_rw [effectiveCrossSection, mul_comm]

section Factorised

variable {ν : Measure P} {μ : Measure T} [SFinite ν] [SFinite μ]

/-- Under the factorisation hypothesis, `F(p₁, p₂, y) = f(p₁) f(p₂) G(y)` and likewise for `F'`,
the ordered integral is the product of the two single-scattering cross sections and the overlap
of the transverse profiles. -/
theorem orderedDPSIntegral_eq_of_factorised {F F' : P → P → T → ℝ} {f f' : P → ℝ} {G G' : T → ℝ}
    (hF : ∀ p₁ p₂ y, F p₁ p₂ y = f p₁ * f p₂ * G y)
    (hF' : ∀ p₁ p₂ y, F' p₁ p₂ y = f' p₁ * f' p₂ * G' y) (σ₁ σ₂ : P → P → ℝ) :
    orderedDPSIntegral ν μ F F' σ₁ σ₂ =
      singleScatteringCrossSection ν f f' σ₁ * singleScatteringCrossSection ν f f' σ₂ *
        ∫ y, G y * G' y ∂μ := by
  rw [orderedDPSIntegral, singleScatteringCrossSection, singleScatteringCrossSection,
    ← integral_prod_mul, ← integral_prod_mul]
  congr 1 with z
  rw [hF, hF']
  ring

/-- **The pocket formula.** If both double parton distributions factorise into single-parton
densities times a transverse profile, `F(p₁, p₂, y) = f(p₁) f(p₂) G(y)` and
`F'(p₁', p₂', y) = f'(p₁') f'(p₂') G'(y)`, then `σ_DPS = (m/2) σ_A σ_B / σ_eff`, with
`m` as in `dpsCrossSection_eq_mul_orderedDPSIntegral` and `σ_eff` the effective cross section of
`G` and `G'`. -/
theorem dpsCrossSection_eq_mul_div_effectiveCrossSection [DecidableEq Proc] {F F' : P → P → T → ℝ}
    {f f' : P → ℝ} {G G' : T → ℝ} (hF : ∀ p₁ p₂ y, F p₁ p₂ y = f p₁ * f p₂ * G y)
    (hF' : ∀ p₁ p₂ y, F' p₁ p₂ y = f' p₁ * f' p₂ * G' y) (σ : Proc → P → P → ℝ) (A B : Proc) :
    dpsCrossSection ν μ F F' σ A B =
      ((if A = B then 1 else 2) / 2 : ℝ) * singleScatteringCrossSection ν f f' (σ A) *
        singleScatteringCrossSection ν f f' (σ B) / effectiveCrossSection μ G G' := by
  have hsymm : ∀ p₁ p₂ y, F p₂ p₁ y = F p₁ p₂ y := fun p₁ p₂ y => by
    rw [hF, hF]; ring
  have hsymm' : ∀ p₁ p₂ y, F' p₂ p₁ y = F' p₁ p₂ y := fun p₁ p₂ y => by
    rw [hF', hF']; ring
  rw [dpsCrossSection_eq_mul_orderedDPSIntegral hsymm hsymm',
    orderedDPSIntegral_eq_of_factorised hF hF', effectiveCrossSection, div_inv_eq_mul]
  ring

end Factorised

/-! ### The Cauchy-Schwarz bound -/

section Bound

variable {μ : Measure T}

/-- **The Cauchy-Schwarz bound on the effective cross section.** A normalised transverse profile
that vanishes outside a set `S` of finite measure has `σ_eff ≤ |S|`: a profile confined to a
region cannot have an effective cross section larger than the region. -/
theorem effectiveCrossSection_le_measureReal {G : T → ℝ} {S : Set T} (hμS : μ S ≠ ⊤)
    (hG : ∀ y ∉ S, G y = 0) (hnorm : ∫ y, G y ∂μ = 1) :
    effectiveCrossSection μ G G ≤ μ.real S := by
  have hint : Integrable G μ := Integrable.of_integral_ne_zero (by simp [hnorm])
  -- A profile that is not square-integrable has `∫ G² = 0`, so `σ_eff = 0⁻¹ = 0`.
  by_cases hG2 : MemLp G 2 μ
  swap
  · have : ¬Integrable (fun y => G y * G y) μ := by
      simpa only [sq] using mt (memLp_two_iff_integrable_sq hint.aestronglyMeasurable).2 hG2
    rw [effectiveCrossSection, integral_undef this, inv_zero]
    exact measureReal_nonneg
  have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hμS
  -- Cauchy-Schwarz on `S`: `1 = ∫_S G ≤ ∫_S 1 ⬝ |G| ≤ |S|^(1/2) (∫ G²)^(1/2)`.
  have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.restrict S) Real.HolderConjugate.two_two
    (f := fun _ => (1 : ℝ)) (g := |G|) (ae_of_all _ fun _ => zero_le_one)
    (ae_of_all _ fun y => abs_nonneg (G y)) (by simpa using memLp_const (1 : ℝ))
    (by simpa using hG2.abs.restrict S)
  have hsq : ∫ y in S, G y ^ 2 ∂μ = ∫ y, G y * G y ∂μ := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by simp [hG y hy]]
    simp_rw [sq]
  simp only [Pi.abs_apply, one_mul, one_pow, integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul, mul_one, Real.rpow_two, sq_abs, hsq, ← Real.sqrt_eq_rpow] at hcs
  have hle : 1 ≤ ∫ y in S, |G y| ∂μ := by
    rw [← hnorm, ← setIntegral_eq_integral_of_forall_compl_eq_zero hG]
    exact integral_mono hint.integrableOn hint.abs.integrableOn fun y => le_abs_self (G y)
  have hkey : 1 ≤ μ.real S * ∫ y, G y * G y ∂μ := by
    rw [← Real.one_le_sqrt, Real.sqrt_mul measureReal_nonneg]
    exact hle.trans hcs
  have hpos : 0 < ∫ y, G y * G y ∂μ := by
    refine (integral_nonneg fun y => mul_self_nonneg (G y)).lt_of_ne fun h => ?_
    rw [← h, mul_zero] at hkey
    norm_num at hkey
  rw [effectiveCrossSection, inv_le_iff_one_le_mul₀ hpos]
  exact hkey

/-- The uniform profile `|S|⁻¹ 𝟙_S` on a measurable set `S` has effective cross section `|S|`,
saturating `effectiveCrossSection_le_measureReal`. -/
theorem effectiveCrossSection_indicator {S : Set T} (hS : MeasurableSet S) :
    effectiveCrossSection μ (S.indicator fun _ => (μ.real S)⁻¹)
      (S.indicator fun _ => (μ.real S)⁻¹) = μ.real S := by
  rw [effectiveCrossSection, ← Set.indicator_mul, integral_indicator_const _ hS, smul_eq_mul]
  rcases eq_or_ne (μ.real S) 0 with h | h
  · simp [h]
  · field_simp

end Bound

/-! ### The Gaussian profile -/

/-- The normalised Gaussian transverse profile of width `w`,
`G(y) = exp(-|y|² / (2w²)) / (2π w²)` on the transverse plane. -/
def gaussianProfile (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2))

theorem gaussianProfile_def (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    gaussianProfile w y = (2 * π * w ^ 2)⁻¹ * exp (-‖y‖ ^ 2 / (2 * w ^ 2)) :=
  (rfl)

theorem gaussianProfile_nonneg (w : ℝ) (y : EuclideanSpace ℝ (Fin 2)) :
    0 ≤ gaussianProfile w y := by
  unfold gaussianProfile
  positivity

/-- The Gaussian profile is normalised. -/
theorem integral_gaussianProfile_eq_one {w : ℝ} (hw : w ≠ 0) :
    ∫ y, gaussianProfile w y = 1 := by
  have hw2 : 0 < w ^ 2 := by positivity
  have : (fun y => gaussianProfile w y) = fun y : EuclideanSpace ℝ (Fin 2) =>
      (2 * π * w ^ 2)⁻¹ * exp (-(2 * w ^ 2)⁻¹ * ‖y‖ ^ 2) := by
    ext y
    rw [gaussianProfile]
    congr 2
    ring
  rw [this, integral_const_mul, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity),
    finrank_euclideanSpace_fin]
  norm_num
  field_simp

/-- **The effective cross section of two Gaussian profiles.** For widths `w` and `w'`,
`σ_eff = 2π (w² + w'²)`. -/
theorem effectiveCrossSection_gaussianProfile {w w' : ℝ} (hw : w ≠ 0) (hw' : w' ≠ 0) :
    effectiveCrossSection volume (gaussianProfile w) (gaussianProfile w') =
      2 * π * (w ^ 2 + w' ^ 2) := by
  have hw2 : 0 < w ^ 2 := by positivity
  have hw2' : 0 < w' ^ 2 := by positivity
  set b := (2 * w ^ 2)⁻¹ + (2 * w' ^ 2)⁻¹
  have hb : 0 < b := by positivity
  have : (fun y => gaussianProfile w y * gaussianProfile w' y) =
      fun y : EuclideanSpace ℝ (Fin 2) =>
        ((2 * π * w ^ 2)⁻¹ * (2 * π * w' ^ 2)⁻¹) * exp (-b * ‖y‖ ^ 2) := by
    ext y
    rw [gaussianProfile, gaussianProfile, mul_mul_mul_comm, ← exp_add]
    congr 2
    ring
  rw [effectiveCrossSection, this, integral_const_mul,
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb, finrank_euclideanSpace_fin]
  norm_num [b]
  field_simp
  ring

/-- Two Gaussian profiles of equal width `w` have `σ_eff = 4π w²`. -/
theorem effectiveCrossSection_gaussianProfile_self (w : ℝ) :
    effectiveCrossSection volume (gaussianProfile w) (gaussianProfile w) = 4 * π * w ^ 2 := by
  rcases eq_or_ne w 0 with rfl | hw
  · simp [effectiveCrossSection, gaussianProfile]
  · rw [effectiveCrossSection_gaussianProfile hw hw]
    ring

end EpsilonEridani.Particles.Parton.DoubleParton
