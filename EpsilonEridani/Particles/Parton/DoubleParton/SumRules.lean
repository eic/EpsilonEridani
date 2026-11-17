/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Physlib.Mathematics.KroneckerDelta.Basic
public import EpsilonEridani.Mathematics.MeasureTheory.UnitTriangle
public import EpsilonEridani.Particles.Parton.PDF.ChargeConjugation

/-!
# The sum rules of double parton distributions and their consistency

A double parton distribution `F a₁ a₂ x₁ x₂` of a hadron, integrated over the transverse
separation of the two partons, is the density for finding a parton of species `a₁` with momentum
fraction `x₁` together with a parton of species `a₂` with momentum fraction `x₂`, both at one
common scale. Since the two partons share the hadron's momentum, the pair `(x₁, x₂)` lies in the
unit triangle `x₁, x₂ ≥ 0`, `x₁ + x₂ ≤ 1`.

Gaunt and Stirling proposed two families of sum rules that tie `F` to the single-parton densities
`f` of the same hadron at the same scale. For every species `a₂` and every `0 < x₂ < 1`:

* the **number sum rule**: for every quark flavour `i`, with `N i` the number of valence quarks of
  flavour `i`,
  `∫_0^{1-x₂} dx₁ (F_{q_i a₂} - F_{q̄_i a₂})(x₁, x₂) = (N i + δ_{a₂ q̄_i} - δ_{a₂ q_i}) f_{a₂}(x₂)`:
  once a parton `a₂` has been found, the rest of the hadron carries `N i` valence quarks of flavour
  `i`, one fewer if `a₂` was a quark of that flavour and one more if it was its antiquark;
* the **momentum sum rule**:
  `∑_{a₁} ∫_0^{1-x₂} dx₁ x₁ F_{a₁ a₂}(x₁, x₂) = (1 - x₂) f_{a₂}(x₂)`:
  the rest of the hadron carries the momentum fraction `1 - x₂`.

Here these are the predicates `NumberSumRule` and `MomentumSumRule`, at a fixed scale. They are
stated, not derived from the operator definition of `F`. In QCD the integral over the transverse
separation diverges at small separation, and Diehl, Plößl and Schäfer prove the sum rules for the
renormalised distributions; here `F` is any function of the two species and the two momentum
fractions.

The two families are not independent of the single-parton sum rules. For a distribution that is
symmetric under exchange of the two partons, integrating the number sum rule against `x₂` and the
momentum sum rule of a quark and its antiquark over `x₂` computes one double integral over the
triangle in two ways, and the comparison gives

`N i * ∑ₐ ∫₀¹ x fₐ(x) dx = ∫₀¹ (f_{q_i} - f_{q̄_i})(x) dx`,

the main theorem `mul_sum_mellinMoment_one_eq_valenceNumber`. So the constants `N i` of the
number sum rule are the valence numbers of `f` exactly when `f` carries the full momentum of the
hadron, and conversely the momentum sum rule of the single-parton densities follows from the two
families as soon as one flavour has a nonzero valence number.

## Main definitions

* `DoubleParton.NumberSumRule F f Q2 N`: the number sum rules of `F` with valence numbers `N`.
* `DoubleParton.MomentumSumRule F f Q2`: the momentum sum rules of `F`.
* `DoubleParton.threeQuarkPdf`, `DoubleParton.threeQuarkDpd`: the single and double parton
  distributions of three quarks of one flavour with uniformly distributed momentum fractions.

## Main statements

* `DoubleParton.mul_sum_mellinMoment_one_eq_valenceNumber`: the consistency relation above.
* `DoubleParton.sum_mellinMoment_one_eq_one`: the two families and a single-parton valence sum
  rule with a nonzero valence number imply the single-parton momentum sum rule.
* `DoubleParton.valenceNumber_eq`: the two families and the single-parton momentum sum rule imply
  that the constants of the number sum rule are the valence numbers of the single-parton densities.
* `DoubleParton.numberSumRule_threeQuarkDpd`, `DoubleParton.momentumSumRule_threeQuarkDpd`: the
  three-quark model satisfies both families, with three valence quarks.

## References

* J. R. Gaunt and W. J. Stirling, *Double parton distributions incorporating perturbative QCD
  evolution and momentum and quark number sum rules*, JHEP 1003 (2010) 005, arXiv:0910.4347.
* M. Diehl, P. Plößl and A. Schäfer, *Proof of sum rules for double parton distributions in QCD*,
  Eur. Phys. J. C 79 (2019) 253, arXiv:1811.00289.
-/

public section

noncomputable section

namespace EpsilonEridani.Particles.Parton.DoubleParton

open MeasureTheory Set KroneckerDelta PDF

variable {Flavor : Type}

/-- The **number sum rules** of the double parton distribution `F` at the scale `Q2`, with
valence numbers `N`: for every quark flavour `i`, every species `a`, and every `0 < x₂ < 1`,
`∫_0^{1-x₂} dx₁ (F_{q_i a} - F_{q̄_i a})(x₁, x₂) = (N i + δ_{a q̄_i} - δ_{a q_i}) f_a(x₂, Q2)`. -/
def NumberSumRule [DecidableEq Flavor] (F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ)
    (f : Pdf (Species Flavor)) (Q2 : ℝ) (N : Flavor → ℝ) : Prop :=
  ∀ i a x₂, 0 < x₂ → x₂ < 1 →
    ∫ x₁ in 0..1 - x₂, (F (.quark i) a x₁ x₂ - F (.antiquark i) a x₁ x₂) =
      (N i + δ[a, .antiquark i] - δ[a, .quark i]) * f a x₂ Q2

/-- The **momentum sum rules** of the double parton distribution `F` at the scale `Q2`: for every
species `a` and every `0 < x₂ < 1`,
`∑_b ∫_0^{1-x₂} dx₁ x₁ F_{b a}(x₁, x₂) = (1 - x₂) f_a(x₂, Q2)`. -/
def MomentumSumRule [Fintype Flavor] (F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ)
    (f : Pdf (Species Flavor)) (Q2 : ℝ) : Prop :=
  ∀ a x₂, 0 < x₂ → x₂ < 1 → ∑ b, ∫ x₁ in 0..1 - x₂, x₁ * F b a x₁ x₂ = (1 - x₂) * f a x₂ Q2

theorem numberSumRule_iff [DecidableEq Flavor] {F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ}
    {f : Pdf (Species Flavor)} {Q2 : ℝ} {N : Flavor → ℝ} :
    NumberSumRule F f Q2 N ↔ ∀ i a x₂, 0 < x₂ → x₂ < 1 →
      ∫ x₁ in 0..1 - x₂, (F (.quark i) a x₁ x₂ - F (.antiquark i) a x₁ x₂) =
        (N i + δ[a, .antiquark i] - δ[a, .quark i]) * f a x₂ Q2 :=
  Iff.rfl

theorem momentumSumRule_iff [Fintype Flavor] {F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ}
    {f : Pdf (Species Flavor)} {Q2 : ℝ} :
    MomentumSumRule F f Q2 ↔ ∀ a x₂, 0 < x₂ → x₂ < 1 →
      ∑ b, ∫ x₁ in 0..1 - x₂, x₁ * F b a x₁ x₂ = (1 - x₂) * f a x₂ Q2 :=
  Iff.rfl

/-! ### Integrating the sum rules over the second momentum fraction -/

/-- The number sum rule, weighted with the second momentum fraction and integrated over the unit
triangle:
`∫_{triangle} x₂ (F_{q_i a} - F_{q̄_i a})(x₁, x₂) = (N i + δ_{a q̄_i} - δ_{a q_i}) ∫₀¹ x f_a(x)`.
-/
theorem setIntegral_unitTriangle_mul_sub_eq [DecidableEq Flavor]
    {F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ} {f : Pdf (Species Flavor)} {Q2 : ℝ}
    {N : Flavor → ℝ} (hN : NumberSumRule F f Q2 N) (i : Flavor) (a : Species Flavor)
    (hF : IntegrableOn (fun p : ℝ × ℝ => p.2 * (F (.quark i) a p.1 p.2 -
      F (.antiquark i) a p.1 p.2)) unitTriangle) :
    ∫ p in unitTriangle, p.2 * (F (.quark i) a p.1 p.2 - F (.antiquark i) a p.1 p.2) =
      (N i + δ[a, .antiquark i] - δ[a, .quark i]) * mellinMoment f 1 a Q2 := by
  rw [setIntegral_unitTriangle hF, mellinMoment, ← integral_const_mul,
    ← setIntegral_congr_set (Ioo_ae_eq_Icc (μ := volume)),
    ← setIntegral_congr_set (Ioo_ae_eq_Icc (μ := volume))]
  refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
  dsimp only
  rw [integral_const_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith [hy.2]), hN i a y hy.1 hy.2]
  ring

/-- The momentum sum rule of the species `a`, integrated over the unit triangle:
`∑_b ∫_{triangle} x₁ F_{b a}(x₁, x₂) = ∫₀¹ (1 - x) f_a(x) dx`. -/
theorem sum_setIntegral_unitTriangle_eq [Fintype Flavor]
    {F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ} {f : Pdf (Species Flavor)} {Q2 : ℝ}
    (hM : MomentumSumRule F f Q2) (a : Species Flavor)
    (hF : ∀ b, IntegrableOn (fun p : ℝ × ℝ => p.1 * F b a p.1 p.2) unitTriangle) :
    ∑ b, ∫ p in unitTriangle, p.1 * F b a p.1 p.2 = ∫ x in Icc (0 : ℝ) 1, (1 - x) * f a x Q2 := by
  simp only [setIntegral_unitTriangle (hF _)]
  rw [← integral_finsetSum _ fun b _ => integrableOn_integral_unitTriangle (hF b),
    ← setIntegral_congr_set (Ioo_ae_eq_Icc (μ := volume)),
    ← setIntegral_congr_set (Ioo_ae_eq_Icc (μ := volume))]
  refine setIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
  simp only [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 - y by linarith [hy.2])]
  exact hM a y hy.1 hy.2

/-! ### The consistency of the two families -/

/-- **The consistency of the double-parton sum rules.** If a double parton distribution `F`,
symmetric under exchange of its two partons, satisfies the number sum rules with valence numbers
`N` and the momentum sum rules against the single-parton densities `f`, then for every flavour `i`
`N i * ∑ₐ ∫₀¹ x fₐ(x) dx = ∫₀¹ (f_{q_i} - f_{q̄_i})(x) dx`.

The integrability hypotheses are those of the momentum-weighted distributions `x₁ F_{a q_i}` and
`x₁ F_{a q̄_i}` on the unit triangle, and of `f_{q_i}` and `f_{q̄_i}` on `[0, 1]`. -/
theorem mul_sum_mellinMoment_one_eq_valenceNumber [Fintype Flavor] [DecidableEq Flavor]
    {F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ} {f : Pdf (Species Flavor)} {Q2 : ℝ}
    {N : Flavor → ℝ} (hN : NumberSumRule F f Q2 N) (hM : MomentumSumRule F f Q2)
    (hsymm : ∀ a b x₁ x₂, F b a x₂ x₁ = F a b x₁ x₂) (i : Flavor)
    (hFq : ∀ a, IntegrableOn (fun p : ℝ × ℝ => p.1 * F a (.quark i) p.1 p.2) unitTriangle)
    (hFqbar : ∀ a, IntegrableOn (fun p : ℝ × ℝ => p.1 * F a (.antiquark i) p.1 p.2) unitTriangle)
    (hfq : IntegrableOn (fun x => f (.quark i) x Q2) (Icc 0 1))
    (hfqbar : IntegrableOn (fun x => f (.antiquark i) x Q2) (Icc 0 1)) :
    N i * ∑ a, mellinMoment f 1 a Q2 = valenceNumber f i Q2 := by
  -- The momentum-weighted valence combination `G a`, and its exchange `G a ∘ swap`, which is the
  -- integrand of the number sum rule weighted with `x₂`.
  set G : Species Flavor → ℝ × ℝ → ℝ := fun a p =>
    p.1 * F a (.quark i) p.1 p.2 - p.1 * F a (.antiquark i) p.1 p.2 with hG
  have hswap (a : Species Flavor) : (fun p : ℝ × ℝ => G a p.swap) =
      fun p => p.2 * (F (.quark i) a p.1 p.2 - F (.antiquark i) a p.1 p.2) := by
    funext p
    simp only [hG, Prod.fst_swap, Prod.snd_swap, hsymm]
    ring
  have hGint (a : Species Flavor) : IntegrableOn (G a) unitTriangle := (hFq a).sub (hFqbar a)
  -- First evaluation of `∑ₐ ∫_{triangle} G a`: through the number sum rules.
  have hnumber : ∑ a, ∫ p in unitTriangle, G a p =
      ∑ a, (N i + δ[a, .antiquark i] - δ[a, .quark i]) * mellinMoment f 1 a Q2 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← setIntegral_unitTriangle_comp_swap, hswap]
    refine setIntegral_unitTriangle_mul_sub_eq hN i a ?_
    rw [← hswap]
    exact integrableOn_unitTriangle_comp_swap_iff.2 (hGint a)
  -- Second evaluation: through the momentum sum rules of `q_i` and `q̄_i`.
  have hmomentum : ∑ a, ∫ p in unitTriangle, G a p =
      (∫ x in Icc (0 : ℝ) 1, (1 - x) * f (.quark i) x Q2) -
        ∫ x in Icc (0 : ℝ) 1, (1 - x) * f (.antiquark i) x Q2 := by
    simp only [hG, integral_sub (hFq _) (hFqbar _), Finset.sum_sub_distrib]
    rw [sum_setIntegral_unitTriangle_eq hM _ hFq, sum_setIntegral_unitTriangle_eq hM _ hFqbar]
  -- `∫₀¹ (1 - x) f = ∫₀¹ f - ∫₀¹ x f`.
  have hsplit {g : ℝ → ℝ} (hg : IntegrableOn g (Icc 0 1)) :
      ∫ x in Icc (0 : ℝ) 1, (1 - x) * g x = (∫ x in Icc (0 : ℝ) 1, x ^ 0 * g x) -
        ∫ x in Icc (0 : ℝ) 1, x ^ 1 * g x := by
    have hxg : IntegrableOn (fun x => x * g x) (Icc 0 1) :=
      hg.continuousOn_mul continuousOn_id isCompact_Icc
    simp only [sub_mul, one_mul, pow_zero, pow_one]
    exact integral_sub hg hxg
  have hdelta : ∑ a, (N i + δ[a, .antiquark i] - δ[a, .quark i]) * mellinMoment f 1 a Q2 =
      N i * ∑ a, mellinMoment f 1 a Q2 + mellinMoment f 1 (.antiquark i) Q2 -
        mellinMoment f 1 (.quark i) Q2 := by
    simp [kroneckerDelta, add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.mul_sum]
  have h := hnumber.symm.trans hmomentum
  rw [hdelta, hsplit hfq, hsplit hfqbar] at h
  rw [valenceNumber_def]
  simp only [mellinMoment] at h ⊢
  linarith

/-- **The momentum sum rule from the double-parton sum rules.** If `F` satisfies the number and
momentum sum rules, and the single-parton densities satisfy the valence sum rule of a flavour `i`
whose valence number `N i` is nonzero, then the single-parton densities satisfy the momentum sum
rule `∑ₐ ∫₀¹ x fₐ(x) dx = 1`. -/
theorem sum_mellinMoment_one_eq_one [Fintype Flavor] [DecidableEq Flavor]
    {F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ} {f : Pdf (Species Flavor)} {Q2 : ℝ}
    {N : Flavor → ℝ} (hN : NumberSumRule F f Q2 N) (hM : MomentumSumRule F f Q2)
    (hsymm : ∀ a b x₁ x₂, F b a x₂ x₁ = F a b x₁ x₂) {i : Flavor}
    (hFq : ∀ a, IntegrableOn (fun p : ℝ × ℝ => p.1 * F a (.quark i) p.1 p.2) unitTriangle)
    (hFqbar : ∀ a, IntegrableOn (fun p : ℝ × ℝ => p.1 * F a (.antiquark i) p.1 p.2) unitTriangle)
    (hfq : IntegrableOn (fun x => f (.quark i) x Q2) (Icc 0 1))
    (hfqbar : IntegrableOn (fun x => f (.antiquark i) x Q2) (Icc 0 1))
    (hval : valenceNumber f i Q2 = N i) (hNi : N i ≠ 0) :
    ∑ a, mellinMoment f 1 a Q2 = 1 := by
  have h := mul_sum_mellinMoment_one_eq_valenceNumber hN hM hsymm i hFq hFqbar hfq hfqbar
  rw [hval] at h
  exact (mul_eq_left₀ hNi).1 h

/-- **The constants of the number sum rule are the valence numbers.** If `F` satisfies the number
and momentum sum rules, and the single-parton densities satisfy the momentum sum rule
`∑ₐ ∫₀¹ x fₐ(x) dx = 1`, then the constant `N i` of the number sum rule is the valence number
`∫₀¹ (f_{q_i} - f_{q̄_i})` of the single-parton densities. -/
theorem valenceNumber_eq [Fintype Flavor] [DecidableEq Flavor]
    {F : Species Flavor → Species Flavor → ℝ → ℝ → ℝ} {f : Pdf (Species Flavor)} {Q2 : ℝ}
    {N : Flavor → ℝ} (hN : NumberSumRule F f Q2 N) (hM : MomentumSumRule F f Q2)
    (hsymm : ∀ a b x₁ x₂, F b a x₂ x₁ = F a b x₁ x₂) {i : Flavor}
    (hFq : ∀ a, IntegrableOn (fun p : ℝ × ℝ => p.1 * F a (.quark i) p.1 p.2) unitTriangle)
    (hFqbar : ∀ a, IntegrableOn (fun p : ℝ × ℝ => p.1 * F a (.antiquark i) p.1 p.2) unitTriangle)
    (hfq : IntegrableOn (fun x => f (.quark i) x Q2) (Icc 0 1))
    (hfqbar : IntegrableOn (fun x => f (.antiquark i) x Q2) (Icc 0 1))
    (hmom : ∑ a, mellinMoment f 1 a Q2 = 1) :
    valenceNumber f i Q2 = N i := by
  rw [← mul_sum_mellinMoment_one_eq_valenceNumber hN hM hsymm i hFq hFqbar hfq hfqbar, hmom,
    mul_one]

/-! ### A model: three quarks of one flavour

Both families are satisfied by a simple hadron with a nontrivial double parton distribution:
three quarks of a single flavour, with no antiquarks and no gluons, whose momentum fractions
`(x₁, x₂, x₃)` are uniformly distributed on the simplex `x₁ + x₂ + x₃ = 1`. The pair `(x₁, x₂)` of
two of the quarks then has the density `2` on the unit triangle, so the density of ordered pairs of
distinct quarks is `3 · 2 · 2 = 12` there, and a single quark has the density `2 (1 - x)` on
`[0, 1]`, so the quark density is `3 · 2 (1 - x) = 6 (1 - x)`. -/

/-- The single-parton densities of the three-quark model: `f_q(x) = 6 (1 - x)` on `[0, 1]` for the
quark, and zero for the antiquark and the gluon, at every scale. -/
def threeQuarkPdf : Pdf (Species Unit)
  | .quark _, x, _ => (Icc (0 : ℝ) 1).indicator (fun x => 6 * (1 - x)) x
  | _, _, _ => 0

/-- The double parton distribution of the three-quark model: `F_{qq} = 12` on the unit triangle,
and zero for every other pair of species. -/
def threeQuarkDpd : Species Unit → Species Unit → ℝ → ℝ → ℝ
  | .quark _, .quark _, x₁, x₂ => unitTriangle.indicator (fun _ => 12) (x₁, x₂)
  | _, _, _, _ => 0

@[simp]
theorem threeQuarkPdf_quark (i : Unit) (x Q2 : ℝ) :
    threeQuarkPdf (.quark i) x Q2 = (Icc (0 : ℝ) 1).indicator (fun x => 6 * (1 - x)) x :=
  (rfl)

@[simp]
theorem threeQuarkPdf_antiquark (i : Unit) (x Q2 : ℝ) : threeQuarkPdf (.antiquark i) x Q2 = 0 :=
  (rfl)

@[simp]
theorem threeQuarkPdf_gluon (x Q2 : ℝ) : threeQuarkPdf .gluon x Q2 = 0 :=
  (rfl)

@[simp]
theorem threeQuarkDpd_quark_quark (i j : Unit) (x₁ x₂ : ℝ) :
    threeQuarkDpd (.quark i) (.quark j) x₁ x₂ = unitTriangle.indicator (fun _ => 12) (x₁, x₂) :=
  (rfl)

@[simp]
theorem threeQuarkDpd_quark_antiquark (i j : Unit) (x₁ x₂ : ℝ) :
    threeQuarkDpd (.quark i) (.antiquark j) x₁ x₂ = 0 :=
  (rfl)

@[simp]
theorem threeQuarkDpd_quark_gluon (i : Unit) (x₁ x₂ : ℝ) :
    threeQuarkDpd (.quark i) .gluon x₁ x₂ = 0 :=
  (rfl)

@[simp]
theorem threeQuarkDpd_antiquark (i : Unit) (b : Species Unit) (x₁ x₂ : ℝ) :
    threeQuarkDpd (.antiquark i) b x₁ x₂ = 0 :=
  (rfl)

@[simp]
theorem threeQuarkDpd_gluon (b : Species Unit) (x₁ x₂ : ℝ) : threeQuarkDpd .gluon b x₁ x₂ = 0 :=
  (rfl)

/-- The double parton distribution of the three-quark model is symmetric under exchange of the two
partons. -/
theorem threeQuarkDpd_swap (a b : Species Unit) (x₁ x₂ : ℝ) :
    threeQuarkDpd b a x₂ x₁ = threeQuarkDpd a b x₁ x₂ := by
  have h : (x₂, x₁) ∈ unitTriangle ↔ (x₁, x₂) ∈ unitTriangle :=
    swap_mem_unitTriangle (p := (x₁, x₂))
  cases a <;> cases b <;> simp only [threeQuarkDpd_quark_quark, threeQuarkDpd_quark_antiquark,
    threeQuarkDpd_quark_gluon, threeQuarkDpd_antiquark, threeQuarkDpd_gluon]
  by_cases hx : (x₁, x₂) ∈ unitTriangle
  · rw [indicator_of_mem hx, indicator_of_mem (h.2 hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (mt h.1 hx)]

/-- Along a horizontal line through the unit triangle at height `y ∈ (0, 1]`, the three-quark
double parton distribution of two quarks is `12` between `0` and `1 - y`. -/
private theorem threeQuarkDpd_quark_quark_of_mem {x y : ℝ} (hy0 : 0 < y) (hy1 : y ≤ 1)
    (hx : x ∈ uIoc 0 (1 - y)) : threeQuarkDpd (.quark ()) (.quark ()) x y = 12 := by
  rw [uIoc_of_le (by linarith)] at hx
  rw [threeQuarkDpd_quark_quark,
    indicator_of_mem (mem_unitTriangle.2 ⟨hx.1.le, hy0.le, by linarith [hx.2]⟩)]

/-- The three-quark model satisfies the number sum rules, with three valence quarks. -/
theorem numberSumRule_threeQuarkDpd (Q2 : ℝ) :
    NumberSumRule threeQuarkDpd threeQuarkPdf Q2 fun _ => 3 := by
  intro i a y hy0 hy1
  have hy : y ∈ Icc (0 : ℝ) 1 := ⟨hy0.le, hy1.le⟩
  cases i
  cases a with
  | quark j =>
    cases j
    have h : ∫ x in 0..1 - y, (threeQuarkDpd (.quark ()) (.quark ()) x y -
        threeQuarkDpd (.antiquark ()) (.quark ()) x y) = ∫ _ in 0..1 - y, (12 : ℝ) :=
      intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => by
        rw [threeQuarkDpd_quark_quark_of_mem hy0 hy1.le hx]
        simp)
    rw [h]
    simp [indicator_of_mem hy]
    ring
  | antiquark => simp
  | gluon => simp

/-- The three-quark model satisfies the momentum sum rules. -/
theorem momentumSumRule_threeQuarkDpd (Q2 : ℝ) :
    MomentumSumRule threeQuarkDpd threeQuarkPdf Q2 := by
  intro a y hy0 hy1
  have hy : y ∈ Icc (0 : ℝ) 1 := ⟨hy0.le, hy1.le⟩
  cases a with
  | quark j =>
    cases j
    have h : ∫ x in 0..1 - y, x * threeQuarkDpd (.quark ()) (.quark ()) x y =
        ∫ x in 0..1 - y, x * 12 :=
      intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx => by
        rw [threeQuarkDpd_quark_quark_of_mem hy0 hy1.le hx])
    simp only [Species.sum_univ, Finset.univ_unique, Finset.sum_singleton, PUnit.default_eq_unit,
      h]
    simp [indicator_of_mem hy, intervalIntegral.integral_mul_const]
    ring
  | antiquark => simp [Species.sum_univ]
  | gluon => simp [Species.sum_univ]

/-- The momentum-weighted double parton distributions of the three-quark model are integrable on
the unit triangle. -/
theorem integrableOn_mul_threeQuarkDpd (a b : Species Unit) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * threeQuarkDpd a b p.1 p.2) unitTriangle := by
  cases a <;> cases b <;> simp only [threeQuarkDpd_quark_quark, threeQuarkDpd_quark_antiquark,
    threeQuarkDpd_quark_gluon, threeQuarkDpd_antiquark, threeQuarkDpd_gluon, mul_zero,
    integrableOn_zero]
  have hc : Continuous fun p : ℝ × ℝ => p.1 * 12 := by fun_prop
  refine (hc.continuousOn.integrableOn_compact isCompact_unitTriangle).congr_fun
    (fun p hp => ?_) measurableSet_unitTriangle
  simp [indicator_of_mem hp]

/-- The single-parton densities of the three-quark model are integrable on `[0, 1]`. -/
theorem integrableOn_threeQuarkPdf (a : Species Unit) (Q2 : ℝ) :
    IntegrableOn (fun x => threeQuarkPdf a x Q2) (Icc 0 1) := by
  cases a <;> simp only [threeQuarkPdf_quark, threeQuarkPdf_antiquark, threeQuarkPdf_gluon,
    integrableOn_zero]
  have hc : Continuous fun x : ℝ => 6 * (1 - x) := by fun_prop
  refine (hc.continuousOn.integrableOn_compact isCompact_Icc).congr_fun (fun x hx => ?_)
    measurableSet_Icc
  simp [indicator_of_mem hx]

/-- The quark of the three-quark model has the valence number `3`. -/
theorem valenceNumber_threeQuarkPdf (Q2 : ℝ) : valenceNumber threeQuarkPdf () Q2 = 3 := by
  have h : ∫ x in Icc (0 : ℝ) 1, x ^ 0 * threeQuarkPdf (.quark ()) x Q2 =
      ∫ x in (0 : ℝ)..1, 6 * (1 - x) := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    exact setIntegral_congr_fun measurableSet_Icc fun x hx => by
      simp [indicator_of_mem hx]
  rw [valenceNumber_def, mellinMoment, h]
  simp [mellinMoment, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id]
  norm_num

/-- **The three-quark model carries the full momentum of the hadron**, as
`sum_mellinMoment_one_eq_one` predicts from its two families of double-parton sum rules and the
valence number `3` of its quark. -/
theorem sum_mellinMoment_one_threeQuarkPdf (Q2 : ℝ) :
    ∑ a, mellinMoment threeQuarkPdf 1 a Q2 = 1 :=
  sum_mellinMoment_one_eq_one (numberSumRule_threeQuarkDpd Q2) (momentumSumRule_threeQuarkDpd Q2)
    threeQuarkDpd_swap (i := ()) (fun a => integrableOn_mul_threeQuarkDpd a _)
    (fun a => integrableOn_mul_threeQuarkDpd a _) (integrableOn_threeQuarkPdf _ Q2)
    (integrableOn_threeQuarkPdf _ Q2) (valenceNumber_threeQuarkPdf Q2) three_ne_zero

end EpsilonEridani.Particles.Parton.DoubleParton
