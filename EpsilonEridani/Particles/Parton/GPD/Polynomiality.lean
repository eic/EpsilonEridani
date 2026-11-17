/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import EpsilonEridani.Particles.Parton.GPD.Moments
public import EpsilonEridani.Particles.Parton.GPD.DoubleDistribution
public import EpsilonEridani.Mathematics.MeasureTheory.Shear
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
/-!

# Polynomiality of GPD Moments from the Double-Distribution Representation

This module derives polynomiality — that the `x`-moments of a GPD are *even* polynomials
in the skewness `ξ`, with the top coefficient the D-term — for a GPD built from a double
distribution, instead of assuming it.

## Statement

With the moment convention of `EpsilonEridani.Particles.Parton.GPD.Moments` (integrand `x ^ n`,
integration over the full support `[-1, 1]`, literature index `n + 1`):

```text
∫_{-1}^{1} dx x^n H(x, ξ, t)
  = Σ_{k = 0}^{n} C(n, k) ξ^k ∫∫ dβ dα β^(n-k) α^k F(β, α, t)   +   ξ^(n+1) ∫ du u^n D(u, t)
```

for `|ξ| ≤ 1`. The derivation is: substitute the one-dimensional form of the
double-distribution representation, change variables from `(x, β)` to `(β, α)` with
`x = β + αξ` (Jacobian `|ξ|`, cancelling the `1/|ξ|` prefactor), exchange the order of
integration, expand `(β + αξ)^n` by the binomial theorem, and read off the coefficient of
`ξ^k`. The D-term piece is a one-dimensional rescaling, `x = ξ u`.

Two structural facts then give the physics content:

* `DoubleDistribution.alphaSymm` kills every odd-`k` term, so the polynomial is even
  (`momentCoeff_eq_zero_of_odd`);
* `DTerm.odd` kills `∫ du u^n D` for even `n`, so the `ξ^(n+1)` slot is occupied only when
  `n + 1` — the literature index — is even. That slot is the D-term
  (`momentPolynomial_coeff_top`).

## References

* D. Müller, D. Robaschik, B. Geyer *et al.*, Fortschr. Phys. **42** (1994) 101.
* A. V. Radyushkin, *Nonforward parton distributions*, Phys. Rev. D **56** (1997) 5524.
* X. Ji, *Off-forward parton distributions*, J. Phys. G **24** (1998) 1181.
* M. Diehl, *Generalized parton distributions*, Phys. Rept. **388** (2003) 41, §4.3.
* A. V. Belitsky and A. V. Radyushkin, Phys. Rept. **418** (2005) 1, §3.

## Main results

* `mellinMomentGpd_ofDoubleDistribution`: the moment formula above, for `|ξ| ≤ 1`.
* `mellinMomentGpd_polynomial`, `mellinMomentH_polynomial`: the moment is an even polynomial in
  `ξ` of degree at most `n + 1`.
* `polynomialityAssumptionsOfDoubleDistribution`: every GPD model built from double
  distributions satisfies `GPD.PolynomialityAssumptions`.

For `ξ ≠ 0` the change of variables is the scaled shear `(β, α) ↦ (β, β + ξ α)` of
`EpsilonEridani.Mathematics.MeasureTheory.Shear`, whose Jacobian `|ξ|` cancels the prefactor
`1/|ξ|` of the double-distribution term. At `ξ = 0` the induced GPD is the `α`-integral of the
double distribution and the formula is Fubini's theorem; only the `k = 0` term survives.

-/

@[expose] public section

noncomputable section

open scoped BigOperators

open MeasureTheory

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GPD

variable {Flavor : Type}

/-- The `(β, α)` monomial moment `∫∫ dβ dα β^m α^k F(β, α, t)` of a double distribution.

These are the form factors `A_{n,k}(t)` of the polynomiality expansion, up to the binomial
factor supplied by `momentCoeff`. -/
def ddMoment (dd : DoubleDistribution Flavor) (i : Flavor) (m k : ℕ) (t : ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t

/-- The `m`-th monomial moment `∫ du u^m D(u, t)` of a D-term. -/
def dtMoment (dt : DTerm Flavor) (i : Flavor) (m : ℕ) (t : ℝ) : ℝ :=
  ∫ u : ℝ, u ^ m * dt.D i u t

/-- Odd `α`-moments of a double distribution vanish.

This is the formal content of the `α`-symmetry of `F`, and it is what makes the moment
polynomial *even* in `ξ`. -/
lemma ddMoment_eq_zero_of_odd (dd : DoubleDistribution Flavor) (i : Flavor) (m k : ℕ)
    (t : ℝ) (hk : Odd k) :
    ddMoment dd i m k t = 0 := by
  -- the reflection `(β, α) ↦ (β, -α)` preserves `volume` on `ℝ × ℝ`
  have hmp : MeasureTheory.MeasurePreserving
      (⇑((MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)))
      (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) MeasureTheory.volume := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    exact (MeasureTheory.MeasurePreserving.id _).prod
      (MeasureTheory.Measure.measurePreserving_neg _)
  -- composing the integrand with it multiplies it by `(-1)^k = -1`
  have hflip : ∀ p : ℝ × ℝ,
      p.1 ^ m * (-p.2) ^ k * dd.F i p.1 (-p.2) t
        = -(p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t) := by
    intro p
    rw [hk.neg_pow, dd.alphaSymm]
    ring
  have key : ddMoment dd i m k t = -ddMoment dd i m k t := by
    calc ddMoment dd i m k t
        = ∫ p : ℝ × ℝ, p.1 ^ m * (-p.2) ^ k * dd.F i p.1 (-p.2) t :=
          (hmp.integral_comp' (fun p : ℝ × ℝ => p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t)).symm
      _ = ∫ p : ℝ × ℝ, -(p.1 ^ m * p.2 ^ k * dd.F i p.1 p.2 t) := by simp_rw [hflip]
      _ = -ddMoment dd i m k t := by rw [MeasureTheory.integral_neg]; rfl
  linarith

/-- Even monomial moments of a D-term vanish, by its oddness in `u`.

This is what confines the D-term to the moments of even literature index. -/
lemma dtMoment_eq_zero_of_even (dt : DTerm Flavor) (i : Flavor) (m : ℕ) (t : ℝ)
    (hm : Even m) :
    dtMoment dt i m t = 0 := by
  -- there is no dedicated odd-function-integral lemma at this pin, so this goes through
  -- negation being measure preserving, exactly as in `ddMoment_eq_zero_of_odd`
  have hmp : MeasureTheory.MeasurePreserving (⇑(MeasurableEquiv.neg ℝ))
      (MeasureTheory.volume : MeasureTheory.Measure ℝ) MeasureTheory.volume :=
    MeasureTheory.Measure.measurePreserving_neg _
  have hflip : ∀ u : ℝ, (-u) ^ m * dt.D i (-u) t = -(u ^ m * dt.D i u t) := by
    intro u
    rw [hm.neg_pow, dt.odd]
    ring
  have key : dtMoment dt i m t = -dtMoment dt i m t := by
    calc dtMoment dt i m t
        = ∫ u : ℝ, (-u) ^ m * dt.D i (-u) t :=
          (hmp.integral_comp' (fun u : ℝ => u ^ m * dt.D i u t)).symm
      _ = ∫ u : ℝ, -(u ^ m * dt.D i u t) := by simp_rw [hflip]
      _ = -dtMoment dt i m t := by rw [MeasureTheory.integral_neg]; rfl
  linarith

/-- The coefficient of `ξ^k` in the `n`-th moment of a GPD built from `dd` and `dt`.

For `k ≤ n` it is the binomial-weighted `(β, α)` moment of the double distribution; the
single extra slot `k = n + 1` carries the D-term. -/
def momentCoeff (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (k : ℕ) (t : ℝ) : ℝ :=
  if k ≤ n then (n.choose k : ℝ) * ddMoment dd i (n - k) k t
  else if k = n + 1 then dtMoment dt i n t
  else 0

/-- Odd coefficients of the moment polynomial vanish: moments are even in `ξ`. -/
lemma momentCoeff_eq_zero_of_odd (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (k : ℕ) (t : ℝ) (hk : Odd k) :
    momentCoeff dd dt n i k t = 0 := by
  rw [momentCoeff]
  split_ifs with h1 h2
  · rw [ddMoment_eq_zero_of_odd dd i (n - k) k t hk, mul_zero]
  · have hodd : Odd (n + 1) := h2 ▸ hk
    have hn : Even n := by
      rcases Nat.even_or_odd n with h | h
      · exact h
      · exfalso
        obtain ⟨j, hj⟩ := h
        obtain ⟨l, hl⟩ := hodd
        omega
    exact dtMoment_eq_zero_of_even dt i n t hn
  · rfl

/-- The moment polynomial of a GPD built from a double distribution and a D-term. -/
def momentPolynomial (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (n + 2), Polynomial.C (momentCoeff dd dt n i k t) * Polynomial.X ^ k

/-- The coefficients of `momentPolynomial` are exactly `momentCoeff`. -/
lemma momentPolynomial_coeff (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) (k : ℕ) :
    (momentPolynomial dd dt n i t).coeff k = momentCoeff dd dt n i k t := by
  rw [momentPolynomial, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq (Finset.range (n + 2)) k (fun j => momentCoeff dd dt n i j t)]
  by_cases hk : k < n + 2
  · rw [ite_eq_left (Finset.mem_range.mpr hk)]
  · rw [ite_eq_right (fun hmem => hk (Finset.mem_range.mp hmem))]
    rw [momentCoeff, ite_eq_right (by omega : ¬ k ≤ n), ite_eq_right (by omega : k ≠ n + 1)]

/-- The moment polynomial has degree at most `n + 1`.

The bound is `n + 1` rather than `n` because the repository's moment index is the
literature index minus one; see the `GPD.Moments` module docstring. -/
lemma momentPolynomial_natDegree_le (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) :
    (momentPolynomial dd dt n i t).natDegree ≤ n + 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro m hm
  rw [momentPolynomial_coeff, momentCoeff, ite_eq_right (by omega : ¬ m ≤ n),
    ite_eq_right (by omega : m ≠ n + 1)]

/-- Evaluating the moment polynomial is summing the coefficients against powers of `ξ`. -/
lemma momentPolynomial_eval (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) (xi : ℝ) :
    (momentPolynomial dd dt n i t).eval xi
      = ∑ k ∈ Finset.range (n + 2), momentCoeff dd dt n i k t * xi ^ k := by
  simp [momentPolynomial, Polynomial.eval_finsetSum]

/-- The binomial expansion of `(β + ξ α)^n F(β, α, t)` into the monomials whose integrals are
the form factors `ddMoment`. -/
private lemma add_mul_pow_mul_eq_sum (dd : DoubleDistribution Flavor) (i : Flavor) (n : ℕ)
    (xi t : ℝ) (p : ℝ × ℝ) :
    (p.1 + xi * p.2) ^ n * dd.F i p.1 p.2 t = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * xi ^ k * (p.1 ^ (n - k) * p.2 ^ k * dd.F i p.1 p.2 t) := by
  rw [add_comm, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The moment of a double distribution along the lines `x = β + ξ α`,
`(β, α) ↦ (β + ξ α)^n F(β, α, t)`, is integrable on the `(β, α)` plane. -/
lemma integrable_add_mul_pow_mul (dd : DoubleDistribution Flavor) (i : Flavor) (n : ℕ)
    (xi t : ℝ) :
    Integrable fun p : ℝ × ℝ => (p.1 + xi * p.2) ^ n * dd.F i p.1 p.2 t := by
  simp_rw [add_mul_pow_mul_eq_sum]
  exact integrable_finsetSum _ fun k _ => (dd.momentIntegrable i (n - k) k t).const_mul _

/-- The moment of a double distribution along the lines `x = β + ξ α` is the binomial sum
of its form factors: `∫∫ (β + ξ α)^n F = ∑_{k ≤ n} C(n, k) ξ^k ∫∫ β^(n-k) α^k F`. -/
lemma integral_add_mul_pow_mul (dd : DoubleDistribution Flavor) (i : Flavor) (n : ℕ)
    (xi t : ℝ) :
    ∫ p : ℝ × ℝ, (p.1 + xi * p.2) ^ n * dd.F i p.1 p.2 t = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * ddMoment dd i (n - k) k t * xi ^ k := by
  simp_rw [add_mul_pow_mul_eq_sum]
  rw [integral_finsetSum _ fun k _ => (dd.momentIntegrable i (n - k) k t).const_mul _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, ddMoment]
  ring

/-- The double-distribution integrand of the moment, written on the `(β, x)` plane, is
integrable for `ξ ≠ 0`: it is the composite of the integrable moment along the lines
`x = β + ξ α` with the inverse of the scaled shear. -/
private lemma integrable_pow_mul_F_div (dd : DoubleDistribution Flavor) (i : Flavor) (n : ℕ)
    {xi : ℝ} (hxi : xi ≠ 0) (t : ℝ) :
    Integrable fun q : ℝ × ℝ => q.2 ^ n * dd.F i q.1 ((q.2 - q.1) / xi) t := by
  rw [← integrable_comp_prod_add_mul_iff _ hxi]
  convert integrable_add_mul_pow_mul dd i n xi t using 3 with p
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hxi]

/-- For `ξ ≠ 0` the double-distribution term of the GPD, weighted by `x^n`, is integrable
in `x`. -/
private lemma integrable_pow_mul_ddTerm (dd : DoubleDistribution Flavor) (i : Flavor) (n : ℕ)
    {xi : ℝ} (hxi : xi ≠ 0) (t : ℝ) :
    Integrable fun x : ℝ => x ^ n * ((|xi|)⁻¹ * ∫ β : ℝ, dd.F i β ((x - β) / xi) t) := by
  refine (((integrable_pow_mul_F_div dd i n hxi t).integral_prod_right).const_mul
    (|xi|)⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [integral_const_mul]
  ring

/-- For `ξ ≠ 0` the `n`-th moment of the double-distribution term of the GPD is the moment of
the double distribution along the lines `x = β + ξ α`: the Jacobian `|ξ|` of the scaled shear
cancels the prefactor `1/|ξ|`. -/
private lemma integral_pow_mul_ddTerm (dd : DoubleDistribution Flavor) (i : Flavor) (n : ℕ)
    {xi : ℝ} (hxi : xi ≠ 0) (t : ℝ) :
    ∫ x : ℝ, x ^ n * ((|xi|)⁻¹ * ∫ β : ℝ, dd.F i β ((x - β) / xi) t)
      = ∫ p : ℝ × ℝ, (p.1 + xi * p.2) ^ n * dd.F i p.1 p.2 t := by
  have hcomp := integral_comp_prod_add_mul
    (fun q : ℝ × ℝ => q.2 ^ n * dd.F i q.1 ((q.2 - q.1) / xi) t) xi
  simp only [add_sub_cancel_left, mul_div_cancel_left₀ _ hxi, smul_eq_mul] at hcomp
  rw [hcomp, Measure.volume_eq_prod,
    integral_prod_symm _ (integrable_pow_mul_F_div dd i n hxi t), abs_inv, ← smul_eq_mul,
    ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [integral_const_mul]
  ring

/-- For `ξ ≠ 0` the D-term contribution to the GPD, weighted by `x^n`, is integrable in `x`. -/
private lemma integrable_pow_mul_dTerm (dt : DTerm Flavor) (i : Flavor) (n : ℕ) {xi : ℝ}
    (hxi : xi ≠ 0) (t : ℝ) :
    Integrable fun x : ℝ => x ^ n * (xi / |xi| * dt.D i (x / xi) t) := by
  refine (((dt.momentIntegrable i n t).comp_div hxi).const_mul (xi / |xi| * xi ^ n)).congr
    (Filter.Eventually.of_forall fun x => ?_)
  have hx : x ^ n = xi ^ n * (x / xi) ^ n := by rw [← mul_pow, mul_div_cancel₀ x hxi]
  simp only
  rw [hx]
  ring

/-- For `ξ ≠ 0` the `n`-th moment of the D-term contribution to the GPD is
`ξ^(n+1) ∫ du u^n D(u, t)`: the rescaling `x = ξ u` contributes `|ξ| ξ^n`, and the prefactor
`ξ/|ξ|` turns `|ξ|` into `ξ`. -/
private lemma integral_pow_mul_dTerm (dt : DTerm Flavor) (i : Flavor) (n : ℕ) {xi : ℝ}
    (hxi : xi ≠ 0) (t : ℝ) :
    ∫ x : ℝ, x ^ n * (xi / |xi| * dt.D i (x / xi) t) = xi ^ (n + 1) * dtMoment dt i n t := by
  have h : ∀ x : ℝ, x ^ n * (xi / |xi| * dt.D i (x / xi) t)
      = xi / |xi| * xi ^ n * ((x / xi) ^ n * dt.D i (x / xi) t) := by
    intro x
    have hx : x ^ n = xi ^ n * (x / xi) ^ n := by rw [← mul_pow, mul_div_cancel₀ x hxi]
    rw [hx]
    ring
  simp_rw [h]
  rw [integral_const_mul, Measure.integral_comp_div (fun u => u ^ n * dt.D i u t), smul_eq_mul,
    dtMoment]
  field_simp
  ring

/-- **The moment formula.** The `n`-th moment of a GPD built from a double distribution and
a D-term is, for physical skewness `|ξ| ≤ 1`, the sum of the binomially weighted `(β, α)`
moments of the double distribution and the D-term moment:
`∫_{-1}^{1} dx x^n H(x, ξ, t) = ∑_{k ≤ n} C(n, k) ξ^k ∫∫ β^(n-k) α^k F + ξ^(n+1) ∫ u^n D`. -/
theorem mellinMomentGpd_ofDoubleDistribution
    (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (xi t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentGpd (gpdOfDoubleDistribution dd dt) n i xi t
      = ∑ k ∈ Finset.range (n + 2), momentCoeff dd dt n i k t * xi ^ k := by
  -- the integrand vanishes off `[-1, 1]`, so the moment is an integral over `ℝ`
  rw [mellinMomentGpd, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
    rw [gpdOfDoubleDistribution_eq_zero_of_one_lt_abs dd dt i x xi t hxi, mul_zero]
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · rw [abs_of_neg (by linarith)]
      linarith
    · rw [abs_of_pos (by linarith)]
      exact hx]
  -- split off the D-term slot and recognise the rest as the moment along `x = β + ξ α`
  rw [Finset.sum_range_succ, momentCoeff, ite_eq_right (by omega : ¬ n + 1 ≤ n), ite_eq_left rfl]
  have hlow : ∀ k ∈ Finset.range (n + 1), momentCoeff dd dt n i k t * xi ^ k
      = (n.choose k : ℝ) * ddMoment dd i (n - k) k t * xi ^ k := fun k hk => by
    rw [momentCoeff, ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [Finset.sum_congr rfl hlow, ← integral_add_mul_pow_mul]
  by_cases hxi0 : xi = 0
  · -- forward limit: the GPD is the `α`-integral of `F`, and the formula is Fubini
    subst hxi0
    simp only [gpdOfDoubleDistribution, ite_true, zero_mul, add_zero,
      zero_pow n.succ_ne_zero]
    have hI := integrable_add_mul_pow_mul dd i n 0 t
    simp only [zero_mul, add_zero] at hI
    rw [mul_zero, add_zero, Measure.volume_eq_prod, integral_prod _ hI]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [integral_const_mul]
  · simp only [gpdOfDoubleDistribution, hxi0, ite_false, mul_add]
    rw [integral_add (integrable_pow_mul_ddTerm dd i n hxi0 t)
      (integrable_pow_mul_dTerm dt i n hxi0 t), integral_pow_mul_ddTerm dd i n hxi0 t,
      integral_pow_mul_dTerm dt i n hxi0 t]
    ring

/-- **Polynomiality.** For a GPD built from a double distribution and a D-term, the `n`-th
`x`-moment is, at physical skewness, an even polynomial in `ξ` of degree at most `n + 1`. -/
theorem mellinMomentGpd_polynomial
    (dd : DoubleDistribution Flavor) (dt : DTerm Flavor) (n : ℕ) (i : Flavor) (t : ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n + 1 ∧ (∀ k, Odd k → p.coeff k = 0) ∧
      ∀ xi, |xi| ≤ 1 →
        mellinMomentGpd (gpdOfDoubleDistribution dd dt) n i xi t = p.eval xi := by
  refine ⟨momentPolynomial dd dt n i t, momentPolynomial_natDegree_le dd dt n i t, ?_, ?_⟩
  · intro k hk
    rw [momentPolynomial_coeff]
    exact momentCoeff_eq_zero_of_odd dd dt n i k t hk
  · intro xi hxi
    rw [momentPolynomial_eval]
    exact mellinMomentGpd_ofDoubleDistribution dd dt n i xi t hxi

/-- Polynomiality of the `H` moments of a GPD model built from double distributions. -/
theorem mellinMomentH_polynomial
    (ddH ddE : DoubleDistribution Flavor) (dtH dtE : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ n + 1 ∧ (∀ k, Odd k → p.coeff k = 0) ∧
      ∀ xi, |xi| ≤ 1 →
        mellinMomentH (Model.ofDoubleDistribution ddH dtH ddE dtE) n i xi t = p.eval xi :=
  mellinMomentGpd_polynomial ddH dtH n i t

/-- Below the top slot the coefficients are pure double-distribution form factors. -/
lemma momentPolynomial_coeff_of_le (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) (k : ℕ) (hk : k ≤ n) :
    (momentPolynomial dd dt n i t).coeff k
      = (n.choose k : ℝ) * ddMoment dd i (n - k) k t := by
  rw [momentPolynomial_coeff, momentCoeff, ite_eq_left hk]

/-- **The D-term is the top coefficient.** The `ξ^(n+1)` coefficient of the moment
polynomial is exactly the `n`-th moment of the D-term, with no double-distribution
contribution. In literature indexing this is the `ξ^n` coefficient of the `n`-th moment,
the `C_n(t)` that carries the pressure and shear-force interpretation of the nucleon
(see e.g. arXiv:2501.16257). -/
lemma momentPolynomial_coeff_top (dd : DoubleDistribution Flavor) (dt : DTerm Flavor)
    (n : ℕ) (i : Flavor) (t : ℝ) :
    (momentPolynomial dd dt n i t).coeff (n + 1) = dtMoment dt i n t := by
  rw [momentPolynomial_coeff, momentCoeff, ite_eq_right (by omega : ¬ n + 1 ≤ n), ite_eq_left rfl]

/-- The D-term slot is empty for even `n`, i.e. for odd literature index `n + 1`. -/
lemma momentPolynomial_coeff_top_eq_zero_of_even (dd : DoubleDistribution Flavor)
    (dt : DTerm Flavor) (n : ℕ) (i : Flavor) (t : ℝ) (hn : Even n) :
    (momentPolynomial dd dt n i t).coeff (n + 1) = 0 := by
  rw [momentPolynomial_coeff_top]
  exact dtMoment_eq_zero_of_even dt i n t hn

/-- **The bridge to the assumption bundle.** Every GPD model built from double distributions
satisfies `PolynomialityAssumptions`, with the coefficients `momentCoeff` of its `H` moments. -/
def polynomialityAssumptionsOfDoubleDistribution
    (ddH ddE : DoubleDistribution Flavor) (dtH dtE : DTerm Flavor) :
    PolynomialityAssumptions (Model.ofDoubleDistribution ddH dtH ddE dtE) where
  coeff := fun n i k t => momentCoeff ddH dtH n i k t
  coeff_eq_zero_of_odd := fun n i k t hk => momentCoeff_eq_zero_of_odd ddH dtH n i k t hk
  polynomial := fun n i xi t hxi => mellinMomentGpd_ofDoubleDistribution ddH dtH n i xi t hxi

/-- The zeroth moment of `H` for a GPD model built from double distributions does not depend
on the skewness. -/
lemma mellinMomentH_n0_eq_at_zero_ofDoubleDistribution
    (ddH ddE : DoubleDistribution Flavor) (dtH dtE : DTerm Flavor)
    (i : Flavor) (xi t : ℝ) (hxi : |xi| ≤ 1) :
    mellinMomentH (Model.ofDoubleDistribution ddH dtH ddE dtE) 0 i xi t
      = mellinMomentH (Model.ofDoubleDistribution ddH dtH ddE dtE) 0 i 0 t :=
  mellinMomentH_n0_eq_at_zero _
    (polynomialityAssumptionsOfDoubleDistribution ddH ddE dtH dtE) i xi t hxi

end GPD
end Parton
end Particles
end EpsilonEridani
