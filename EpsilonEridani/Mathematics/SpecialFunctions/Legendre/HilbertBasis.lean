/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.Legendre.Basic
public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness

/-!
# The Legendre polynomials as a Hilbert basis of `L²[-1, 1]`

The normalized Legendre polynomials `√((2n + 1) / 2) Pₙ` form a Hilbert basis of the
square-integrable functions on `[-1, 1]` with respect to Lebesgue measure. Orthonormality is the
orthogonality relation `setIntegral_Icc_legendre_mul_legendre` of `Legendre/Basic.lean`;
completeness says that the family spans, so that an expansion in Legendre polynomials is a
decomposition of the whole space and not a truncation of it. This is what makes the angular part
of a partial-wave expansion complete: a square-integrable function of `cos θ` is the `L²` sum of its
Legendre series, and it is determined by its Legendre coefficients.

The construction is an instance of Tau Ceti's family-agnostic weighted-`L²` machinery at the
constant weight `1` on `volume.restrict (Set.Icc (-1) 1)`. Orthonormality is fed in through
`TauCeti.hilbertBasisOfOrthogonalSystem`, and completeness comes from moment determinacy for a
compactly supported finite measure, `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`,
applied to the exact-degree family `Pₙ` (`degree_legendre`).

## Main definitions

* `EpsilonEridani.Polynomial.legendreHilbertBasis 𝕜`: the Hilbert basis of
  `L²([-1, 1]; 𝕜)` whose `n`-th vector is `√((2n + 1) / 2) Pₙ`.

## Main statements

* `coeFn_legendreHilbertBasis`: the `n`-th basis vector is the function `√((2n + 1) / 2) Pₙ (x)`;
* `legendreHilbertBasis_repr_apply`: the `n`-th coordinate of `f` is its Legendre coefficient
  `√((2n + 1) / 2) ∫₋₁¹ Pₙ (x) f (x) dx`;
* `integrableOn_Icc_legendre_smul`: the integrals `∫₋₁¹ Pₙ (x) f (x) dx` against an
  integrable `f` are integrals of integrable functions;
* `ae_eq_zero_of_forall_setIntegral_Icc_legendre_smul_eq_zero`: completeness in its elementary form,
  a square-integrable function on `[-1, 1]` orthogonal to every `Pₙ` vanishes almost everywhere;
* `ae_eq_of_forall_setIntegral_Icc_legendre_smul_eq`: a square-integrable function on `[-1, 1]` is
  determined almost everywhere by its Legendre coefficients.

## References

* [G. Szegő, *Orthogonal Polynomials*, §3.1 and §4.7]
* [NIST Digital Library of Mathematical Functions, §18.2(i) and §18.3](https://dlmf.nist.gov/18)
* `TauCeti.chebyshevTEnvelopeHilbertBasis`
  (`TauCeti/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Envelope.lean`), the Tau Ceti
  instance of the same machinery that this construction follows.
-/

public section

namespace EpsilonEridani

namespace Polynomial

open _root_.Polynomial MeasureTheory Set

/-- Lebesgue measure on `[-1, 1]` (with the constant weight `1`) has a finite exponential moment:
the analytic input of moment determinacy. -/
private theorem exists_integrable_exp_mul_abs_Icc :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      ((volume.restrict (Icc (-1 : ℝ) 1)).withDensity fun _ => ENNReal.ofReal 1) := by
  refine ⟨1, one_pos, ?_⟩
  rw [ENNReal.ofReal_one, ← Pi.one_def, withDensity_one]
  exact (by fun_prop : Continuous fun x : ℝ => Real.exp (1 * |x|)).integrableOn_Icc

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The `L²` membership obligation of the normalized Legendre polynomials. -/
private theorem memLp_legendre_div_sqrt (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) ((legendre n).eval x / Real.sqrt (2 / (2 * n + 1)))) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).withDensity fun _ => ENNReal.ofReal 1) :=
  TauCeti.memLp_two_bareNormalized (𝕜 := 𝕜) exists_integrable_exp_mul_abs_Icc legendre
    (fun n => 2 / (2 * n + 1)) n

/-- **The Legendre polynomials are a Hilbert basis of `L²[-1, 1]`.** The `n`-th vector is the
normalized Legendre polynomial `√((2n + 1) / 2) Pₙ` (`coeFn_legendreHilbertBasis`), as an element
of the square-integrable `𝕜`-valued functions for Lebesgue measure on `[-1, 1]`. -/
noncomputable def legendreHilbertBasis :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 (volume.restrict (Icc (-1 : ℝ) 1))) :=
  TauCeti.hilbertBasisOfOrthogonalSystem (fun n x => (legendre n).eval x) (fun _ => 1)
    (fun n => 2 / (2 * n + 1)) (ae_of_all _ fun _ => one_pos) aemeasurable_const
    (fun n => by positivity)
    (fun m n => by simpa using setIntegral_Icc_legendre_mul_legendre m n)
    (memLp_legendre_div_sqrt 𝕜)
    (TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot legendre (fun _ => 1)
      (fun n => 2 / (2 * n + 1)) degree_legendre (fun n => by positivity)
      exists_integrable_exp_mul_abs_Icc (memLp_legendre_div_sqrt 𝕜))

/-- **The basis vectors are the normalized Legendre polynomials**: the `n`-th vector of
`legendreHilbertBasis` is represented by `x ↦ √((2n + 1) / 2) Pₙ (x)`. -/
theorem coeFn_legendreHilbertBasis (n : ℕ) :
    ⇑(legendreHilbertBasis 𝕜 n) =ᵐ[volume.restrict (Icc (-1 : ℝ) 1)]
      fun x => (algebraMap ℝ 𝕜) (Real.sqrt ((2 * n + 1) / 2) * (legendre n).eval x) := by
  refine (TauCeti.coeFn_hilbertBasisOfOrthogonalSystem _ _ _ _ _ _ _ _ _ n).trans
    (ae_of_all _ fun x => ?_)
  simp only [Real.sqrt_one, mul_one]
  rw [div_eq_mul_inv ((legendre n).eval x), ← Real.sqrt_inv, inv_div,
    mul_comm ((legendre n).eval x)]

variable {𝕜}

/-- The integrand `Pₙ (x) f (x)` of a Legendre coefficient of an integrable function on
`[-1, 1]` is integrable on `[-1, 1]`, so the integrals in the statements below are genuine. -/
theorem integrableOn_Icc_legendre_smul (n : ℕ) {f : ℝ → 𝕜}
    (hf : IntegrableOn f (Icc (-1 : ℝ) 1)) :
    IntegrableOn (fun x => (legendre n).eval x • f x) (Icc (-1 : ℝ) 1) :=
  hf.continuousOn_smul (legendre n).continuous.continuousOn isCompact_Icc

/-- **The coordinates are the Legendre coefficients**: the `n`-th coordinate of `f ∈ L²[-1, 1]` in
`legendreHilbertBasis` is `√((2n + 1) / 2) ∫₋₁¹ Pₙ (x) f (x) dx`. -/
theorem legendreHilbertBasis_repr_apply (f : Lp 𝕜 2 (volume.restrict (Icc (-1 : ℝ) 1))) (n : ℕ) :
    (legendreHilbertBasis 𝕜).repr f n =
      Real.sqrt ((2 * n + 1) / 2) • ∫ x in Icc (-1 : ℝ) 1, (legendre n).eval x • f x := by
  rw [HilbertBasis.repr_apply_apply, L2.inner_def, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_legendreHilbertBasis 𝕜 n] with x hx
  rw [hx, RCLike.inner_apply', RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, smul_smul,
    RCLike.real_smul_eq_coe_mul]

/-- **Completeness of the Legendre polynomials.** A square-integrable function on `[-1, 1]` whose
integral against every Legendre polynomial vanishes is zero almost everywhere. -/
theorem ae_eq_zero_of_forall_setIntegral_Icc_legendre_smul_eq_zero {f : ℝ → 𝕜}
    (hf : MemLp f 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (h : ∀ n, ∫ x in Icc (-1 : ℝ) 1, (legendre n).eval x • f x = 0) :
    f =ᵐ[volume.restrict (Icc (-1 : ℝ) 1)] 0 := by
  have hrepr : (legendreHilbertBasis 𝕜).repr hf.toLp = 0 := by
    ext n
    have hcongr : ∫ x in Icc (-1 : ℝ) 1, (legendre n).eval x • MemLp.toLp f hf x =
        ∫ x in Icc (-1 : ℝ) 1, (legendre n).eval x • f x :=
      integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [hx])
    rw [legendreHilbertBasis_repr_apply, lp.coeFn_zero, Pi.zero_apply, hcongr, h n, smul_zero]
  have hzero : hf.toLp = 0 := (legendreHilbertBasis 𝕜).repr.map_eq_zero_iff.mp hrepr
  filter_upwards [hf.coeFn_toLp, Lp.coeFn_zero 𝕜 2 (volume.restrict (Icc (-1 : ℝ) 1))]
    with x hx h0
  rw [← hx, hzero, h0]

/-- **A function is determined by its Legendre coefficients.** Two square-integrable functions on
`[-1, 1]` with the same integral against every Legendre polynomial agree almost everywhere. -/
theorem ae_eq_of_forall_setIntegral_Icc_legendre_smul_eq {f g : ℝ → 𝕜}
    (hf : MemLp f 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Icc (-1 : ℝ) 1)))
    (h : ∀ n, ∫ x in Icc (-1 : ℝ) 1, (legendre n).eval x • f x =
      ∫ x in Icc (-1 : ℝ) 1, (legendre n).eval x • g x) :
    f =ᵐ[volume.restrict (Icc (-1 : ℝ) 1)] g := by
  refine (ae_eq_zero_of_forall_setIntegral_Icc_legendre_smul_eq_zero (hf.sub hg) fun n => ?_).mono
    fun x hx => sub_eq_zero.mp hx
  simp only [Pi.sub_apply, smul_sub]
  rw [integral_sub (integrableOn_Icc_legendre_smul n (hf.integrable one_le_two))
    (integrableOn_Icc_legendre_smul n (hg.integrable one_le_two)), h n, sub_self]

end Polynomial

end EpsilonEridani
