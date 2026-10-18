/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.Gegenbauer.Measure
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Probability.Moments.VanishingMoments

/-!
# The Gegenbauer polynomials of index `3/2` as a Hilbert basis

The Gegenbauer polynomials `C_n^{(3/2)}` are orthogonal for the measure `(1 - x²) dx` on
`(-1, 1]`, with squared norms `2 (n + 1) (n + 2) / (2n + 3)`
(`EpsilonEridani.Mathematics.SpecialFunctions.Gegenbauer.Measure`). This file divides them by
those norms and proves that the resulting modes are a *Hilbert basis* of
`L²(gegenbauerThreeHalvesMeasure)`: an orthonormal family whose closed span is everything.

Completeness is the substance. A vector of `L²` orthogonal to every mode is orthogonal to every
polynomial evaluation, because the family is a basis of `ℝ[X]`
(`EpsilonEridani.gegenbauerThreeHalvesBasis`); hence all of its monomial moments vanish; hence it
is almost everywhere zero, by moment determinacy
(`TauCeti.ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp`), whose single hypothesis
— integrability of `exp (a |x|)` at one positive rate — holds here because the weight measure is
finite and supported on `[-1, 1]`, so that `exp (a |x|)` is a continuous function integrated over
a compact set.

The orthonormality and the final assembly are done here rather than through the family-agnostic
`TauCeti.hilbertBasisOfWeightedMeasure`, whose conclusion is a basis of `L²` of a measure written
as an explicit `withDensity`: the body of `gegenbauerThreeHalvesMeasure` is not exposed, so that
space is not definitionally this one, and transporting across the two would cost more than the
four lemmas it saves. TauCeti's own Chebyshev family is assembled directly for the same reason.

The resulting unitary `L²(gegenbauerThreeHalvesMeasure) ≃ₗᵢ ℓ²(ℕ)` is what makes the Gegenbauer
coefficients of a function a complete invariant: two functions with the same coefficients agree
almost everywhere, and a square-summable sequence of coefficients comes from a function. That is
the setting in which the expansion of a leading-twist light-cone distribution amplitude
`6 u (1 - u) ∑ₙ aₙ C_n^{(3/2)}(2u - 1)` converges, and in which the evolution of the amplitude
decouples into the independent evolution of its coefficients.

## Main definitions

* `EpsilonEridani.polynomialEvalGegenbauerThreeHalvesLp`: polynomial evaluation as a linear map
  into `L²(gegenbauerThreeHalvesMeasure)`.
* `EpsilonEridani.gegenbauerThreeHalvesNormSq`: the squared `L²` norm
  `2 (n + 1) (n + 2) / (2n + 3)` of `C_n^{(3/2)}`.
* `EpsilonEridani.normalizedGegenbauerThreeHalves`,
  `EpsilonEridani.normalizedGegenbauerThreeHalvesLp`: the normalized mode
  `C_n^{(3/2)} / ‖C_n^{(3/2)}‖`, as a function and as a vector of `L²`.
* `EpsilonEridani.gegenbauerThreeHalvesHilbertBasis`: the Hilbert basis of
  `L²(gegenbauerThreeHalvesMeasure)` it forms.

## Main statements

* `EpsilonEridani.orthonormal_normalizedGegenbauerThreeHalvesLp`: the modes are orthonormal.
* `EpsilonEridani.orthogonal_span_normalizedGegenbauerThreeHalvesLp_eq_bot`: completeness.
* `EpsilonEridani.gegenbauerThreeHalvesHilbertBasis_repr_apply`: the `n`-th coordinate of the
  resulting isometry onto `ℓ²(ℕ)` is the inner product with the `n`-th mode.

## References

* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, 4th edition (1975),
  chapter IV, §4.7 and §3.1.
* The Chebyshev Hilbert basis of the TauCeti library
  (`TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.HilbertBasis`, with its `Moments`
  and `Span` files), whose development this one follows step for step.
-/

public section

namespace EpsilonEridani

open MeasureTheory Polynomial

/-! ### Polynomial moments of the weight measure -/

/-- Every monomial has a finite moment against the Gegenbauer weight measure. -/
theorem integrable_pow_gegenbauerThreeHalvesMeasure (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) gegenbauerThreeHalvesMeasure :=
  (continuous_pow k).continuousOn.integrable_gegenbauerThreeHalvesMeasure

/-- A real polynomial evaluation is square integrable for the Gegenbauer weight measure. -/
theorem memLp_two_eval_gegenbauerThreeHalvesMeasure (q : ℝ[X]) :
    MemLp (fun x : ℝ => q.eval x) 2 gegenbauerThreeHalvesMeasure :=
  TauCeti.memLp_two_eval_of_forall_integrable_pow integrable_pow_gegenbauerThreeHalvesMeasure q

/-- Evaluation of a real polynomial, cast into any `RCLike` scalar field, as a linear map into
`L²(gegenbauerThreeHalvesMeasure)`. It is well defined because every polynomial has a finite
second moment for the weight measure. -/
noncomputable def polynomialEvalGegenbauerThreeHalvesLp (𝕜 : Type*) [RCLike 𝕜] :
    ℝ[X] →ₗ[ℝ] Lp 𝕜 2 gegenbauerThreeHalvesMeasure :=
  TauCeti.polynomialEvalLp 𝕜 integrable_pow_gegenbauerThreeHalvesMeasure

/-- The `L²` representative of a polynomial evaluation is the evaluation. -/
theorem coeFn_polynomialEvalGegenbauerThreeHalvesLp (𝕜 : Type*) [RCLike 𝕜] (q : ℝ[X]) :
    ⇑(polynomialEvalGegenbauerThreeHalvesLp 𝕜 q) =ᵐ[gegenbauerThreeHalvesMeasure]
      fun x : ℝ => (algebraMap ℝ 𝕜) (q.eval x) :=
  TauCeti.coeFn_polynomialEvalLp 𝕜 integrable_pow_gegenbauerThreeHalvesMeasure q

/-! ### The normalized modes -/

/-- The squared `L²(gegenbauerThreeHalvesMeasure)` norm of `C_n^{(3/2)}`. That it is this
rational number is `EpsilonEridani.integral_gegenbauerThreeHalves_mul_self`; the name is
introduced here because the normalisation of the modes, and the Gegenbauer coefficients of a
function, are read against it. -/
noncomputable def gegenbauerThreeHalvesNormSq (n : ℕ) : ℝ :=
  2 * (n + 1) * (n + 2) / (2 * n + 3)

/-- The defining value `2 (n + 1) (n + 2) / (2n + 3)` of the squared norm. -/
theorem gegenbauerThreeHalvesNormSq_def (n : ℕ) :
    gegenbauerThreeHalvesNormSq n = 2 * (n + 1) * (n + 2) / (2 * n + 3) :=
  (rfl)

/-- No Gegenbauer polynomial is null for the weight measure. -/
theorem gegenbauerThreeHalvesNormSq_pos (n : ℕ) : 0 < gegenbauerThreeHalvesNormSq n := by
  rw [gegenbauerThreeHalvesNormSq_def]
  positivity

/-- The norm `‖C_n^{(3/2)}‖`, by which the modes are divided, is nonzero. -/
theorem sqrt_gegenbauerThreeHalvesNormSq_ne_zero (n : ℕ) :
    Real.sqrt (gegenbauerThreeHalvesNormSq n) ≠ 0 :=
  Real.sqrt_ne_zero'.mpr (gegenbauerThreeHalvesNormSq_pos n)

/-- The normalized Gegenbauer mode `C_n^{(3/2)} / ‖C_n^{(3/2)}‖`, of unit norm in
`L²(gegenbauerThreeHalvesMeasure)`. -/
noncomputable def normalizedGegenbauerThreeHalves (n : ℕ) (x : ℝ) : ℝ :=
  (gegenbauerThreeHalves ℝ n).eval x / Real.sqrt (gegenbauerThreeHalvesNormSq n)

/-- The defining equation of the normalized Gegenbauer mode. -/
@[simp]
theorem normalizedGegenbauerThreeHalves_def (n : ℕ) (x : ℝ) :
    normalizedGegenbauerThreeHalves n x =
      (gegenbauerThreeHalves ℝ n).eval x / Real.sqrt (gegenbauerThreeHalvesNormSq n) :=
  (rfl)

/-- The normalized Gegenbauer mode is continuous. -/
theorem continuous_normalizedGegenbauerThreeHalves (n : ℕ) :
    Continuous (normalizedGegenbauerThreeHalves n) :=
  (gegenbauerThreeHalves ℝ n).continuous.div_const _

/-- The normalized Gegenbauer mode is square integrable for the weight measure. -/
theorem memLp_normalizedGegenbauerThreeHalves (n : ℕ) :
    MemLp (normalizedGegenbauerThreeHalves n) 2 gegenbauerThreeHalvesMeasure := by
  have hcont := continuous_normalizedGegenbauerThreeHalves n
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  exact (hcont.pow 2).continuousOn.integrable_gegenbauerThreeHalvesMeasure

/-- The normalized Gegenbauer mode, cast into any `RCLike` scalar field, is square integrable
for the weight measure. -/
theorem memLp_algebraMap_normalizedGegenbauerThreeHalves {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) (normalizedGegenbauerThreeHalves n x)) 2
      gegenbauerThreeHalvesMeasure := by
  simpa only [← RCLike.algebraMap_eq_ofReal] using
    (memLp_normalizedGegenbauerThreeHalves n).ofReal (K := 𝕜)

/-- The normalized Gegenbauer mode as a vector of `L²(gegenbauerThreeHalvesMeasure)`. -/
noncomputable def normalizedGegenbauerThreeHalvesLp (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Lp 𝕜 2 gegenbauerThreeHalvesMeasure :=
  (memLp_algebraMap_normalizedGegenbauerThreeHalves (𝕜 := 𝕜) n).toLp _

/-- The `L²` representative of the `n`-th mode is the normalized Gegenbauer mode. -/
theorem coeFn_normalizedGegenbauerThreeHalvesLp {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) :
    ⇑(normalizedGegenbauerThreeHalvesLp 𝕜 n) =ᵐ[gegenbauerThreeHalvesMeasure]
      fun x : ℝ => (algebraMap ℝ 𝕜) (normalizedGegenbauerThreeHalves n x) :=
  MemLp.coeFn_toLp _

/-- The normalized Gegenbauer modes have Kronecker-delta pairings for the weight measure. -/
theorem integral_normalizedGegenbauerThreeHalves_mul_normalizedGegenbauerThreeHalves (m n : ℕ) :
    ∫ x, normalizedGegenbauerThreeHalves m x * normalizedGegenbauerThreeHalves n x
      ∂gegenbauerThreeHalvesMeasure = if m = n then 1 else 0 := by
  have hm := sqrt_gegenbauerThreeHalvesNormSq_ne_zero m
  have hn := sqrt_gegenbauerThreeHalvesNormSq_ne_zero n
  have hsplit : ∀ x : ℝ, normalizedGegenbauerThreeHalves m x *
      normalizedGegenbauerThreeHalves n x =
        (Real.sqrt (gegenbauerThreeHalvesNormSq m) *
            Real.sqrt (gegenbauerThreeHalvesNormSq n))⁻¹ *
          ((gegenbauerThreeHalves ℝ m).eval x * (gegenbauerThreeHalves ℝ n).eval x) := by
    intro x
    rw [normalizedGegenbauerThreeHalves_def, normalizedGegenbauerThreeHalves_def]
    field_simp
  rw [integral_congr_ae (Filter.Eventually.of_forall hsplit), integral_const_mul,
    integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves]
  split_ifs with h
  · subst h
    rw [← gegenbauerThreeHalvesNormSq_def,
      Real.mul_self_sqrt (gegenbauerThreeHalvesNormSq_pos m).le,
      inv_mul_cancel₀ (gegenbauerThreeHalvesNormSq_pos m).ne']
  · rw [mul_zero]

/-- The normalized Gegenbauer modes have Kronecker-delta inner products in
`L²(gegenbauerThreeHalvesMeasure)`. -/
@[simp]
theorem inner_normalizedGegenbauerThreeHalvesLp {𝕜 : Type*} [RCLike 𝕜] (m n : ℕ) :
    inner 𝕜 (normalizedGegenbauerThreeHalvesLp 𝕜 m) (normalizedGegenbauerThreeHalvesLp 𝕜 n) =
      if m = n then 1 else 0 := by
  have hinner : ∀ a b : ℝ,
      inner 𝕜 ((algebraMap ℝ 𝕜) a) ((algebraMap ℝ 𝕜) b) = (algebraMap ℝ 𝕜) (a * b) := by
    intro a b
    simp [RCLike.inner_apply, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, mul_comm]
  have hcast : inner 𝕜 (normalizedGegenbauerThreeHalvesLp 𝕜 m)
      (normalizedGegenbauerThreeHalvesLp 𝕜 n) =
        ∫ x, (algebraMap ℝ 𝕜) (normalizedGegenbauerThreeHalves m x *
          normalizedGegenbauerThreeHalves n x) ∂gegenbauerThreeHalvesMeasure := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_normalizedGegenbauerThreeHalvesLp (𝕜 := 𝕜) m,
      coeFn_normalizedGegenbauerThreeHalvesLp (𝕜 := 𝕜) n] with x hxm hxn
    rw [hxm, hxn]
    exact hinner _ _
  rw [hcast, RCLike.algebraMap_eq_ofReal, integral_ofReal,
    integral_normalizedGegenbauerThreeHalves_mul_normalizedGegenbauerThreeHalves]
  rcases eq_or_ne m n with rfl | hmn
  · simp
  · simp [hmn]

/-- The normalized Gegenbauer modes form an orthonormal family in
`L²(gegenbauerThreeHalvesMeasure)`. -/
theorem orthonormal_normalizedGegenbauerThreeHalvesLp {𝕜 : Type*} [RCLike 𝕜] :
    Orthonormal 𝕜 (normalizedGegenbauerThreeHalvesLp 𝕜) :=
  orthonormal_iff_ite.mpr inner_normalizedGegenbauerThreeHalvesLp

/-! ### From the modes to every polynomial -/

/-- Under the evaluation map, `C_n^{(3/2)}` is its norm times the `n`-th normalized mode. -/
theorem polynomialEvalGegenbauerThreeHalvesLp_gegenbauerThreeHalves (𝕜 : Type*) [RCLike 𝕜]
    (n : ℕ) :
    polynomialEvalGegenbauerThreeHalvesLp 𝕜 (gegenbauerThreeHalves ℝ n) =
      Real.sqrt (gegenbauerThreeHalvesNormSq n) • normalizedGegenbauerThreeHalvesLp 𝕜 n := by
  refine Lp.ext ?_
  filter_upwards [coeFn_polynomialEvalGegenbauerThreeHalvesLp 𝕜 (gegenbauerThreeHalves ℝ n),
    coeFn_normalizedGegenbauerThreeHalvesLp (𝕜 := 𝕜) n,
    Lp.coeFn_smul (Real.sqrt (gegenbauerThreeHalvesNormSq n))
      (normalizedGegenbauerThreeHalvesLp 𝕜 n)] with x heval hmode hsmul
  rw [heval, hsmul, Pi.smul_apply, hmode, normalizedGegenbauerThreeHalves_def, Algebra.smul_def,
    ← map_mul]
  congr 1
  have hs := sqrt_gegenbauerThreeHalvesNormSq_ne_zero n
  field_simp

/-- Every polynomial evaluation lies in the linear span of the normalized Gegenbauer modes: the
family is a basis of `ℝ[X]`, so this is the basis expansion transported into `L²`. -/
theorem polynomialEvalGegenbauerThreeHalvesLp_mem_span (𝕜 : Type*) [RCLike 𝕜] (q : ℝ[X]) :
    polynomialEvalGegenbauerThreeHalvesLp 𝕜 q ∈
      Submodule.span 𝕜 (Set.range (normalizedGegenbauerThreeHalvesLp 𝕜)) := by
  set S := Submodule.span 𝕜 (Set.range (normalizedGegenbauerThreeHalvesLp 𝕜)) with hS
  have hq : q ∈ Submodule.span ℝ (Set.range (gegenbauerThreeHalvesBasis ℝ)) := by
    rw [Module.Basis.span_eq]
    exact Submodule.mem_top
  refine Submodule.span_induction ?_
    ((polynomialEvalGegenbauerThreeHalvesLp 𝕜).map_zero ▸ S.zero_mem)
    (fun _ _ _ _ hx hy => by simpa using S.add_mem hx hy)
    (fun a _ _ hx => by
      rw [map_smul, algebra_compatible_smul 𝕜 a]
      exact S.smul_mem _ hx) hq
  rintro p ⟨n, rfl⟩
  rw [gegenbauerThreeHalvesBasis_apply, polynomialEvalGegenbauerThreeHalvesLp_gegenbauerThreeHalves,
    algebra_compatible_smul 𝕜]
  exact S.smul_mem _ (Submodule.subset_span (Set.mem_range_self n))

/-- A vector orthogonal to every normalized Gegenbauer mode is orthogonal to the `L²` evaluation
of every real polynomial. -/
theorem inner_polynomialEvalGegenbauerThreeHalvesLp_eq_zero (𝕜 : Type*) [RCLike 𝕜]
    (g : Lp 𝕜 2 gegenbauerThreeHalvesMeasure)
    (hmode : ∀ n, inner 𝕜 g (normalizedGegenbauerThreeHalvesLp 𝕜 n) = 0) (q : ℝ[X]) :
    inner 𝕜 g (polynomialEvalGegenbauerThreeHalvesLp 𝕜 q) = 0 := by
  refine Submodule.span_induction ?_ (by simp)
    (fun _ _ _ _ hx hy => by simp [inner_add_right, hx, hy])
    (fun _ _ _ hx => by simp [inner_smul_right, hx])
    (polynomialEvalGegenbauerThreeHalvesLp_mem_span 𝕜 q)
  rintro v ⟨n, rfl⟩
  exact hmode n

/-! ### Completeness -/

/-- Every exponential weight is integrable for the Gegenbauer weight measure: it is a finite
measure supported on the compact interval `[-1, 1]`. This is the hypothesis of moment
determinacy. -/
theorem integrable_exp_mul_abs_gegenbauerThreeHalvesMeasure (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|)) gegenbauerThreeHalvesMeasure :=
  (Real.continuous_exp.comp
    (continuous_const.mul continuous_abs)).continuousOn.integrable_gegenbauerThreeHalvesMeasure

/-- A vector orthogonal to every normalized Gegenbauer mode has vanishing monomial moments. -/
theorem monomial_moment_gegenbauerThreeHalvesMeasure_eq_zero (𝕜 : Type*) [RCLike 𝕜]
    (g : Lp 𝕜 2 gegenbauerThreeHalvesMeasure)
    (hmode : ∀ n, inner 𝕜 g (normalizedGegenbauerThreeHalvesLp 𝕜 n) = 0) (n : ℕ) :
    ∫ x, (algebraMap ℝ 𝕜 x) ^ n * g x ∂gegenbauerThreeHalvesMeasure = 0 := by
  have hflip : inner 𝕜 (polynomialEvalGegenbauerThreeHalvesLp 𝕜 (X ^ n)) g = 0 :=
    inner_eq_zero_symm.mpr
      (inner_polynomialEvalGegenbauerThreeHalvesLp_eq_zero 𝕜 g hmode (X ^ n))
  rw [MeasureTheory.L2.inner_def] at hflip
  rw [← hflip]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_polynomialEvalGegenbauerThreeHalvesLp 𝕜 (X ^ n)] with x hx
  rw [hx, RCLike.inner_apply, Polynomial.eval_pow, Polynomial.eval_X,
    RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal, RCLike.ofReal_pow]
  ring

/-- **Completeness of the Gegenbauer family.** The orthogonal complement of the span of the
normalized modes is trivial: a vector orthogonal to all of them has vanishing monomial moments,
hence is almost everywhere zero by moment determinacy. -/
theorem orthogonal_span_normalizedGegenbauerThreeHalvesLp_eq_bot (𝕜 : Type*) [RCLike 𝕜] :
    (Submodule.span 𝕜 (Set.range (normalizedGegenbauerThreeHalvesLp 𝕜)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro g hg
  have hmode : ∀ n, inner 𝕜 g (normalizedGegenbauerThreeHalvesLp 𝕜 n) = 0 := fun n =>
    inner_eq_zero_symm.mpr
      ((Submodule.mem_orthogonal _ _).mp hg _ (Submodule.subset_span ⟨n, rfl⟩))
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (TauCeti.ae_eq_zero_of_forall_moment_eq_zero_of_exists_integrable_exp
      (ν := gegenbauerThreeHalvesMeasure)
      ⟨1, one_pos, integrable_exp_mul_abs_gegenbauerThreeHalvesMeasure 1⟩ (Lp.memLp g)
      (monomial_moment_gegenbauerThreeHalvesMeasure_eq_zero 𝕜 g hmode))

/-- **The Gegenbauer polynomials of index `3/2` are a Hilbert basis of
`L²(gegenbauerThreeHalvesMeasure)`.** Orthonormality is
`orthonormal_normalizedGegenbauerThreeHalvesLp` and completeness is
`orthogonal_span_normalizedGegenbauerThreeHalvesLp_eq_bot`. -/
noncomputable def gegenbauerThreeHalvesHilbertBasis (𝕜 : Type*) [RCLike 𝕜] :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 gegenbauerThreeHalvesMeasure) :=
  HilbertBasis.mkOfOrthogonalEqBot orthonormal_normalizedGegenbauerThreeHalvesLp
    (orthogonal_span_normalizedGegenbauerThreeHalvesLp_eq_bot 𝕜)

/-- The basis vectors are the normalized Gegenbauer modes. Without this the construction would
only exhibit *some* Hilbert basis of `L²(gegenbauerThreeHalvesMeasure)`. -/
@[simp]
theorem coe_gegenbauerThreeHalvesHilbertBasis (𝕜 : Type*) [RCLike 𝕜] :
    ⇑(gegenbauerThreeHalvesHilbertBasis 𝕜) = normalizedGegenbauerThreeHalvesLp 𝕜 :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The `n`-th Gegenbauer coefficient of a vector of `L²(gegenbauerThreeHalvesMeasure)`, under
the isometry onto `ℓ²(ℕ)` carried by the Hilbert basis, is its inner product with the `n`-th
normalized mode. -/
@[simp]
theorem gegenbauerThreeHalvesHilbertBasis_repr_apply (𝕜 : Type*) [RCLike 𝕜]
    (f : Lp 𝕜 2 gegenbauerThreeHalvesMeasure) (n : ℕ) :
    (gegenbauerThreeHalvesHilbertBasis 𝕜).repr f n =
      inner 𝕜 (normalizedGegenbauerThreeHalvesLp 𝕜 n) f := by
  rw [HilbertBasis.repr_apply_apply, coe_gegenbauerThreeHalvesHilbertBasis]

end EpsilonEridani
