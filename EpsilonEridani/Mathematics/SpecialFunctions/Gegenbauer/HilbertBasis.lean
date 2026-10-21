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
`TauCeti.hilbertBasisOfWeightedMeasure`, whose conclusion is a basis of `L²` of a measure spelled
as an explicit `withDensity`. That is a different space to Lean: the body of
`gegenbauerThreeHalvesMeasure` is not exposed outside its own module, so
`Lp 𝕜 2 gegenbauerThreeHalvesMeasure` is not definitionally the `L²` of the `withDensity` form,
and every statement would have to be transported along
`EpsilonEridani.gegenbauerThreeHalvesMeasure_eq_withDensity`.

The resulting unitary `L²(gegenbauerThreeHalvesMeasure) ≃ₗᵢ ℓ²(ℕ)` is what makes the Gegenbauer
coefficients of a function a complete invariant: two functions with the same coefficients agree
almost everywhere, and a square-summable sequence of coefficients comes from a function. That is
the setting in which the expansion of a leading-twist light-cone distribution amplitude
`6 u (1 - u) ∑ₙ aₙ C_n^{(3/2)}(2u - 1)` converges, and in which the evolution of the amplitude
decouples into the independent evolution of its coefficients.

## Main definitions

* `EpsilonEridani.polynomialEvalGegenbauerThreeHalvesLp`: polynomial evaluation as a linear map
  into `L²(gegenbauerThreeHalvesMeasure)`.
* `EpsilonEridani.normalizedGegenbauerThreeHalves`,
  `EpsilonEridani.normalizedGegenbauerThreeHalvesLp`: the normalized mode
  `C_n^{(3/2)} / ‖C_n^{(3/2)}‖`, as a function and as a vector of `L²`.
* `EpsilonEridani.gegenbauerThreeHalvesHilbertBasis`: the Hilbert basis of
  `L²(gegenbauerThreeHalvesMeasure)` it forms.

## Main statements

* `EpsilonEridani.norm_polynomialEvalGegenbauerThreeHalvesLp_gegenbauerThreeHalves`: the `L²` norm
  of `C_n^{(3/2)}` is `√(gegenbauerThreeHalvesNormSq n)`.
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

/-! ### Polynomial evaluation in `L²` -/

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

/-- The norm `‖C_n^{(3/2)}‖`, by which the modes are divided, is nonzero. -/
theorem sqrt_gegenbauerThreeHalvesNormSq_ne_zero (n : ℕ) :
    Real.sqrt (gegenbauerThreeHalvesNormSq n) ≠ 0 :=
  Real.sqrt_ne_zero'.mpr (gegenbauerThreeHalvesNormSq_pos n)

/-- The normalized Gegenbauer mode `C_n^{(3/2)} / ‖C_n^{(3/2)}‖`, of unit norm in
`L²(gegenbauerThreeHalvesMeasure)`. -/
noncomputable def normalizedGegenbauerThreeHalves (n : ℕ) (x : ℝ) : ℝ :=
  (gegenbauerThreeHalves ℝ n).eval x / Real.sqrt (gegenbauerThreeHalvesNormSq n)

/-- The defining equation of the normalized Gegenbauer mode. -/
theorem normalizedGegenbauerThreeHalves_def (n : ℕ) (x : ℝ) :
    normalizedGegenbauerThreeHalves n x =
      (gegenbauerThreeHalves ℝ n).eval x / Real.sqrt (gegenbauerThreeHalvesNormSq n) :=
  (rfl)

/-- The normalized Gegenbauer mode as a vector of `L²(gegenbauerThreeHalvesMeasure)`: the `L²`
evaluation of `C_n^{(3/2)}`, divided by the norm `‖C_n^{(3/2)}‖`. -/
noncomputable def normalizedGegenbauerThreeHalvesLp (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Lp 𝕜 2 gegenbauerThreeHalvesMeasure :=
  (Real.sqrt (gegenbauerThreeHalvesNormSq n))⁻¹ •
    polynomialEvalGegenbauerThreeHalvesLp 𝕜 (gegenbauerThreeHalves ℝ n)

/-- Under the evaluation map, `C_n^{(3/2)}` is its norm times the `n`-th normalized mode. -/
theorem polynomialEvalGegenbauerThreeHalvesLp_gegenbauerThreeHalves (𝕜 : Type*) [RCLike 𝕜]
    (n : ℕ) :
    polynomialEvalGegenbauerThreeHalvesLp 𝕜 (gegenbauerThreeHalves ℝ n) =
      Real.sqrt (gegenbauerThreeHalvesNormSq n) • normalizedGegenbauerThreeHalvesLp 𝕜 n := by
  rw [normalizedGegenbauerThreeHalvesLp,
    smul_inv_smul₀ (sqrt_gegenbauerThreeHalvesNormSq_ne_zero n)]

/-- The `L²` representative of the `n`-th mode is the normalized Gegenbauer mode. -/
theorem coeFn_normalizedGegenbauerThreeHalvesLp {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) :
    ⇑(normalizedGegenbauerThreeHalvesLp 𝕜 n) =ᵐ[gegenbauerThreeHalvesMeasure]
      fun x : ℝ => (algebraMap ℝ 𝕜) (normalizedGegenbauerThreeHalves n x) := by
  filter_upwards [Lp.coeFn_smul (Real.sqrt (gegenbauerThreeHalvesNormSq n))⁻¹
      (polynomialEvalGegenbauerThreeHalvesLp 𝕜 (gegenbauerThreeHalves ℝ n)),
    coeFn_polynomialEvalGegenbauerThreeHalvesLp 𝕜 (gegenbauerThreeHalves ℝ n)] with x hsmul heval
  rw [normalizedGegenbauerThreeHalvesLp, hsmul, Pi.smul_apply, heval, Algebra.smul_def, ← map_mul,
    inv_mul_eq_div, normalizedGegenbauerThreeHalves_def]

/-- The normalized Gegenbauer modes have Kronecker-delta pairings for the weight measure. -/
@[simp]
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
    rw [Real.mul_self_sqrt (gegenbauerThreeHalvesNormSq_pos m).le,
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

/-- The `L²(gegenbauerThreeHalvesMeasure)` norm of `C_n^{(3/2)}` is the square root of
`gegenbauerThreeHalvesNormSq n`, which is what justifies that name. -/
theorem norm_polynomialEvalGegenbauerThreeHalvesLp_gegenbauerThreeHalves (𝕜 : Type*) [RCLike 𝕜]
    (n : ℕ) :
    ‖polynomialEvalGegenbauerThreeHalvesLp 𝕜 (gegenbauerThreeHalves ℝ n)‖ =
      Real.sqrt (gegenbauerThreeHalvesNormSq n) := by
  rw [polynomialEvalGegenbauerThreeHalvesLp_gegenbauerThreeHalves, norm_smul,
    (orthonormal_normalizedGegenbauerThreeHalvesLp (𝕜 := 𝕜)).norm_eq_one n, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]

/-! ### From the modes to every polynomial -/

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
private theorem inner_polynomialEvalGegenbauerThreeHalvesLp_eq_zero (𝕜 : Type*) [RCLike 𝕜]
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

/-- A vector orthogonal to every normalized Gegenbauer mode integrates to zero against every
monomial: `∫ xⁿ g x ∂gegenbauerThreeHalvesMeasure = 0`. -/
private theorem integral_pow_mul_gegenbauerThreeHalvesMeasure_eq_zero (𝕜 : Type*) [RCLike 𝕜]
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
      (integral_pow_mul_gegenbauerThreeHalvesMeasure_eq_zero 𝕜 g hmode))

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
