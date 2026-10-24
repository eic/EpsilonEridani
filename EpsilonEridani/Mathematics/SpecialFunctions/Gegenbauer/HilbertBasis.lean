/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.Gegenbauer.Measure
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Map
public import TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness
public import TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-!
# The Gegenbauer polynomials of index `3/2` as a Hilbert basis

The Gegenbauer polynomials `C_n^{(3/2)}` are orthogonal for the measure `(1 - x²) dx` on
`(-1, 1]`, with squared norms `2 (n + 1) (n + 2) / (2n + 3)`
(`EpsilonEridani.Mathematics.SpecialFunctions.Gegenbauer.Measure`). This file puts the normalized
modes `C_n^{(3/2)} / ‖C_n^{(3/2)}‖` in `L²(gegenbauerThreeHalvesMeasure)` and proves that they are
a *Hilbert basis* of that space: an orthonormal family whose closed span is everything.

Both halves are instances of the family-agnostic machinery of TauCeti rather than arguments made
here. `TauCeti.hilbertBasisOfWeightedMeasure` turns an orthogonality relation for a weight into an
orthonormal basis of the weighted `L²` space, and
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` discharges its completeness hypothesis for
a family of polynomials of exact degree (`EpsilonEridani.degree_gegenbauerThreeHalves`) against a
measure with one finite exponential moment — which holds here because the weight measure is finite
and supported on `[-1, 1]`, so `exp (a |x|)` is a continuous function integrated over a compact set
(`EpsilonEridani.integrable_exp_mul_abs_gegenbauerThreeHalvesMeasure`). The weight data the
machinery consumes is `μ = volume.restrict (Ioc (-1) 1)` with `w x = 1 - x²`.

That machinery is stated for the weighted measure in its `withDensity` spelling, which is the
body of `gegenbauerThreeHalvesMeasure` but is not definitionally available outside the module
defining it. The two `L²` spaces are nevertheless *equal*, so `TauCeti.castLpₗᵢ` at
`EpsilonEridani.gegenbauerThreeHalvesMeasure_eq_withDensity` moves vectors and bases between them
without moving representatives, exactly as `TauCeti.gaussianHermiteHilbertBasis` moves the Hermite
basis onto `L²(γ)`.

The resulting unitary `L²(gegenbauerThreeHalvesMeasure) ≃ₗᵢ ℓ²(ℕ)` is what makes the Gegenbauer
coefficients of a function a complete invariant: two functions with the same coefficients agree
almost everywhere, and a square-summable sequence of coefficients comes from a function. That is
the setting in which the expansion of a leading-twist light-cone distribution amplitude
`6 u (1 - u) ∑ₙ aₙ C_n^{(3/2)}(2u - 1)` converges, and in which the evolution of the amplitude
decouples into the independent evolution of its coefficients.

## Main definitions

* `EpsilonEridani.normalizedGegenbauerThreeHalvesLp`: the normalized mode
  `C_n^{(3/2)} / ‖C_n^{(3/2)}‖` as a vector of `L²(gegenbauerThreeHalvesMeasure)`.
* `EpsilonEridani.gegenbauerThreeHalvesHilbertBasis`: the Hilbert basis of
  `L²(gegenbauerThreeHalvesMeasure)` the modes form.

## Main statements

* `EpsilonEridani.inner_normalizedGegenbauerThreeHalvesLp_eq_integral`: the inner product against
  the `n`-th mode — the `n`-th Gegenbauer coefficient — is the weighted integral.
* `EpsilonEridani.orthonormal_normalizedGegenbauerThreeHalvesLp`: the modes are orthonormal.
* `EpsilonEridani.orthogonal_span_normalizedGegenbauerThreeHalvesLp_eq_bot`: completeness.
* `EpsilonEridani.gegenbauerThreeHalvesHilbertBasis_repr_apply`: the `n`-th coordinate of the
  resulting isometry onto `ℓ²(ℕ)` is the inner product with the `n`-th mode.

## References

* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, 4th edition (1975),
  chapter IV, §4.7 and §3.1.
* The weighted-`L²` development of the TauCeti library: the bridge
  `TauCeti.Analysis.InnerProductSpace.WeightedOrthogonalBasis` with its completeness input
  `TauCeti.Analysis.InnerProductSpace.PolynomialCompleteness`, and
  `TauCeti.Probability.Distributions.Gaussian.Hermite.Basis`, the instance of both at the Hermite
  family whose transport onto a named measure this file follows.
* `TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure`, from which the shape of the
  mode layer — `TauCeti.normalizedChebyshevTLp` with its representative and inner-product lemmas —
  is adapted.
-/

public section

namespace EpsilonEridani

open MeasureTheory

/-! ### The weight data of the family

The weighted-basis bridge takes the reference measure and the weight separately, so the
orthogonality relation and the exponential moment are restated for
`volume.restrict (Ioc (-1) 1)` and `w x = 1 - x²`, whose `withDensity` is
`gegenbauerThreeHalvesMeasure`. -/

/-- The weight `1 - x²` is non-negative almost everywhere on `(-1, 1]`. -/
private theorem one_sub_sq_nonneg_ae :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)), 0 ≤ 1 - x ^ 2 :=
  ae_restrict_of_forall_mem measurableSet_Ioc fun _ hx => by nlinarith [hx.1, hx.2]

/-- The orthogonality relation in the form the weighted-basis bridge takes it: the weight is a
factor of the integrand and the measure is unweighted. -/
private theorem integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves_mul_weight (m n : ℕ) :
    ∫ x, (gegenbauerThreeHalves ℝ m).eval x * (gegenbauerThreeHalves ℝ n).eval x * (1 - x ^ 2)
        ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)) =
      if m = n then gegenbauerThreeHalvesNormSq n else 0 := by
  rw [← integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves m n,
    integral_gegenbauerThreeHalvesMeasure, intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
  rw [smul_eq_mul]
  ring

/-- The exponential moment of the weight measure, in the existential `withDensity` form the
completeness theorem takes it. -/
private theorem exp_moment_gegenbauerThreeHalvesWeight :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      ((volume.restrict (Set.Ioc (-1 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (1 - x ^ 2)) :=
  ⟨1, one_pos, gegenbauerThreeHalvesMeasure_eq_withDensity ▸
    integrable_exp_mul_abs_gegenbauerThreeHalvesMeasure 1⟩

/-- The `MemLp` obligation of the normalized family, the generic
`TauCeti.memLp_two_bareNormalized` at `p n = C_n^{(3/2)}`, `c = gegenbauerThreeHalvesNormSq`. -/
private theorem memLp_normalizedGegenbauerThreeHalves (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    MemLp (fun x : ℝ => (algebraMap ℝ 𝕜) ((gegenbauerThreeHalves ℝ n).eval x /
        Real.sqrt (gegenbauerThreeHalvesNormSq n))) 2
      ((volume.restrict (Set.Ioc (-1 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (1 - x ^ 2)) :=
  TauCeti.memLp_two_bareNormalized (𝕜 := 𝕜) exp_moment_gegenbauerThreeHalvesWeight
    (gegenbauerThreeHalves ℝ) gegenbauerThreeHalvesNormSq n

/-! ### The modes in `L²` -/

/-- The normalized Gegenbauer mode as a vector of `L²(gegenbauerThreeHalvesMeasure)`: the
`TauCeti.bareNormalizedLp` vector of the weight data, carried onto the named measure by
`TauCeti.castLpₗᵢ`. -/
noncomputable def normalizedGegenbauerThreeHalvesLp (𝕜 : Type*) [RCLike 𝕜] (n : ℕ) :
    Lp 𝕜 2 gegenbauerThreeHalvesMeasure :=
  TauCeti.castLpₗᵢ (𝕜 := 𝕜) gegenbauerThreeHalvesMeasure_eq_withDensity.symm
    (TauCeti.bareNormalizedLp (𝕜 := 𝕜) (fun n x => (gegenbauerThreeHalves ℝ n).eval x)
      (fun x => 1 - x ^ 2) gegenbauerThreeHalvesNormSq
      (memLp_normalizedGegenbauerThreeHalves 𝕜) n)

/-- The `L²` representative of the `n`-th mode is the normalized Gegenbauer mode. -/
theorem coeFn_normalizedGegenbauerThreeHalvesLp {𝕜 : Type*} [RCLike 𝕜] (n : ℕ) :
    ⇑(normalizedGegenbauerThreeHalvesLp 𝕜 n) =ᵐ[gegenbauerThreeHalvesMeasure]
      fun x : ℝ => (algebraMap ℝ 𝕜) (normalizedGegenbauerThreeHalves n x) := by
  -- The representative of the pre-transport vector, read on the named measure: the two measures
  -- are equal, and the vector's own type mentions only the `withDensity` one, so the filter can
  -- be rewritten.
  have hbare : ∀ᵐ x ∂gegenbauerThreeHalvesMeasure,
      ⇑(TauCeti.bareNormalizedLp (𝕜 := 𝕜) (fun n x => (gegenbauerThreeHalves ℝ n).eval x)
          (fun x => 1 - x ^ 2) gegenbauerThreeHalvesNormSq
          (memLp_normalizedGegenbauerThreeHalves 𝕜) n) x =
        (algebraMap ℝ 𝕜) ((gegenbauerThreeHalves ℝ n).eval x /
          Real.sqrt (gegenbauerThreeHalvesNormSq n)) := by
    rw [gegenbauerThreeHalvesMeasure_eq_withDensity]
    exact TauCeti.coeFn_bareNormalizedLp (𝕜 := 𝕜) (fun n x => (gegenbauerThreeHalves ℝ n).eval x)
      (fun x => 1 - x ^ 2) gegenbauerThreeHalvesNormSq
      (memLp_normalizedGegenbauerThreeHalves 𝕜) n
  filter_upwards [hbare] with x hx
  rw [normalizedGegenbauerThreeHalvesLp, TauCeti.coeFn_castLpₗᵢ, hx,
    normalizedGegenbauerThreeHalves_def]

/-- **The `n`-th Gegenbauer coefficient as a weighted integral.** Pairing with the `n`-th mode in
`L²(gegenbauerThreeHalvesMeasure)` is integration against it for the weight, which is how the
coefficient of a concrete amplitude is computed. -/
theorem inner_normalizedGegenbauerThreeHalvesLp_eq_integral {𝕜 : Type*} [RCLike 𝕜] (n : ℕ)
    (f : Lp 𝕜 2 gegenbauerThreeHalvesMeasure) :
    inner 𝕜 (normalizedGegenbauerThreeHalvesLp 𝕜 n) f =
      ∫ x, (algebraMap ℝ 𝕜) (normalizedGegenbauerThreeHalves n x) * f x
        ∂gegenbauerThreeHalvesMeasure := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_normalizedGegenbauerThreeHalvesLp (𝕜 := 𝕜) n] with x hx
  rw [hx, RCLike.inner_apply, RCLike.algebraMap_eq_ofReal, RCLike.conj_ofReal]
  exact mul_comm _ _

/-! ### The Hilbert basis -/

/-- **The Gegenbauer polynomials of index `3/2` are a Hilbert basis of
`L²(gegenbauerThreeHalvesMeasure)`.** This is `TauCeti.hilbertBasisOfWeightedMeasure` at the weight
data of the family, whose completeness hypothesis is the exact-degree case
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot` of moment determinacy, carried onto the
named measure by `TauCeti.castLpₗᵢ`. -/
noncomputable def gegenbauerThreeHalvesHilbertBasis (𝕜 : Type*) [RCLike 𝕜] :
    HilbertBasis ℕ 𝕜 (Lp 𝕜 2 gegenbauerThreeHalvesMeasure) :=
  (TauCeti.hilbertBasisOfWeightedMeasure (𝕜 := 𝕜)
    (fun n x => (gegenbauerThreeHalves ℝ n).eval x) (fun x => 1 - x ^ 2)
    gegenbauerThreeHalvesNormSq one_sub_sq_nonneg_ae (by fun_prop)
    gegenbauerThreeHalvesNormSq_pos
    integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves_mul_weight
    (memLp_normalizedGegenbauerThreeHalves 𝕜)
    (TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot (𝕜 := 𝕜) (gegenbauerThreeHalves ℝ)
      (fun x => 1 - x ^ 2) gegenbauerThreeHalvesNormSq (degree_gegenbauerThreeHalves ℝ)
      gegenbauerThreeHalvesNormSq_pos exp_moment_gegenbauerThreeHalvesWeight
      (memLp_normalizedGegenbauerThreeHalves 𝕜))).mapₗᵢ
      (TauCeti.castLpₗᵢ gegenbauerThreeHalvesMeasure_eq_withDensity.symm)

/-- The basis vectors are the normalized Gegenbauer modes. Without this the construction would
only exhibit *some* Hilbert basis of `L²(gegenbauerThreeHalvesMeasure)`. -/
@[simp]
theorem coe_gegenbauerThreeHalvesHilbertBasis (𝕜 : Type*) [RCLike 𝕜] :
    ⇑(gegenbauerThreeHalvesHilbertBasis 𝕜) = normalizedGegenbauerThreeHalvesLp 𝕜 := by
  funext n
  rw [gegenbauerThreeHalvesHilbertBasis, HilbertBasis.mapₗᵢ_apply,
    TauCeti.coe_hilbertBasisOfWeightedMeasure, normalizedGegenbauerThreeHalvesLp]

/-- The normalized Gegenbauer modes form an orthonormal family in
`L²(gegenbauerThreeHalvesMeasure)`: they are the vectors of a Hilbert basis. -/
theorem orthonormal_normalizedGegenbauerThreeHalvesLp {𝕜 : Type*} [RCLike 𝕜] :
    Orthonormal 𝕜 (normalizedGegenbauerThreeHalvesLp 𝕜) := by
  rw [← coe_gegenbauerThreeHalvesHilbertBasis 𝕜]
  exact (gegenbauerThreeHalvesHilbertBasis 𝕜).orthonormal

/-- The normalized Gegenbauer modes have Kronecker-delta inner products in
`L²(gegenbauerThreeHalvesMeasure)`. -/
@[simp]
theorem inner_normalizedGegenbauerThreeHalvesLp {𝕜 : Type*} [RCLike 𝕜] (m n : ℕ) :
    inner 𝕜 (normalizedGegenbauerThreeHalvesLp 𝕜 m) (normalizedGegenbauerThreeHalvesLp 𝕜 n) =
      if m = n then 1 else 0 :=
  orthonormal_iff_ite.mp orthonormal_normalizedGegenbauerThreeHalvesLp m n

/-- **Completeness of the Gegenbauer family.** The orthogonal complement of the span of the
normalized modes is trivial, because they are the vectors of a Hilbert basis, whose span is
dense. -/
theorem orthogonal_span_normalizedGegenbauerThreeHalvesLp_eq_bot (𝕜 : Type*) [RCLike 𝕜] :
    (Submodule.span 𝕜 (Set.range (normalizedGegenbauerThreeHalvesLp 𝕜)))ᗮ = ⊥ := by
  rw [← Submodule.topologicalClosure_eq_top_iff, ← coe_gegenbauerThreeHalvesHilbertBasis 𝕜]
  exact (gegenbauerThreeHalvesHilbertBasis 𝕜).dense_span

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
