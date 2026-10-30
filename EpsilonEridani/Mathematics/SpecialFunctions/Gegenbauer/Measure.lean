/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.SpecialFunctions.Gegenbauer.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
import EpsilonEridani.Mathematics.Calculus.Polynomial
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The weight measure and orthogonality of the Gegenbauer polynomials of index `3/2`

The Gegenbauer polynomials `C_n^{(3/2)}` of `Mathematics/SpecialFunctions/Gegenbauer/Basic.lean`
are orthogonal on `[-1, 1]` for the weight `1 - x²`. This file defines the corresponding finite
measure, `(1 - x²) dx` on `(-1, 1]`, and proves the orthogonality relation together with the
closed form of the squared norms,

  `∫₋₁¹ (1 - x²) C_m^{(3/2)}(x) C_n^{(3/2)}(x) dx = δ_{mn} 2 (n + 1) (n + 2) / (2n + 3)`

(DLMF Table 18.3.1 at `λ = 3/2`, where the Gamma-function constant
`π 2^{1 - 2λ} Γ(n + 2λ) / ((n + λ) Γ(λ)² n!)` reduces to this rational number).

The measure is spelled as Lebesgue measure on `(-1, 1]` with a density, the shape the standard
`withDensity` and weighted-`L²` API consumes.

Orthogonality is proved by the Sturm–Liouville argument: `C_n^{(3/2)}` solves
`((1 - x²)² y')' = -n (n + 3) (1 - x²) y`, the operator on the left is symmetric under the
integral over `[-1, 1]` because `(1 - x²)²` vanishes at both endpoints
(`Polynomial.integral_derivative_mul_derivative_mul_comm`), and the eigenvalues `n (n + 3)` are
distinct. The squared norms then follow from the three-term recurrence, paired with
`C_{n+2}^{(3/2)}` and with `C_{n+1}^{(3/2)}`.

## Main definitions

* `EpsilonEridani.gegenbauerThreeHalvesMeasure`: the measure `(1 - x²) dx` on `(-1, 1]`.
* `EpsilonEridani.gegenbauerThreeHalvesNormSq`: the squared norm
  `2 (n + 1) (n + 2) / (2n + 3)` of `C_n^{(3/2)}` for the measure.
* `EpsilonEridani.normalizedGegenbauerThreeHalves`: the normalized mode
  `C_n^{(3/2)} / ‖C_n^{(3/2)}‖`.

## Main statements

* `EpsilonEridani.integral_gegenbauerThreeHalvesMeasure`: integrals against the measure are
  weighted interval integrals over `[-1, 1]`.
* `EpsilonEridani.gegenbauerThreeHalvesMeasure_univ`,
  `EpsilonEridani.gegenbauerThreeHalvesMeasure_real_univ`: the measure has total mass `4 / 3`,
  in `ℝ≥0∞` and in `ℝ`; in particular it is a finite measure.
* `ContinuousOn.integrable_gegenbauerThreeHalvesMeasure`: a function continuous on `[-1, 1]` is
  integrable for the measure, with
  `EpsilonEridani.integrable_exp_mul_abs_gegenbauerThreeHalvesMeasure` its exponential instance and
  `EpsilonEridani.exists_integrable_exp_mul_abs_withDensity_one_sub_sq` the form of that instance
  the weighted-`L²` machinery takes.
* `EpsilonEridani.integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves`: the orthogonality
  relation, with the squared norms `EpsilonEridani.integral_gegenbauerThreeHalves_mul_self`.

## References

* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, 4th edition (1975),
  chapter IV, §4.7.
* NIST Digital Library of Mathematical Functions, §18.3 and §18.8.
* The Chebyshev weight measure, the template this construction follows. The measure as a
  `withDensity` of Lebesgue measure, with its integral and integrability lemmas, is adapted from
  `Polynomial.Chebyshev.measureT`, `Polynomial.Chebyshev.integral_measureT` and
  `Polynomial.Chebyshev.integrable_measureT` in Mathlib
  (`Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality`); the squared norms as
  a named constant and the normalized modes are adapted from `TauCeti.chebyshevTNormSq` and
  `TauCeti.normalizedChebyshevT` in the TauCeti library
  (`TauCeti.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Measure`).
-/

public section

namespace EpsilonEridani

open MeasureTheory Polynomial

/-- The orthogonality measure `(1 - x²) dx` on `(-1, 1]` of the Gegenbauer polynomials
`C_n^{(3/2)}`. -/
noncomputable def gegenbauerThreeHalvesMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioc (-1 : ℝ) 1)).withDensity fun x => ENNReal.ofReal (1 - x ^ 2)

/-- `gegenbauerThreeHalvesMeasure` is Lebesgue measure on `(-1, 1]` with density `1 - x²`. -/
theorem gegenbauerThreeHalvesMeasure_eq_withDensity :
    gegenbauerThreeHalvesMeasure =
      (volume.restrict (Set.Ioc (-1 : ℝ) 1)).withDensity fun x => ENNReal.ofReal (1 - x ^ 2) :=
  (rfl)

/-- The weight `1 - x²` is non-negative on `(-1, 1]`. -/
private theorem one_sub_sq_nonneg_of_mem_Ioc {x : ℝ} (hx : x ∈ Set.Ioc (-1 : ℝ) 1) :
    0 ≤ 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

/-- The weight `1 - x²` is non-negative almost everywhere on `(-1, 1]`, the sign hypothesis of the
weighted-`L²` machinery. -/
theorem ae_zero_le_one_sub_sq :
    ∀ᵐ x ∂(volume.restrict (Set.Ioc (-1 : ℝ) 1)), 0 ≤ 1 - x ^ 2 :=
  ae_restrict_of_forall_mem measurableSet_Ioc fun _ => one_sub_sq_nonneg_of_mem_Ioc

/-- Integration against `gegenbauerThreeHalvesMeasure` is integration over `[-1, 1]` against the
weight `1 - x²`. -/
theorem integral_gegenbauerThreeHalvesMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) :
    ∫ x, f x ∂gegenbauerThreeHalvesMeasure = ∫ x in -1..1, (1 - x ^ 2) • f x := by
  rw [gegenbauerThreeHalvesMeasure_eq_withDensity,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top), intervalIntegral.integral_of_le (by norm_num)]
  refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
  rw [ENNReal.toReal_ofReal (one_sub_sq_nonneg_of_mem_Ioc hx)]

/-- `gegenbauerThreeHalvesMeasure` has total mass `∫₋₁¹ (1 - x²) dx = 4 / 3`. -/
@[simp]
theorem gegenbauerThreeHalvesMeasure_univ :
    gegenbauerThreeHalvesMeasure Set.univ = 4 / 3 := by
  rw [gegenbauerThreeHalvesMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal
      ((by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self) ae_zero_le_one_sub_sq,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_sub
      intervalIntegrable_const ((continuous_pow 2).intervalIntegrable _ _), integral_pow]
  -- evaluate the mass, then normalise `ofReal (4 / 3)` to the `ℝ≥0∞` literal
  norm_num [ENNReal.ofReal_div_of_pos, ENNReal.ofReal_ofNat]

/-- The total mass of `gegenbauerThreeHalvesMeasure`, as a real number. -/
@[simp]
theorem gegenbauerThreeHalvesMeasure_real_univ :
    gegenbauerThreeHalvesMeasure.real Set.univ = 4 / 3 := by
  rw [measureReal_def, gegenbauerThreeHalvesMeasure_univ]
  norm_num

instance : IsFiniteMeasure gegenbauerThreeHalvesMeasure where
  measure_univ_lt_top := by
    rw [gegenbauerThreeHalvesMeasure_univ]
    exact ENNReal.div_lt_top (by norm_num) (by norm_num)

/-- A function continuous on `[-1, 1]` is integrable for `gegenbauerThreeHalvesMeasure`; in
particular every polynomial is. -/
theorem _root_.ContinuousOn.integrable_gegenbauerThreeHalvesMeasure {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E} (hf : ContinuousOn f (Set.Icc (-1) 1)) :
    Integrable f gegenbauerThreeHalvesMeasure := by
  rw [gegenbauerThreeHalvesMeasure_eq_withDensity,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
  simp_rw [ENNReal.toReal_ofReal']
  exact (by fun_prop : Continuous fun x : ℝ => max (1 - x ^ 2) 0).continuousOn.smul hf

/-- Every exponential weight is integrable for `gegenbauerThreeHalvesMeasure`: it is a finite
measure supported on the compact interval `[-1, 1]`. -/
theorem integrable_exp_mul_abs_gegenbauerThreeHalvesMeasure (a : ℝ) :
    Integrable (fun x : ℝ => Real.exp (a * |x|)) gegenbauerThreeHalvesMeasure :=
  (Real.continuous_exp.comp
    (continuous_const.mul continuous_abs)).continuousOn.integrable_gegenbauerThreeHalvesMeasure

/-- The exponential moment of the weight measure, in the existential `withDensity` form the
weighted-`L²` machinery takes it. -/
theorem exists_integrable_exp_mul_abs_withDensity_one_sub_sq :
    ∃ a : ℝ, 0 < a ∧ Integrable (fun x : ℝ => Real.exp (a * |x|))
      ((volume.restrict (Set.Ioc (-1 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (1 - x ^ 2)) :=
  ⟨1, one_pos, gegenbauerThreeHalvesMeasure_eq_withDensity ▸
    integrable_exp_mul_abs_gegenbauerThreeHalvesMeasure 1⟩

/-- A product of polynomial evaluations is integrable for `gegenbauerThreeHalvesMeasure`. -/
private theorem integrable_eval_mul_eval (p q : ℝ[X]) :
    Integrable (fun x => p.eval x * q.eval x) gegenbauerThreeHalvesMeasure :=
  (p.continuous.mul q.continuous).continuousOn.integrable_gegenbauerThreeHalvesMeasure

/-- The weighted pairing of two polynomial evaluations depends only on their product. -/
private theorem integral_eval_mul_eval_congr {p₁ q₁ p₂ q₂ : ℝ[X]}
    (h : p₁ * q₁ = p₂ * q₂) :
    ∫ x, p₁.eval x * q₁.eval x ∂gegenbauerThreeHalvesMeasure =
      ∫ x, p₂.eval x * q₂.eval x ∂gegenbauerThreeHalvesMeasure :=
  integral_congr_ae (ae_of_all _ fun x => by simpa only [eval_mul] using congrArg (eval x) h)

/-- The eigenvalues `n (n + 3)` of the Gegenbauer differential equation are distinct. -/
private theorem natCast_mul_add_three_ne {m n : ℕ} (h : m ≠ n) :
    (m : ℝ) * (m + 3) ≠ n * (n + 3) := by
  intro he
  have he' : m * (m + 3) = n * (n + 3) := by exact_mod_cast he
  rcases Nat.lt_or_gt_of_ne h with h' | h' <;> nlinarith

/-- **Orthogonality** of the Gegenbauer polynomials of index `3/2` for distinct degrees:
`∫₋₁¹ (1 - x²) C_m^{(3/2)}(x) C_n^{(3/2)}(x) dx = 0` for `m ≠ n`. -/
theorem integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves_of_ne {m n : ℕ} (h : m ≠ n) :
    ∫ x, (gegenbauerThreeHalves ℝ m).eval x * (gegenbauerThreeHalves ℝ n).eval x
      ∂gegenbauerThreeHalvesMeasure = 0 := by
  have hs := integral_derivative_mul_derivative_mul_comm ((1 - X ^ 2) ^ 2)
    (gegenbauerThreeHalves ℝ m) (gegenbauerThreeHalves ℝ n) (a := -1) (b := 1) (by norm_num)
    (by norm_num)
  rw [derivative_one_sub_X_sq_sq_mul_derivative_gegenbauerThreeHalves,
    derivative_one_sub_X_sq_sq_mul_derivative_gegenbauerThreeHalves] at hs
  have key : ∀ (c : ℝ) (p q : ℝ[X]), ∫ x in (-1 : ℝ)..1, (-C c * ((1 - X ^ 2) * p) * q).eval x =
      -c * ∫ x, p.eval x * q.eval x ∂gegenbauerThreeHalvesMeasure := fun c p q => by
    rw [integral_gegenbauerThreeHalvesMeasure, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ => by
      simp only [eval_mul, eval_neg, eval_C, eval_sub, eval_one, eval_pow, eval_X, smul_eq_mul]
      ring
  have hcomm : ∫ x, (gegenbauerThreeHalves ℝ n).eval x * (gegenbauerThreeHalves ℝ m).eval x
      ∂gegenbauerThreeHalvesMeasure = ∫ x, (gegenbauerThreeHalves ℝ m).eval x *
        (gegenbauerThreeHalves ℝ n).eval x ∂gegenbauerThreeHalvesMeasure :=
    integral_eval_mul_eval_congr
      (mul_comm (gegenbauerThreeHalves ℝ n) (gegenbauerThreeHalves ℝ m))
  rw [key, mul_comm (gegenbauerThreeHalves ℝ m), key, hcomm] at hs
  have hne := sub_ne_zero.mpr (natCast_mul_add_three_ne h).symm
  exact (mul_eq_zero.mp (by linear_combination hs)).resolve_left hne

/-- The three-term recurrence `(n + 2) C_{n+2} = (2n + 5) X C_{n+1} - (n + 3) C_n`, integrated
against `C_j^{(3/2)}`. -/
private theorem integral_gegenbauerThreeHalves_add_two_mul (n j : ℕ) :
    ((n : ℝ) + 2) * ∫ x, (gegenbauerThreeHalves ℝ (n + 2)).eval x *
        (gegenbauerThreeHalves ℝ j).eval x ∂gegenbauerThreeHalvesMeasure =
      (2 * n + 5) * (∫ x, (X * gegenbauerThreeHalves ℝ (n + 1)).eval x *
          (gegenbauerThreeHalves ℝ j).eval x ∂gegenbauerThreeHalvesMeasure) -
        (n + 3) * ∫ x, (gegenbauerThreeHalves ℝ n).eval x *
          (gegenbauerThreeHalves ℝ j).eval x ∂gegenbauerThreeHalvesMeasure := by
  have hrec : ∀ x, ((n : ℝ) + 2) * ((gegenbauerThreeHalves ℝ (n + 2)).eval x *
      (gegenbauerThreeHalves ℝ j).eval x) =
        (2 * n + 5) * ((X * gegenbauerThreeHalves ℝ (n + 1)).eval x *
          (gegenbauerThreeHalves ℝ j).eval x) -
        (n + 3) * ((gegenbauerThreeHalves ℝ n).eval x * (gegenbauerThreeHalves ℝ j).eval x) :=
    fun x => by
      have := congrArg (eval x) (C_mul_gegenbauerThreeHalves_add_two ℝ n)
      simp only [eval_mul, eval_sub, eval_C, eval_X] at this ⊢
      linear_combination (gegenbauerThreeHalves ℝ j).eval x * this
  rw [← MeasureTheory.integral_const_mul, integral_congr_ae (ae_of_all _ hrec),
    integral_sub ((integrable_eval_mul_eval _ _).const_mul _)
      ((integrable_eval_mul_eval _ _).const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]

/-- The squared norms satisfy
`(n + 2) (2n + 7) ‖C_{n+2}^{(3/2)}‖² = (2n + 5) (n + 4) ‖C_{n+1}^{(3/2)}‖²`, from the three-term
recurrence paired with `C_{n+2}^{(3/2)}` and with `C_{n+1}^{(3/2)}`. -/
private theorem integral_gegenbauerThreeHalves_mul_self_add_two (n : ℕ) :
    ((n : ℝ) + 2) * (2 * n + 7) * ∫ x, (gegenbauerThreeHalves ℝ (n + 2)).eval x *
        (gegenbauerThreeHalves ℝ (n + 2)).eval x ∂gegenbauerThreeHalvesMeasure =
      (2 * n + 5) * (n + 4) * ∫ x, (gegenbauerThreeHalves ℝ (n + 1)).eval x *
        (gegenbauerThreeHalves ℝ (n + 1)).eval x ∂gegenbauerThreeHalvesMeasure := by
  have h₁ := integral_gegenbauerThreeHalves_add_two_mul n (n + 2)
  have h₂ := integral_gegenbauerThreeHalves_add_two_mul (n + 1) (n + 1)
  rw [integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves_of_ne (m := n) (n := n + 2)
    (by omega)] at h₁
  rw [integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves_of_ne (by omega)] at h₂
  -- the two cross terms `∫ x C_{n+1} C_{n+2}` coincide
  have hX : ∫ x, (X * gegenbauerThreeHalves ℝ (n + 1 + 1)).eval x *
      (gegenbauerThreeHalves ℝ (n + 1)).eval x ∂gegenbauerThreeHalvesMeasure =
        ∫ x, (X * gegenbauerThreeHalves ℝ (n + 1)).eval x *
          (gegenbauerThreeHalves ℝ (n + 2)).eval x ∂gegenbauerThreeHalvesMeasure :=
    integral_eval_mul_eval_congr (by ring)
  rw [hX] at h₂
  push_cast at h₂
  linear_combination (2 * (n : ℝ) + 7) * h₁ - (2 * (n : ℝ) + 5) * h₂

/-- The squared norm of `C_n^{(3/2)}` for `gegenbauerThreeHalvesMeasure`, the rational number
`2 (n + 1) (n + 2) / (2n + 3)` of `EpsilonEridani.integral_gegenbauerThreeHalves_mul_self`. The
normalisation of the Gegenbauer modes, and the Gegenbauer coefficients of a function, are read
against it. -/
noncomputable def gegenbauerThreeHalvesNormSq (n : ℕ) : ℝ :=
  2 * (n + 1) * (n + 2) / (2 * n + 3)

/-- The defining value `2 (n + 1) (n + 2) / (2n + 3)` of the squared norm. -/
theorem gegenbauerThreeHalvesNormSq_def (n : ℕ) :
    gegenbauerThreeHalvesNormSq n = 2 * (n + 1) * (n + 2) / (2 * n + 3) :=
  (rfl)

/-- The squared norm `2 (n + 1) (n + 2) / (2n + 3)` is positive; with
`EpsilonEridani.integral_gegenbauerThreeHalves_mul_self` this says that no `C_n^{(3/2)}` is null
for the weight measure. -/
theorem gegenbauerThreeHalvesNormSq_pos (n : ℕ) : 0 < gegenbauerThreeHalvesNormSq n := by
  rw [gegenbauerThreeHalvesNormSq_def]
  positivity

/-- The squared norm of `C_n^{(3/2)}`:
`∫₋₁¹ (1 - x²) C_n^{(3/2)}(x)² dx = 2 (n + 1) (n + 2) / (2n + 3)`. -/
@[simp]
theorem integral_gegenbauerThreeHalves_mul_self : ∀ n : ℕ,
    ∫ x, (gegenbauerThreeHalves ℝ n).eval x * (gegenbauerThreeHalves ℝ n).eval x
      ∂gegenbauerThreeHalvesMeasure = gegenbauerThreeHalvesNormSq n
  | 0 => by
    norm_num [gegenbauerThreeHalvesNormSq_def, measureReal_def, gegenbauerThreeHalvesMeasure_univ]
  | 1 => by
    have h : ∀ x : ℝ, (1 - x ^ 2) • ((gegenbauerThreeHalves ℝ 1).eval x *
        (gegenbauerThreeHalves ℝ 1).eval x) = 9 * x ^ 2 - 9 * x ^ 4 := fun x => by
      simp only [gegenbauerThreeHalves_one, eval_mul, eval_C, eval_X, smul_eq_mul]
      ring
    rw [integral_gegenbauerThreeHalvesMeasure]
    simp_rw [h]
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ => 9 * x ^ 2).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ => 9 * x ^ 4).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
      integral_pow]
    norm_num [gegenbauerThreeHalvesNormSq_def]
  | n + 2 => by
    have h := integral_gegenbauerThreeHalves_mul_self_add_two n
    rw [integral_gegenbauerThreeHalves_mul_self (n + 1)] at h
    have h₂ : ((n : ℝ) + 2) * (2 * n + 7) ≠ 0 := by positivity
    rw [← mul_right_inj' h₂, h]
    simp only [gegenbauerThreeHalvesNormSq_def]
    push_cast
    field_simp
    ring

/-- **Orthogonality relation** of the Gegenbauer polynomials of index `3/2`:
`∫₋₁¹ (1 - x²) C_m^{(3/2)}(x) C_n^{(3/2)}(x) dx = δ_{mn} 2 (n + 1) (n + 2) / (2n + 3)`. -/
@[simp]
theorem integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves (m n : ℕ) :
    ∫ x, (gegenbauerThreeHalves ℝ m).eval x * (gegenbauerThreeHalves ℝ n).eval x
      ∂gegenbauerThreeHalvesMeasure =
        if m = n then gegenbauerThreeHalvesNormSq n else 0 := by
  split_ifs with h
  · rw [h, integral_gegenbauerThreeHalves_mul_self]
  · exact integral_gegenbauerThreeHalves_mul_gegenbauerThreeHalves_of_ne h

/-! ### The normalized modes -/

/-- The normalized Gegenbauer mode `C_n^{(3/2)} / ‖C_n^{(3/2)}‖`, of unit norm for
`gegenbauerThreeHalvesMeasure`. -/
noncomputable def normalizedGegenbauerThreeHalves (n : ℕ) (x : ℝ) : ℝ :=
  (gegenbauerThreeHalves ℝ n).eval x / Real.sqrt (gegenbauerThreeHalvesNormSq n)

/-- The defining equation of the normalized Gegenbauer mode. -/
theorem normalizedGegenbauerThreeHalves_def (n : ℕ) (x : ℝ) :
    normalizedGegenbauerThreeHalves n x =
      (gegenbauerThreeHalves ℝ n).eval x / Real.sqrt (gegenbauerThreeHalvesNormSq n) :=
  (rfl)

end EpsilonEridani
