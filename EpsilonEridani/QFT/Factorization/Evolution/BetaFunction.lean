/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import EpsilonEridani.Mathematics.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic.LinearCombination

/-!
# The beta function as a formal power series, and its change under a redefinition of the coupling

The running of a coupling `a` with the scale is `da/dt = β(a)`, `t = log (μ² / μ₀²)`. In
perturbation theory `β` is a formal power series in `a` without constant or linear term,
normalised as

  `β(a) = - β₀ a² - β₁ a³ - β₂ a⁴ - ⋯`,

so that `β₀ > 0` is asymptotic freedom; `betaCoeff β n` is the coefficient `βₙ`.

A redefinition of the coupling is a formal substitution `a' = F(a) = u a + c₁ a² + c₂ a³ + ⋯`
with `u` a unit, an element of the substitution group
`EpsilonEridani.PowerSeries.SubstGroup`. A change of renormalisation scheme is one with `u = 1`;
a change with `F = u a` is a change of normalisation of the coupling, such as
`α_s / (2π) = 2 · α_s / (4π)`.

By the chain rule the coupling `a' = F(a)` runs with `da'/dt = F'(a) β(a)`, so its beta function
`β' = transformBeta F β` is determined by

  `β'(F(a)) = F'(a) β(a)`        (`subst_transformBeta`, `transformBeta_eq_iff`),

and `transformBeta` is an action of the substitution group (`transformBeta_one`,
`transformBeta_mul`). Comparing the coefficients of `a²`, `a³` and `a⁴` gives

  `β₀' = β₀`,  `β₁' = β₁`,  `β₂' = β₂ - c₁ β₁ + (c₂ - c₁²) β₀`

for a change of scheme: the first two coefficients of the beta function are scheme independent,
and the third is not, unless `β₀ = β₁ = 0`.

## Main definitions

* `betaCoeff β n`: the coefficient `βₙ = -[a^{n+2}] β`.
* `transformBeta F β`: the beta function of the coupling `a' = F(a)`.
* `cubicSchemeChange c₁ c₂`: the change of scheme `a ↦ a + c₁ a² + c₂ a³`.

## Main statements

* `transformBeta_eq_iff`: `transformBeta F β` is the unique `β'` with `β'(F(a)) = F'(a) β(a)`.
* `X_sq_dvd_transformBeta`: a beta function stays one under a redefinition of the coupling.
* `betaCoeff_transformBeta_zero`, `betaCoeff_transformBeta_one`,
  `betaCoeff_transformBeta_two`: the transformation of `β₀`, `β₁`, `β₂` under any redefinition.
* `betaCoeff_transformBeta_zero_of_coeff_one_eq_one`,
  `betaCoeff_transformBeta_one_of_coeff_one_eq_one`: `β₀` and `β₁` are invariant under a change
  of scheme.
* `betaCoeff_transformBeta_two_of_coeff_one_eq_one`: `β₂' = β₂ - c₁ β₁ + (c₂ - c₁²) β₀`.
* `forall_betaCoeff_transformBeta_two_eq_iff`: `β₂` is invariant under every change of scheme
  exactly when `β₀ = β₁ = 0`.
* `transformBeta_scale`, `betaCoeff_transformBeta_scale`: under `a ↦ u a` the coefficients
  scale as `βₙ' = βₙ / u^{n+1}`; for `a = α_s/(2π)` against `a₄ = α_s/(4π)` this is
  `betaCoeff_transformBeta_scale_two`.

## References

* W. E. Caswell, *Phys. Rev. Lett.* **33** (1974) 244.
* D. R. T. Jones, *Nucl. Phys. B* **75** (1974) 531.
* J. C. Collins, *Renormalization*, Cambridge University Press (1984).
-/

public section

noncomputable section

open PowerSeries EpsilonEridani.PowerSeries

namespace EpsilonEridani
namespace QFT
namespace Factorization
namespace Evolution

variable {R : Type*} [CommRing R]

/-- The coefficient `βₙ` of a beta function `β(a) = - β₀ a² - β₁ a³ - ⋯`, that is
`-[a^{n+2}] β`. -/
def betaCoeff (β : R⟦X⟧) (n : ℕ) : R :=
  -coeff (n + 2) β

@[simp]
lemma betaCoeff_def (β : R⟦X⟧) (n : ℕ) : betaCoeff β n = -coeff (n + 2) β := (rfl)

/-! ### The beta function of a redefined coupling -/

/-- The beta function of the coupling `a' = F(a)`, given the beta function `β` of `a`:
`β'(a') = F'(F⁻¹(a')) β(F⁻¹(a'))`. -/
def transformBeta (F : SubstGroup R) (β : R⟦X⟧) : R⟦X⟧ :=
  (d⁄dX F.toPowerSeries * β).subst F⁻¹.toPowerSeries

lemma transformBeta_def (F : SubstGroup R) (β : R⟦X⟧) :
    transformBeta F β = (d⁄dX F.toPowerSeries * β).subst F⁻¹.toPowerSeries := (rfl)

/-- The defining property of the transformed beta function: `β'(F(a)) = F'(a) β(a)`, the chain
rule for `da'/dt` with `a' = F(a)`. -/
theorem subst_transformBeta (F : SubstGroup R) (β : R⟦X⟧) :
    (transformBeta F β).subst F.toPowerSeries = d⁄dX F.toPowerSeries * β := by
  rw [transformBeta_def, subst_comp_subst_apply F⁻¹.hasSubst F.hasSubst,
    SubstGroup.subst_toPowerSeries_inv, X_subst]

/-- `transformBeta F β` is the unique power series `β'` with `β'(F(a)) = F'(a) β(a)`. -/
theorem transformBeta_eq_iff {F : SubstGroup R} {β β' : R⟦X⟧} :
    transformBeta F β = β' ↔ β'.subst F.toPowerSeries = d⁄dX F.toPowerSeries * β := by
  refine ⟨fun h => h ▸ subst_transformBeta F β, fun h => ?_⟩
  rw [transformBeta_def, ← h, subst_comp_subst_apply F.hasSubst F⁻¹.hasSubst,
    SubstGroup.toPowerSeries_subst_inv, X_subst]

/-- Leaving the coupling unchanged leaves its beta function unchanged. -/
@[simp]
theorem transformBeta_one (β : R⟦X⟧) : transformBeta 1 β = β := by
  rw [transformBeta_eq_iff, SubstGroup.toPowerSeries_one, X_subst, derivative_X, one_mul]

/-- Redefining the coupling by `G` and then by `F` is redefining it by `F * G`, the substitution
`a ↦ F(G(a))`. -/
theorem transformBeta_mul (F G : SubstGroup R) (β : R⟦X⟧) :
    transformBeta (F * G) β = transformBeta F (transformBeta G β) := by
  rw [transformBeta_eq_iff, SubstGroup.toPowerSeries_mul,
    ← subst_comp_subst_apply F.hasSubst G.hasSubst, subst_transformBeta, subst_mul G.hasSubst,
    subst_transformBeta, derivative_subst G.hasSubst, mul_assoc]

/-! ### The first three coefficients -/

/-- A beta function, a power series without constant or linear term, stays one under a
redefinition of the coupling. -/
theorem X_sq_dvd_transformBeta (F : SubstGroup R) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    X ^ 2 ∣ transformBeta F β := by
  obtain ⟨γ, rfl⟩ := hβ
  rw [transformBeta_def, mul_left_comm, subst_mul F⁻¹.hasSubst, subst_pow F⁻¹.hasSubst,
    subst_X F⁻¹.hasSubst]
  exact (pow_dvd_pow_of_dvd (X_dvd_iff.mpr F⁻¹.constantCoeff_toPowerSeries) 2).mul_right _

/-- The coefficients of `a²`, `a³` and `a⁴` in `β'(F(a)) = F'(a) β(a)`, for
`β' = transformBeta F β` and `F(a) = u a + c₁ a² + c₂ a³ + ⋯`. -/
private lemma coeff_subst_transformBeta (F : SubstGroup R) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    coeff 1 F.toPowerSeries ^ 2 * coeff 2 (transformBeta F β) =
        coeff 1 F.toPowerSeries * coeff 2 β ∧
      2 * coeff 1 F.toPowerSeries * coeff 2 F.toPowerSeries * coeff 2 (transformBeta F β) +
          coeff 1 F.toPowerSeries ^ 3 * coeff 3 (transformBeta F β) =
        coeff 1 F.toPowerSeries * coeff 3 β + 2 * coeff 2 F.toPowerSeries * coeff 2 β ∧
      (coeff 2 F.toPowerSeries ^ 2 + 2 * coeff 1 F.toPowerSeries * coeff 3 F.toPowerSeries) *
            coeff 2 (transformBeta F β) +
          3 * coeff 1 F.toPowerSeries ^ 2 * coeff 2 F.toPowerSeries *
            coeff 3 (transformBeta F β) +
          coeff 1 F.toPowerSeries ^ 4 * coeff 4 (transformBeta F β) =
        coeff 1 F.toPowerSeries * coeff 4 β + 2 * coeff 2 F.toPowerSeries * coeff 3 β +
          3 * coeff 3 F.toPowerSeries * coeff 2 β := by
  have hβ' := X_pow_dvd_iff.mp hβ
  have hγ := X_pow_dvd_iff.mp (X_sq_dvd_transformBeta F hβ)
  have h₂ := congrArg (coeff 2) (subst_transformBeta F β)
  have h₃ := congrArg (coeff 3) (subst_transformBeta F β)
  have h₄ := congrArg (coeff 4) (subst_transformBeta F β)
  -- Expand `[aⁿ] β'(F(a))` as a finite sum over the powers `F(a)ᵈ`, `d ≤ n`, and `[aⁿ] F'(a) β(a)`
  -- as a Cauchy product; the coefficients of `a⁰` and `a¹` of `β` and `β'` vanish.
  simp [coeff_subst_eq_sum_range F.constantCoeff_toPowerSeries, Finset.sum_range_succ, coeff_mul,
    Finset.Nat.sum_antidiagonal_succ, coeff_derivative, hγ 0 (by norm_num), hγ 1 (by norm_num),
    hβ' 0 (by norm_num), hβ' 1 (by norm_num), pow_succ] at h₂ h₃ h₄
  refine ⟨?_, ?_, ?_⟩
  · linear_combination h₂
  · linear_combination h₃
  · linear_combination h₄

/-- The one-loop coefficient under a redefinition of the coupling: `u β₀' = β₀`, where
`u = F'(0)`. -/
theorem betaCoeff_transformBeta_zero (F : SubstGroup R) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    coeff 1 F.toPowerSeries * betaCoeff (transformBeta F β) 0 = betaCoeff β 0 := by
  have h := (coeff_subst_transformBeta F hβ).1
  rw [betaCoeff_def, betaCoeff_def]
  exact F.isUnit_coeff_one_toPowerSeries.mul_left_cancel (by linear_combination -h)

/-- The two-loop coefficient under a redefinition of the coupling: `u² β₁' = β₁`, where
`u = F'(0)`. -/
theorem betaCoeff_transformBeta_one (F : SubstGroup R) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    coeff 1 F.toPowerSeries ^ 2 * betaCoeff (transformBeta F β) 1 = betaCoeff β 1 := by
  obtain ⟨-, h₃, -⟩ := coeff_subst_transformBeta F hβ
  have h₀ := betaCoeff_transformBeta_zero F hβ
  simp only [betaCoeff_def, Nat.reduceAdd] at h₀ ⊢
  exact F.isUnit_coeff_one_toPowerSeries.mul_left_cancel
    (by linear_combination -h₃ - 2 * coeff 2 F.toPowerSeries * h₀)

/-- The three-loop coefficient under a redefinition `F(a) = u a + c₁ a² + c₂ a³ + ⋯` of the
coupling: `u⁵ β₂' = u² β₂ - u c₁ β₁ + (u c₂ - c₁²) β₀`. -/
theorem betaCoeff_transformBeta_two (F : SubstGroup R) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    coeff 1 F.toPowerSeries ^ 5 * betaCoeff (transformBeta F β) 2 =
      coeff 1 F.toPowerSeries ^ 2 * betaCoeff β 2 -
        coeff 1 F.toPowerSeries * coeff 2 F.toPowerSeries * betaCoeff β 1 +
        (coeff 1 F.toPowerSeries * coeff 3 F.toPowerSeries - coeff 2 F.toPowerSeries ^ 2) *
          betaCoeff β 0 := by
  obtain ⟨-, -, h₄⟩ := coeff_subst_transformBeta F hβ
  have h₀ := betaCoeff_transformBeta_zero F hβ
  have h₁ := betaCoeff_transformBeta_one F hβ
  simp only [betaCoeff_def, Nat.reduceAdd] at h₀ h₁ ⊢
  linear_combination -coeff 1 F.toPowerSeries * h₄ -
    (coeff 2 F.toPowerSeries ^ 2 + 2 * coeff 1 F.toPowerSeries * coeff 3 F.toPowerSeries) * h₀ -
    3 * coeff 1 F.toPowerSeries * coeff 2 F.toPowerSeries * h₁

/-! ### Scheme independence -/

/-- **`β₀` is scheme independent**: a change of renormalisation scheme, `F'(0) = 1`, leaves the
one-loop coefficient of a beta function unchanged. -/
theorem betaCoeff_transformBeta_zero_of_coeff_one_eq_one {F : SubstGroup R}
    (hF : coeff 1 F.toPowerSeries = 1) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    betaCoeff (transformBeta F β) 0 = betaCoeff β 0 := by
  simpa [hF] using betaCoeff_transformBeta_zero F hβ

/-- **`β₁` is scheme independent**: a change of renormalisation scheme, `F'(0) = 1`, leaves the
two-loop coefficient of a beta function unchanged. -/
theorem betaCoeff_transformBeta_one_of_coeff_one_eq_one {F : SubstGroup R}
    (hF : coeff 1 F.toPowerSeries = 1) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    betaCoeff (transformBeta F β) 1 = betaCoeff β 1 := by
  simpa [hF] using betaCoeff_transformBeta_one F hβ

/-- The three-loop coefficient under the change of scheme `a ↦ a + c₁ a² + c₂ a³ + ⋯`:
`β₂' = β₂ - c₁ β₁ + (c₂ - c₁²) β₀`. -/
theorem betaCoeff_transformBeta_two_of_coeff_one_eq_one {F : SubstGroup R}
    (hF : coeff 1 F.toPowerSeries = 1) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    betaCoeff (transformBeta F β) 2 = betaCoeff β 2 - coeff 2 F.toPowerSeries * betaCoeff β 1 +
      (coeff 3 F.toPowerSeries - coeff 2 F.toPowerSeries ^ 2) * betaCoeff β 0 := by
  simpa [hF] using betaCoeff_transformBeta_two F hβ

/-- The change of scheme `a ↦ a + c₁ a² + c₂ a³`. -/
def cubicSchemeChange (c₁ c₂ : R) : SubstGroup R :=
  ⟨X + C c₁ * X ^ 2 + C c₂ * X ^ 3, by simp, by simp [coeff_X]⟩

@[simp]
lemma toPowerSeries_cubicSchemeChange (c₁ c₂ : R) :
    (cubicSchemeChange c₁ c₂).toPowerSeries = X + C c₁ * X ^ 2 + C c₂ * X ^ 3 := (rfl)

/-- Under `a ↦ a + c₁ a² + c₂ a³` the three-loop coefficient becomes
`β₂ - c₁ β₁ + (c₂ - c₁²) β₀`. -/
theorem betaCoeff_transformBeta_cubicSchemeChange_two (c₁ c₂ : R) {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    betaCoeff (transformBeta (cubicSchemeChange c₁ c₂) β) 2 =
      betaCoeff β 2 - c₁ * betaCoeff β 1 + (c₂ - c₁ ^ 2) * betaCoeff β 0 := by
  simpa [coeff_X, coeff_C_mul_X_pow] using
    betaCoeff_transformBeta_two_of_coeff_one_eq_one (F := cubicSchemeChange c₁ c₂)
      (by simp [coeff_X]) hβ

/-- **`β₂` is scheme dependent**: the three-loop coefficient is invariant under every change of
renormalisation scheme exactly when the first two coefficients vanish. -/
theorem forall_betaCoeff_transformBeta_two_eq_iff {β : R⟦X⟧} (hβ : X ^ 2 ∣ β) :
    (∀ F : SubstGroup R, coeff 1 F.toPowerSeries = 1 →
        betaCoeff (transformBeta F β) 2 = betaCoeff β 2) ↔
      betaCoeff β 0 = 0 ∧ betaCoeff β 1 = 0 := by
  refine ⟨fun h => ?_, fun ⟨h₀, h₁⟩ F hF => ?_⟩
  · have h₀ := h (cubicSchemeChange 0 1) (by simp [coeff_X])
    have h₁ := h (cubicSchemeChange 1 1) (by simp [coeff_X])
    rw [betaCoeff_transformBeta_cubicSchemeChange_two _ _ hβ] at h₀ h₁
    constructor
    · linear_combination h₀
    · linear_combination -h₁
  · rw [betaCoeff_transformBeta_two_of_coeff_one_eq_one hF hβ, h₀, h₁]
    ring

/-! ### Changes of normalisation -/

/-- Under the change of normalisation `a' = u a` the beta function becomes
`β'(a') = u β(a' / u)`. -/
theorem transformBeta_scale (u : Rˣ) (β : R⟦X⟧) :
    transformBeta (SubstGroup.scale u) β = C (u : R) * rescale (↑u⁻¹ : R) β := by
  rw [transformBeta_eq_iff, SubstGroup.toPowerSeries_scale, ← smul_eq_C_mul, ← smul_eq_C_mul,
    PowerSeries.subst_smul (HasSubst.smul_X' _), ← rescale_eq_subst, rescale_rescale]
  simp

/-- Under the change of normalisation `a' = u a` the coefficients of the beta function scale as
`βₙ' = βₙ / u^{n+1}`. -/
theorem betaCoeff_transformBeta_scale (u : Rˣ) (β : R⟦X⟧) (n : ℕ) :
    (u : R) ^ (n + 1) * betaCoeff (transformBeta (SubstGroup.scale u) β) n = betaCoeff β n := by
  rw [transformBeta_scale, betaCoeff_def, betaCoeff_def, coeff_C_mul, coeff_rescale]
  have : (u : R) ^ (n + 1) * u * (↑u⁻¹ : R) ^ (n + 2) = 1 := by
    rw [← pow_succ, ← mul_pow, Units.mul_inv, one_pow]
  linear_combination -coeff (n + 2) β * this

/-- The coupling `a = α_s / (2π)` against `a₄ = α_s / (4π)`: if `β` is the beta function of `a₄`,
the beta function of `a = 2 a₄` has the coefficients `βₙ / 2^{n+1}`; in particular `β₀` halves. -/
theorem betaCoeff_transformBeta_scale_two {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) (β : K⟦X⟧)
    (n : ℕ) :
    betaCoeff (transformBeta (SubstGroup.scale (Units.mk0 2 h2)) β) n =
      betaCoeff β n / 2 ^ (n + 1) := by
  rw [eq_div_iff (pow_ne_zero _ h2), mul_comm]
  simpa using betaCoeff_transformBeta_scale (Units.mk0 2 h2) β n

end Evolution
end Factorization
end QFT
end EpsilonEridani
