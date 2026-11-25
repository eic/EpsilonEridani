/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Particles.Parton.PDF.Basic
public import EpsilonEridani.QFT.Scattering.DIS.CrossSection

/-!
# Weighted moments of a structure function

The sum rules of inclusive DIS are statements about weighted integrals over the Bjorken variable,

  `momentF F w Q² = ∫₀¹ dx w(x) F(x, Q²)`,

of a structure function `F`. The weights that occur are `x^(N-2)` for the moments of `F₂` that
the operator-product expansion organises, `x^(N-1)` for those of `F₃`, and `1/x` for the Adler
and the Gottfried sum rules. No integrability is built into `momentF`: it is the interval
integral, and a statement that needs the integrand to be integrable says so as a hypothesis.

In the parton model, `F₂ = x Σᵢ eᵢ² qᵢ` (`DIS.f2LO`), so the `x^n`-weighted moment of `F₂` is the
charge-weighted sum of the `(n + 1)`-th Mellin moments of the densities (`momentF_f2LO_pow`):
each sum rule has a structure-function form and a density form, and they are the same statement.

## Main definitions

* `momentF`: the weighted moment `∫₀¹ w F` of a structure function at a scale.

## Main statements

* `momentF_congr`, `momentF_const_mul`, `momentF_add`, `momentF_sub`: the weighted moment is
  determined by its integrand on `(0, 1]` and is linear under integrability.
* `momentF_f2LO_pow`: for integrable moment integrands, `∫₀¹ xⁿ F₂ = Σᵢ eᵢ² ∫₀¹ x^(n+1) qᵢ`, the
  structure-function moment as a charge-weighted sum of `PDF.mellinMoment`s, and
  `momentF_f2LO_pow_of_regularity`: the same for a regular density.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Inclusive

open Particles.Parton.PDF (Pdf Regularity mellinMoment mellinMoment_eq_intervalIntegral)

/-- **The weighted moment of a structure function**, `∫₀¹ dx w(x) F(x, Q²)`, at the scale `Q2`.
It is the interval integral, so it is `0` when the integrand is not integrable; the statements
using it carry the integrability they need as hypotheses. -/
def momentF (F : ℝ → ℝ → ℝ) (w : ℝ → ℝ) (Q2 : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, w x * F x Q2

theorem momentF_def (F : ℝ → ℝ → ℝ) (w : ℝ → ℝ) (Q2 : ℝ) :
    momentF F w Q2 = ∫ x in (0 : ℝ)..1, w x * F x Q2 :=
  (rfl)

/-- Two weighted moments agree when their weighted integrands agree on `(0, 1]`: the point `0`,
where a `1/x` weight is singular, does not matter. -/
theorem momentF_congr {F G : ℝ → ℝ → ℝ} {w v : ℝ → ℝ} {Q2 : ℝ}
    (h : ∀ x ∈ Set.Ioc (0 : ℝ) 1, w x * F x Q2 = v x * G x Q2) :
    momentF F w Q2 = momentF G v Q2 :=
  intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun x hx =>
    h x (by rwa [Set.uIoc_of_le zero_le_one] at hx))

/-- A constant factor of the structure function comes out of its weighted moment. -/
theorem momentF_const_mul (c : ℝ) (F : ℝ → ℝ → ℝ) (w : ℝ → ℝ) (Q2 : ℝ) :
    momentF (fun x Q2 => c * F x Q2) w Q2 = c * momentF F w Q2 := by
  simp only [momentF_def, ← intervalIntegral.integral_const_mul, mul_left_comm]

/-- The weighted moment of a sum is the sum of the weighted moments, when both weighted
integrands are integrable on the unit interval. -/
theorem momentF_add {F G : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {Q2 : ℝ}
    (hF : IntervalIntegrable (fun x => w x * F x Q2) MeasureTheory.volume 0 1)
    (hG : IntervalIntegrable (fun x => w x * G x Q2) MeasureTheory.volume 0 1) :
    momentF (fun x Q2 => F x Q2 + G x Q2) w Q2 = momentF F w Q2 + momentF G w Q2 := by
  simp only [momentF_def, mul_add]
  exact intervalIntegral.integral_add hF hG

/-- The weighted moment of a difference is the difference of the weighted moments, when both
weighted integrands are integrable on the unit interval. -/
theorem momentF_sub {F G : ℝ → ℝ → ℝ} {w : ℝ → ℝ} {Q2 : ℝ}
    (hF : IntervalIntegrable (fun x => w x * F x Q2) MeasureTheory.volume 0 1)
    (hG : IntervalIntegrable (fun x => w x * G x Q2) MeasureTheory.volume 0 1) :
    momentF (fun x Q2 => F x Q2 - G x Q2) w Q2 = momentF F w Q2 - momentF G w Q2 := by
  simp only [momentF_def, mul_sub]
  exact intervalIntegral.integral_sub hF hG

/-- **The moments of `F₂` are the Mellin moments of the densities.** For the quark charges `e`
and a density `q` whose `(n + 1)`-th moment integrands are integrable on the unit interval (every
regular density, by `PDF.Regularity.momentIntegrable`), the `xⁿ`-weighted moment of the
leading-order `F₂ = x Σᵢ eᵢ² qᵢ` is `Σᵢ eᵢ² ∫₀¹ x^(n+1) qᵢ`. -/
theorem momentF_f2LO_pow {ι : Type} [Fintype ι] {q : Pdf ι} {n : ℕ} {Q2 : ℝ}
    (h : ∀ i, IntervalIntegrable (fun x => x ^ (n + 1) * q i x Q2) MeasureTheory.volume 0 1)
    (e : ι → ℝ) :
    momentF (f2LO e q) (fun x => x ^ n) Q2 = ∑ i, e i ^ 2 * mellinMoment q (n + 1) i Q2 := by
  simp only [momentF_def, mellinMoment_eq_intervalIntegral, ← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_finsetSum fun i _ => (h i).const_mul _]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [f2LO_def, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `momentF_f2LO_pow` for a regular density, whose moment integrands are all integrable. -/
theorem momentF_f2LO_pow_of_regularity {ι : Type} [Fintype ι] {q : Pdf ι} (h : Regularity q)
    (e : ι → ℝ) (n : ℕ) (Q2 : ℝ) :
    momentF (f2LO e q) (fun x => x ^ n) Q2 = ∑ i, e i ^ 2 * mellinMoment q (n + 1) i Q2 :=
  momentF_f2LO_pow (fun i => h.momentIntervalIntegrable (n + 1) i Q2 0 1) e

end Inclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
