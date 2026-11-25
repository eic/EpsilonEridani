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

* `momentF_f2LO_pow`: for integrable moment integrands, `∫₀¹ xⁿ F₂ = Σᵢ eᵢ² ∫₀¹ x^(n+1) qᵢ`, the
  structure-function moment as a charge-weighted sum of `PDF.mellinMoment`s.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Inclusive

open Particles.Parton.PDF (Pdf mellinMoment mellinMoment_eq_intervalIntegral)

/-- **The weighted moment of a structure function**, `∫₀¹ dx w(x) F(x, Q²)`, at the scale `Q2`.
It is the interval integral, so it is `0` when the integrand is not integrable; the statements
using it carry the integrability they need as hypotheses. -/
def momentF (F : ℝ → ℝ → ℝ) (w : ℝ → ℝ) (Q2 : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, w x * F x Q2

theorem momentF_def (F : ℝ → ℝ → ℝ) (w : ℝ → ℝ) (Q2 : ℝ) :
    momentF F w Q2 = ∫ x in (0 : ℝ)..1, w x * F x Q2 :=
  (rfl)

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

end Inclusive
end DIS
end Scattering
end QFT
end EpsilonEridani
