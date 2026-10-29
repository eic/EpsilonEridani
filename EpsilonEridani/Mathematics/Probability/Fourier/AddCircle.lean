/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Analysis.Fourier.AddCircle
public import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.HasLaw

/-!
# The Fourier monomials of random angles

The Fourier monomial `fourier n` composed with a random angle on the circle: having modulus `1`
(`norm_fourier_eval`), it is integrable against any finite measure when composed with an almost
everywhere measurable angle (`integrable_fourier_comp`, `integrable_fourier_mul_conj_fourier`).
For two independent angles the expectation of the pair harmonic `e^{i n X} conj (e^{i n Y})`
factorises into the Fourier moments of their laws (`integral_fourier_mul_conj_fourier`).

The docstrings below write the monomial as `e^{i n x}`: this abbreviates `fourier n x`, which
Mathlib defines (`fourier_coe_apply`) as `e^{2 π i n x / T}` for an arbitrary period `T`, so the
two readings coincide only in the physical case `T = 2π`.
-/

public section

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace EpsilonEridani

variable {T : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- For two independent angles `X` and `Y` with laws `μ` and `ν`, the expectation of the pair
harmonic `e^{i n X} conj (e^{i n Y}) = e^{i n (X - Y)}` is the product of the Fourier moment
`∫ e^{i n x} dμ` with the conjugate of `∫ e^{i n x} dν`. -/
theorem integral_fourier_mul_conj_fourier {μ ν : Measure (AddCircle T)} {X Y : Ω → AddCircle T}
    (hXY : ProbabilityTheory.IndepFun X Y P) (hX : ProbabilityTheory.HasLaw X μ P)
    (hY : ProbabilityTheory.HasLaw Y ν P) (n : ℤ) :
    ∫ ω, fourier n (X ω) * conj (fourier n (Y ω)) ∂P =
      (∫ x, fourier n x ∂μ) * conj (∫ x, fourier n x ∂ν) := by
  rw [hXY.integral_fun_comp_mul_comp (f := fun x => fourier n x)
      (g := fun y => conj (fourier n y)) hX.aemeasurable hY.aemeasurable
      (fourier n).continuous.aestronglyMeasurable
      (Complex.continuous_conj.comp (fourier n).continuous).aestronglyMeasurable, integral_conj]
  exact congrArg₂ (fun a b => a * conj b)
    (hX.integral_comp (fourier n).continuous.aestronglyMeasurable)
    (hY.integral_comp (fourier n).continuous.aestronglyMeasurable)

variable [IsFiniteMeasure P]

/-- The harmonic `e^{i n X}` of an almost everywhere measurable angle `X` is integrable. -/
@[fun_prop]
theorem integrable_fourier_comp {X : Ω → AddCircle T} (hX : AEMeasurable X P) (n : ℤ) :
    Integrable (fun ω => fourier n (X ω)) P :=
  .of_bound ((fourier n).continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => (norm_fourier_eval n (X ω)).le)

/-- The pair harmonic `e^{i n X} conj (e^{i n Y})` of two almost everywhere measurable angles is
integrable. -/
@[fun_prop]
theorem integrable_fourier_mul_conj_fourier {X Y : Ω → AddCircle T} (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) (n : ℤ) :
    Integrable (fun ω => fourier n (X ω) * conj (fourier n (Y ω))) P := by
  simpa only [Pi.sub_apply, fourier_eval_sub] using integrable_fourier_comp (hX.sub hY) n

end EpsilonEridani
