/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Fourier.AddCircle

/-!
# The Fourier monomials on the circle as a character and as random variables

Extensions of `Mathlib.Analysis.Fourier.AddCircle` and of `TauCeti.Analysis.Fourier.AddCircle`:
the Fourier monomial `fourier n`, with the normalisation of the bundled additive character
`TauCeti.fourierAddChar`, is a character of the circle in its argument (`fourier_eval_add`,
`fourier_eval_sub`), and, having modulus `1` (`norm_fourier_eval`), it is integrable against any
finite measure when composed with an almost everywhere measurable angle
(`integrable_fourier_comp`, `integrable_fourier_mul_conj_fourier`).

The docstrings below write the monomial as `e^{i n x}`: this abbreviates `fourier n x`, which
Mathlib defines (`fourier_coe_apply`) as `e^{2 π i n x / T}` for an arbitrary period `T`, so the
two readings coincide only in the physical case `T = 2π`.
-/

public section

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace EpsilonEridani

variable {T : ℝ}

/-- The Fourier monomial is a character of the circle: `e^{i n (x + y)} = e^{i n x} e^{i n y}`. -/
theorem fourier_eval_add (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [← TauCeti.fourierAddChar_apply, AddChar.map_add_eq_mul]

/-- The Fourier monomial turns a difference into a product with a conjugate:
`e^{i n (x - y)} = e^{i n x} conj (e^{i n y})`. -/
theorem fourier_eval_sub (n : ℤ) (x y : AddCircle T) :
    fourier n (x - y) = fourier n x * conj (fourier n y) := by
  rw [sub_eq_add_neg, fourier_eval_add]
  simp only [fourier_apply, zsmul_neg, fourier_neg']

/-- The Fourier monomial takes values of modulus `1`: `‖e^{i n x}‖ = 1`. -/
theorem norm_fourier_eval (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

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
