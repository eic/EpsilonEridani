/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Fourier.AddCircle

/-!
# The Fourier monomials on the circle as a character and as random variables

Extensions of `Mathlib.Analysis.Fourier.AddCircle`: the Fourier monomial `fourier n` is a
character of the circle in its argument (`fourier_apply_add`), and, being bounded by `1`, it is
integrable against any finite measure when composed with an almost everywhere measurable angle
(`integrable_fourier_comp`, `integrable_fourier_mul_conj_fourier`).
-/

public section

open MeasureTheory AddCircle
open scoped ComplexConjugate

namespace EpsilonEridani

variable {T : ℝ}

/-- The Fourier monomial is a character of the circle: `e^{i n (x + y)} = e^{i n x} e^{i n y}`. -/
theorem fourier_apply_add (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, toCircle_add, Circle.coe_mul]

/-- The Fourier monomial satisfies `fourier n (x - y) = fourier n x * conj (fourier n y)`. -/
theorem fourier_apply_sub (n : ℤ) (x y : AddCircle T) :
    fourier n (x - y) = fourier n x * conj (fourier n y) := by
  rw [fourier_apply, fourier_apply, fourier_apply, smul_sub, sub_eq_add_neg, toCircle_add,
    toCircle_neg, Circle.coe_mul, Circle.coe_inv_eq_conj]

/-- Every Fourier monomial has norm `1`. -/
theorem norm_fourier (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  rw [fourier_apply, Circle.norm_coe]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- The harmonic `e^{i n X}` of an almost everywhere measurable angle `X` is integrable. -/
theorem integrable_fourier_comp {X : Ω → AddCircle T} (hX : AEMeasurable X P) (n : ℤ) :
    Integrable (fun ω => fourier n (X ω)) P :=
  .of_bound ((fourier n).continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by simp)

/-- The pair harmonic `e^{i n X} conj (e^{i n Y})` of two almost everywhere measurable angles is
integrable. -/
theorem integrable_fourier_mul_conj_fourier {X Y : Ω → AddCircle T} (hX : AEMeasurable X P)
    (hY : AEMeasurable Y P) (n : ℤ) :
    Integrable (fun ω => fourier n (X ω) * conj (fourier n (Y ω))) P := by
  have : (fun ω => fourier n (X ω) * conj (fourier n (Y ω))) =
      (fun ω => fourier n ((X - Y) ω)) := by
    ext ω
    simpa [Pi.sub_apply] using (fourier_apply_sub n (X ω) (Y ω)).symm
  rw [this]
  exact integrable_fourier_comp (AEMeasurable.sub hX hY) n

end EpsilonEridani
