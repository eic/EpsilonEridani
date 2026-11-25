/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import TauCeti.Analysis.Fourier.AddCircle

/-!
# The Fourier monomials on the circle as a character

Extensions of `Mathlib.Analysis.Fourier.AddCircle` and of `TauCeti.Analysis.Fourier.AddCircle`:
the Fourier monomial `fourier n`, with the normalisation of the bundled additive character
`TauCeti.fourierAddChar`, is a character of the circle in its argument (`fourier_eval_add`,
`fourier_eval_sub`) and has modulus `1` (`norm_fourier_eval`).

The docstrings below write the monomial as `e^{i n x}`: this abbreviates `fourier n x`, which
Mathlib defines (`fourier_coe_apply`) as `e^{2 π i n x / T}` for an arbitrary period `T`, so the
two readings coincide only in the physical case `T = 2π`.
-/

public section

open AddCircle
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

end EpsilonEridani
