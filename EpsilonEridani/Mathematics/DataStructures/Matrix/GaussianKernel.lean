/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.DataStructures.Matrix.PosSemidef
public import TauCeti.Analysis.Bochner.Gaussian.Basic

/-!
# The real Gaussian kernel is positive semidefinite

The real Gaussian kernel `(a, b) ↦ exp (-c ‖a - b‖²)` on a real inner-product space is positive
semidefinite for every `c ≥ 0`. It is the entrywise real part of the complex Gaussian kernel,
whose positive semidefiniteness is Tau Ceti's `TauCeti.posSemidef_cexp_neg_mul_sq_norm`
(`TauCeti/Analysis/Bochner/Gaussian/Basic.lean`), and the entrywise real part of a
positive-semidefinite matrix is positive semidefinite (`Matrix.PosSemidef.map_re`, recorded in
`EpsilonEridani/Mathematics/DataStructures/Matrix/PosSemidef.lean`). This module keeps the
lemma apart from that file so that only its consumers carry Tau Ceti's Bochner/Gaussian theory.

This is the positivity input of the dipole S-matrix of the Golec-Biernat-Wüsthoff amplitude:
`SmallX.isAdmissible_golecBiernatWusthoff`, in
`EpsilonEridani/QFT/SmallX/Dipole/Amplitude.lean`, derives the admissibility of the amplitude
from it.

## Main results

- `Matrix.posSemidef_rexp_neg_mul_sq_norm`: the real Gaussian kernel
  `(a, b) ↦ exp (-c ‖a - b‖²)` on a real inner-product space is positive semidefinite, `c ≥ 0`.
-/

public section

namespace Matrix

open scoped ComplexOrder

/-- The real Gaussian kernel `(a, b) ↦ exp (-c ‖a - b‖²)` on a real inner-product space is
positive semidefinite for every `c ≥ 0`: it is the entrywise real part of the complex Gaussian
kernel, whose positive semidefiniteness is `TauCeti.posSemidef_cexp_neg_mul_sq_norm`, and the
real part of a positive-semidefinite matrix is positive semidefinite
(`Matrix.PosSemidef.map_re`). The index space is arbitrary. -/
theorem posSemidef_rexp_neg_mul_sq_norm {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {c : ℝ} (hc : 0 ≤ c) :
    (Matrix.of fun a b : V => Real.exp (-(c * ‖a - b‖ ^ 2))).PosSemidef := by
  have hG : (Matrix.of fun a b : V => Complex.exp (-(c * ‖a - b‖ ^ 2 : ℝ))).PosSemidef :=
    TauCeti.posSemidef_cexp_neg_mul_sq_norm hc
  have e : (Matrix.of fun a b : V => Complex.exp (-(c * ‖a - b‖ ^ 2 : ℝ))).map RCLike.re =
      Matrix.of fun a b => Real.exp (-(c * ‖a - b‖ ^ 2)) := by
    ext a b
    simp only [map_apply, of_apply, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
      RCLike.re_to_complex, Complex.ofReal_re]
  exact e ▸ hG.map_re

end Matrix
