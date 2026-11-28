/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Physlib.Relativity.Fermions.Dirac.GammaMatrices

/-!
# Extensions of Clifford multiplication on Dirac spinors

Three consequences of Physlib's Clifford relation `Fermion.Dirac.gammaMatrix_anticomm`,
`/v /w + /w /v = 2 (v · w)`, where `/v` is `Fermion.Dirac.gammaMatrix v`:

* Clifford multiplication by Minkowski-orthogonal vectors anticommutes,
  `v · w = 0 → /v /w = -(/w /v)`
  (`gammaMatrix_mul_gammaMatrix_eq_neg_mul_of_minkowskiProduct_eq_zero`);
* Clifford multiplication by a null vector squares to zero, `v · v = 0 → /v /v = 0`
  (`gammaMatrix_mul_self_eq_zero_of_minkowskiProduct_self_eq_zero`);
* the Dirac operator factorises the Klein–Gordon operator, `(/v + m)(/v - m) = v · v - m²`
  (`gammaMatrix_add_smul_one_mul_gammaMatrix_sub_smul_one`).
-/

public section

namespace Fermion.Dirac

open scoped Lorentz.Vector

/-- Clifford multiplication by Minkowski-orthogonal vectors anticommutes. -/
theorem gammaMatrix_mul_gammaMatrix_eq_neg_mul_of_minkowskiProduct_eq_zero
    {v w : Lorentz.Vector} (h : ⟪v, w⟫ₘ = 0) :
    gammaMatrix v * gammaMatrix w = -(gammaMatrix w * gammaMatrix v) :=
  eq_neg_of_add_eq_zero_left (by simp [gammaMatrix_anticomm, h])

/-- Clifford multiplication by a null vector squares to zero. -/
theorem gammaMatrix_mul_self_eq_zero_of_minkowskiProduct_self_eq_zero {v : Lorentz.Vector}
    (h : ⟪v, v⟫ₘ = 0) : gammaMatrix v * gammaMatrix v = 0 := by
  simp [gammaMatrix_mul_self, h]

/-- The Dirac operator factorises the Klein–Gordon operator, `(/v + m)(/v - m) = v · v - m²`. -/
theorem gammaMatrix_add_smul_one_mul_gammaMatrix_sub_smul_one (v : Lorentz.Vector) (m : ℝ) :
    (gammaMatrix v + m • 1) * (gammaMatrix v - m • 1) =
      (⟪v, v⟫ₘ - m ^ 2) • (1 : Module.End ℂ Dirac) := by
  simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    gammaMatrix_mul_self]
  module

end Fermion.Dirac
