/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic

/-!
# Concrete Minkowski forms for witnesses

`Kinematics.Witness.gWit` is the `+--` Minkowski form on `ℝ × ℝ × ℝ`, one time and two space
directions, and `Kinematics.Witness.gFour` is the `+---` Minkowski form on `ℝ⁴`, one time and
three space directions, both in the `Kinematics` sign convention. They are the concrete forms
on which the DIS tensor, polarized-kinematics and jet-frame witnesses are evaluated.
-/

public section

namespace EpsilonEridani
namespace QFT
namespace Scattering
namespace DIS
namespace Kinematics

namespace Witness

/-- The `+--` Minkowski form on `ℝ × ℝ × ℝ`, one time and two space directions:
`g v w = v₀w₀ - v₁w₁ - v₂w₂`, in the `Kinematics` sign convention. Two space directions are the
fewest that leave, besides the direction of a momentum transfer, a further spatial direction;
`Tensors.Hadronic.Witness` uses it as a spectator direction. -/
noncomputable def gWit : Bilin (ℝ × ℝ × ℝ) :=
  LinearMap.mk₂ ℝ (fun v w => v.1 * w.1 - v.2.1 * w.2.1 - v.2.2 * w.2.2)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)
    (fun _ _ _ => by simp only [Prod.fst_add, Prod.snd_add]; ring)
    (fun _ _ _ => by simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring)

@[simp] lemma gWit_apply (v w : ℝ × ℝ × ℝ) :
    gWit v w = v.1 * w.1 - v.2.1 * w.2.1 - v.2.2 * w.2.2 := (rfl)

/-- `gWit` is symmetric, as a metric must be. -/
lemma gWit_isSymm : gWit.IsSymm := by
  refine { eq := ?_ }
  intro v w
  simp only [gWit_apply]
  ring

/-- The `+---` Minkowski form on `ℝ⁴`: `g v w = v₀w₀ - v₁w₁ - v₂w₂ - v₃w₃`, in the `Kinematics`
sign convention. It is the four-dimensional counterpart of `gWit`, the form on which the
parity-odd and polarized-kinematics witnesses are evaluated. -/
def gFour : Bilin (Fin 4 → ℝ) :=
  Matrix.toBilin' (Matrix.diagonal ![1, -1, -1, -1])

@[simp] lemma gFour_apply (v w : Fin 4 → ℝ) :
    gFour v w = v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3 := by
  simp only [gFour, Matrix.toBilin'_apply', dotProduct, Matrix.mulVec_diagonal,
    Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_mul,
    neg_mul, mul_neg]
  ring

/-- `gFour` is symmetric, as a metric must be. -/
lemma gFour_isSymm : gFour.IsSymm :=
  Matrix.isSymm_toBilin'_iff_isSymm.mpr (Matrix.isSymm_diagonal _)

end Witness

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
