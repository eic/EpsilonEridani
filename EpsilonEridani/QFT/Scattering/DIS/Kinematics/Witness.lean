/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith, Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Scattering.DIS.Kinematics.Basic

/-!
# A concrete Minkowski form for witnesses

`Kinematics.Witness.gWit` is the `+--` Minkowski form on `ℝ × ℝ × ℝ`, one time and two space
directions, in the `Kinematics` sign convention. It is the concrete form on which the DIS tensor,
polarized-kinematics and jet-frame witnesses are evaluated.
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

end Witness

end Kinematics
end DIS
end Scattering
end QFT
end EpsilonEridani
