/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.Jets.Frame.Basic
public import EpsilonEridani.QFT.Scattering.DIS.Tensors.Basic

/-!
# A witness for reference frames

The `+--` Minkowski form `gWit` on `ℝ × ℝ × ℝ`, already used as the DIS tensor witness, carries
the rest frame `n = (1, 0, 0)`. In it the energy of `p` is its time component, and two
back-to-back photons have opening angle `π`.

## Main statements

* `Frame.Witness.cosAngle_backToBack_restFrameWit_eq_neg_one`: in the rest frame of the `+--`
  Minkowski form, two back-to-back photons have `cos θ = -1`.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace Jets
namespace Frame
namespace Witness

open EpsilonEridani.QFT.Scattering.DIS.Tensors.Hadronic.Witness (gWit gWit_isSymm)

/-- The rest frame `n = (1, 0, 0)` of the Minkowski form `gWit`. -/
def restFrameWit : Frame gWit where
  n := (1, 0, 0)
  timelike := by norm_num

/-- In the rest frame the energy of a momentum is its time component. -/
@[simp]
theorem energy_restFrameWit_apply (p : ℝ × ℝ × ℝ) : restFrameWit.energy p = p.1 := by
  simp [energy_apply, restFrameWit]

/-- Two back-to-back photons, `(1, 1, 0)` and `(1, -1, 0)`, have `cos θ = -1` in the rest
frame. -/
theorem cosAngle_backToBack_restFrameWit_eq_neg_one :
    restFrameWit.cosAngle ((1, 1, 0) : ℝ × ℝ × ℝ) (1, -1, 0) = -1 := by
  have h := restFrameWit.one_sub_cosAngle_of_massless gWit_isSymm
    (a := ((1, 1, 0) : ℝ × ℝ × ℝ)) (b := (1, -1, 0)) (by norm_num) (by norm_num)
    (by norm_num [energy_restFrameWit_apply]) (by norm_num [energy_restFrameWit_apply])
  rw [energy_restFrameWit_apply, energy_restFrameWit_apply] at h
  norm_num at h
  linarith

end Witness
end Frame
end Jets
end QFT
end EpsilonEridani
