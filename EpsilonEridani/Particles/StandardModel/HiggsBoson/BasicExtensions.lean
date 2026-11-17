/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck, The EpsilonEridani contributors
-/
module

public import Physlib.Particles.StandardModel.HiggsBoson.Basic

/-!
# Extensions of the Higgs doublet

This file extends `Physlib.Particles.StandardModel.HiggsBoson.Basic` with the Higgs vacuum
`(0, v)`, the vacuum direction used for electroweak symmetry breaking.

## Main definitions

* `higgsVacuum`: the Higgs vector `(0, v)`, with the vacuum value in the lower component.
-/

public section

open StandardModel

namespace EpsilonEridani.Particles.StandardModel.HiggsBoson

/-- The Higgs vacuum `(0, v)`, in the lower (`T³ = -1/2`) component of the hypercharge-`1` Higgs
doublet. With `Q = T³ + Y / 2` this is the neutral component. Physlib's `HiggsVec.ofReal a` is
`!₂[√a, 0]` and uses the upper component instead. -/
def higgsVacuum (v : ℂ) : HiggsVec := !₂[0, v]

/-- The Higgs vacuum in components. -/
theorem ofLp_higgsVacuum (v : ℂ) : (higgsVacuum v).ofLp = ![0, v] :=
  WithLp.ofLp_toLp _ _

end EpsilonEridani.Particles.StandardModel.HiggsBoson

end
