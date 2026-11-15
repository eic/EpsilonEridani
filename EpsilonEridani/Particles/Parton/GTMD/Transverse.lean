/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

# The transverse plane

This module defines the transverse plane `Transverse = EuclideanSpace ℝ (Fin 2)` of the
light-front frame, in which transverse momenta and transverse positions are genuine
two-vectors rather than non-negative reals standing for a magnitude.

## Main definitions

* `Transverse`: the two-dimensional transverse plane.
-/
@[expose] public section

namespace EpsilonEridani
namespace Particles
namespace Parton
namespace GTMD

/-- The two-dimensional transverse plane of the light-front frame. -/
abbrev Transverse : Type := EuclideanSpace ℝ (Fin 2)

end GTMD
end Parton
end Particles
end EpsilonEridani
