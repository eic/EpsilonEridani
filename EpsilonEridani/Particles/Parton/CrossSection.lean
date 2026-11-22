/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The collinear single-scattering cross section

In collinear factorisation, the hadronic cross section for a single hard scattering is the
integral of the parton densities `f` and `f'` of the two colliding hadrons against the partonic
cross section `σ`:

`σ = ∫ f(p) f'(p') σ(p, p') dν(p) dν(p')`.

`singleScatteringCrossSection` states this for an arbitrary measure space `P` of parton labels.
For physical applications `P` is `Flavour × ℝ`, with counting measure on the flavours and
Lebesgue measure on the momentum fraction.
-/

public section

noncomputable section

open MeasureTheory

namespace EpsilonEridani
namespace Particles
namespace Parton

variable {P : Type*} [MeasurableSpace P]

/-- The collinear single-scattering cross section `∫ f(p) f'(p') σ(p, p') dν(p) dν(p')`, for
parton densities `f` and `f'` of the two hadrons and a partonic cross section `σ`. -/
def singleScatteringCrossSection (ν : Measure P) (f f' : P → ℝ) (σ : P → P → ℝ) : ℝ :=
  ∫ q : P × P, f q.1 * f' q.2 * σ q.1 q.2 ∂ν.prod ν

theorem singleScatteringCrossSection_def (ν : Measure P) (f f' : P → ℝ) (σ : P → P → ℝ) :
    singleScatteringCrossSection ν f f' σ = ∫ q : P × P, f q.1 * f' q.2 * σ q.1 q.2 ∂ν.prod ν :=
  (rfl)

end Parton
end Particles
end EpsilonEridani
