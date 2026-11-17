/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.QCD.AdjointRepresentation
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Light-cone Wilson-line configurations

At high energy a target is probed through the eikonal phases picked up by fast partons crossing
it. A quark at transverse position `x` crossing the target along the light cone acquires the
fundamental Wilson line

```
U(x) = P exp( i g ∫_{-∞}^{+∞} dx⁺ A⁻ᵃ(x⁺, x) tᵃ ),
```

where `tᵃ` are the fundamental generators of `SU(N_c)` and the path ordering `P` places larger
values of the light-cone time `x⁺` to the left. An antiquark at `y` acquires `U(y)†`. See
Kovchegov and Levin, *Quantum Chromodynamics at High Energy*, CUP 2012, for this description of
a high-energy target. The ordering is fixed here once, for every Wilson-line correlator built
from these configurations.

This file fixes the representation of such a target used by the colour-dipole description of
small-`x` scattering. A `WilsonConfiguration N_c` is a map from the transverse plane to the
unitary group `U(N_c)`. The path-ordered exponential is not constructed: every property of the
dipole and higher Wilson-line correlators used downstream follows from unitarity of `U(x)` and
from its gauge transformation law, which are the two pieces of structure recorded here.

* Under a gauge transformation `Ω(x⁺, x)`, the line from `x⁺ = -∞` to `x⁺ = +∞` transforms as
  `U(x) ↦ Ω(+∞, x) U(x) Ω(-∞, x)†`. `WilsonConfiguration.gaugeTransform Ω₊ Ω₋ U` is this action,
  with `Ω₊` and `Ω₋` the gauge transformation at the two ends of the light cone; it is a left
  action of pairs of unitary-valued maps.
* The adjoint (gluon) Wilson line is defined from the fundamental one,
  `Uᵃᵇ_adj(x) = 2 Re Tr(tᵃ U(x) tᵇ U(x)†)`, through the adjoint representation
  `EpsilonEridani.QFT.QCD.RepresentationColor.SUNGen.adjointHom`; it is real orthogonal.

Every entry of `U(x)` has modulus at most one by `entry_norm_bound_of_unitary`.

## Main definitions

- `SmallX.WilsonConfiguration`: a map from the transverse plane to `U(N_c)`.
- `SmallX.WilsonConfiguration.gaugeTransform`: the action `U(x) ↦ Ω₊(x) U(x) Ω₋(x)†`.
- `SmallX.WilsonConfiguration.adjointLine`: the adjoint Wilson line, valued in the orthogonal
  group on the adjoint index set.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Matrix QCD.RepresentationColor

/-- A light-cone Wilson-line configuration of a target: a unitary `N_c × N_c` matrix at each
point of the transverse plane, understood as the fundamental Wilson line crossing the target
at that transverse position. -/
abbrev WilsonConfiguration (Nc : ℕ) : Type :=
  EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ

namespace WilsonConfiguration

variable {Nc : ℕ}

/-- The gauge transformation of a Wilson-line configuration, `U(x) ↦ Ω₊(x) U(x) Ω₋(x)†`, where
`Ω₊` and `Ω₋` are the gauge transformation at light-cone times `x⁺ = +∞` and `x⁺ = -∞`. -/
def gaugeTransform (Ωp Ωm : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) : WilsonConfiguration Nc :=
  fun x => Ωp x * U x * star (Ωm x)

@[simp]
lemma gaugeTransform_apply (Ωp Ωm : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) (x : EuclideanSpace ℝ (Fin 2)) :
    gaugeTransform Ωp Ωm U x = Ωp x * U x * star (Ωm x) :=
  (rfl)

/-- The trivial gauge transformation acts trivially. -/
@[simp]
lemma gaugeTransform_one (U : WilsonConfiguration Nc) : gaugeTransform 1 1 U = U := by
  ext1 x
  simp

/-- Gauge transformations compose: performing `(Ω₊, Ω₋)` and then `(Ω₊', Ω₋')` is the gauge
transformation `(Ω₊' Ω₊, Ω₋' Ω₋)`. -/
@[simp]
lemma gaugeTransform_gaugeTransform
    (Ωp Ωm Ωp' Ωm' : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) :
    gaugeTransform Ωp' Ωm' (gaugeTransform Ωp Ωm U) = gaugeTransform (Ωp' * Ωp) (Ωm' * Ωm) U := by
  ext1 x
  simp only [gaugeTransform_apply, Pi.mul_apply, star_mul, mul_assoc]

/-- The adjoint Wilson line at `x`, `Uᵃᵇ_adj(x) = 2 Re Tr(tᵃ U(x) tᵇ U(x)†)`, as an element of
the orthogonal group on the adjoint index set of `su(N_c)`. -/
def adjointLine (U : WilsonConfiguration Nc) (x : EuclideanSpace ℝ (Fin 2)) :
    orthogonalGroup (SUNGen.SUNIndex Nc) ℝ :=
  SUNGen.adjointHom (U x)

@[simp]
lemma adjointLine_apply (U : WilsonConfiguration Nc) (x : EuclideanSpace ℝ (Fin 2)) :
    U.adjointLine x = SUNGen.adjointHom (U x) :=
  (rfl)

/-- The adjoint Wilson line of a gauge-transformed configuration,
`U_adj(x) ↦ Ω₊_adj(x) U_adj(x) Ω₋_adj(x)ᵀ`. -/
lemma adjointLine_gaugeTransform (Ωp Ωm : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) (x : EuclideanSpace ℝ (Fin 2)) :
    (gaugeTransform Ωp Ωm U).adjointLine x =
      SUNGen.adjointHom (Ωp x) * U.adjointLine x * star (SUNGen.adjointHom (Ωm x)) := by
  simp only [adjointLine_apply, gaugeTransform_apply, map_mul, Unitary.star_eq_inv, map_inv]

end WilsonConfiguration

end SmallX
end QFT
end EpsilonEridani
