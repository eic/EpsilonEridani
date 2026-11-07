/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.SmallX.Dipole.Operator

/-!
# The quadrupole operator

The quadrupole is the four-point member `n = 2` of the `2n`-point Wilson-line correlators
`SmallX.multipoleS`: for quarks at `x`, `z` and antiquarks at `y`, `w`,

```
Q U x y z w = (1 / N_c) Re Tr(U(x) U(y)† U(z) U(w)†).
```

It is the next correlator after the dipole, and enters, for instance, the cross section for
quark-antiquark dijet production in deep-inelastic scattering at small `x` (Jalilian-Marian and
Kovchegov, *Phys. Rev.* **D70** (2004) 114017; Dominguez, Marquet, Xiao and Yuan, *Phys. Rev.*
**D83** (2011) 105005). Its properties are specialisations of those of the general correlator,
and hold configuration by configuration:

* `|Q| ≤ 1`;
* when two Wilson lines standing next to each other in the trace sit at the same transverse
  position they cancel, so each of the four coincidence limits of *adjacent* lines is a dipole.
  Coincident quark positions (`Q U x y x w`) or coincident antiquark positions (`Q U x y z y`)
  do not reduce;
* the quadrupole is invariant under the cyclic shift of its two quark-antiquark pairs and under
  reversal of the order of its four arguments (the traced product at `w, z, y, x` is the
  Hermitian conjugate of the one at `x, y, z, w`), and under every gauge transformation whose
  values at the two ends of the light cone agree at each pair of positions whose Wilson lines
  stand next to each other in the trace.

## Main definitions

- `SmallX.quadrupoleS`: the quadrupole operator.

## Main results

- `SmallX.quadrupoleS_def`: the explicit trace formula for the quadrupole.
- `SmallX.multipoleS_fin_two`: the four-point correlator is the quadrupole operator.
- `SmallX.abs_quadrupoleS_le_one`: the unitarity bound `|Q| ≤ 1`.
- `SmallX.quadrupoleS_self_left`, `SmallX.quadrupoleS_self_mid`, `SmallX.quadrupoleS_self_right`,
  `SmallX.quadrupoleS_self_outer`: the coincidence limits of the quadrupole.
- `SmallX.quadrupoleS_cycle`: invariance under the cyclic shift of the two pairs.
- `SmallX.quadrupoleS_reverse`: invariance under reversal of the order of the arguments.
- `SmallX.quadrupoleS_gaugeTransform`: gauge invariance of the quadrupole.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Matrix

variable {Nc : ℕ}

/-- The quadrupole operator `Q U x y z w = (1 / N_c) Re Tr(U(x) U(y)† U(z) U(w)†)` of a
Wilson-line configuration `U`: the four-point correlator with quarks at `x`, `z` and antiquarks
at `y`, `w`. -/
def quadrupoleS (U : WilsonConfiguration Nc) (x y z w : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  multipoleS U ![x, z] ![y, w]

/-- The quadrupole operator as an explicit normalised trace. -/
lemma quadrupoleS_def (U : WilsonConfiguration Nc) (x y z w : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x y z w = (Nc : ℝ)⁻¹ * (trace ((U x : Matrix (Fin Nc) (Fin Nc) ℂ) *
      star (U y).1 * (U z).1 * star (U w).1)).re := by
  simp [quadrupoleS, multipoleS_def, mul_assoc]

/-- The four-point correlator is the quadrupole operator. -/
@[simp]
theorem multipoleS_fin_two (U : WilsonConfiguration Nc) (x y : Fin 2 → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U x y = quadrupoleS U (x 0) (y 0) (x 1) (y 1) := by
  simp [quadrupoleS_def, multipoleS_def, mul_assoc]

/-- **Unitarity bound** on the quadrupole operator of a single configuration. -/
theorem abs_quadrupoleS_le_one (U : WilsonConfiguration Nc) (x y z w : EuclideanSpace ℝ (Fin 2)) :
    |quadrupoleS U x y z w| ≤ 1 :=
  abs_multipoleS_le_one U _ _

/-- The quadrupole is invariant under the cyclic exchange of its two quark-antiquark pairs. -/
theorem quadrupoleS_cycle (U : WilsonConfiguration Nc) (x y z w : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x y z w = quadrupoleS U z w x y := by
  rw [quadrupoleS, quadrupoleS]
  refine (multipoleS_cons_eq_snoc U x y ![z] ![w]).trans ?_
  congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- Coincidence limit of the quadrupole: when the first quark and the first antiquark coincide,
the quadrupole is the dipole of the second pair. -/
@[simp]
theorem quadrupoleS_self_left (U : WilsonConfiguration Nc) (x z w : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x x z w = dipoleS U z w :=
  (multipoleS_cons_self_left U x ![z] ![w]).trans (multipoleS_fin_one U _ _)

/-- Coincidence limit of the quadrupole: when the second quark and the second antiquark
coincide, the quadrupole is the dipole of the first pair. -/
@[simp]
theorem quadrupoleS_self_right (U : WilsonConfiguration Nc) (x y z : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x y z z = dipoleS U x y :=
  (quadrupoleS_cycle U x y z z).trans (quadrupoleS_self_left U z x y)

/-- Coincidence limit of the quadrupole: when the first antiquark and the second quark
coincide, the lines `U(y)† U(y)` cancel and the quadrupole is the dipole `S U x w`. -/
@[simp]
theorem quadrupoleS_self_mid (U : WilsonConfiguration Nc) (x y w : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x y y w = dipoleS U x w :=
  (multipoleS_cons_self_mid U x y w ![] ![]).trans (multipoleS_fin_one U _ _)

/-- Coincidence limit of the quadrupole: when the second antiquark and the first quark
coincide, the lines `U(x)† U(x)`, adjacent through the cyclicity of the trace, cancel and the
quadrupole is the dipole `S U z y`. -/
@[simp]
theorem quadrupoleS_self_outer (U : WilsonConfiguration Nc) (x y z : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x y z x = dipoleS U z y :=
  (quadrupoleS_cycle U x y z x).trans (quadrupoleS_self_mid U z x y)

/-- The quadrupole is invariant under reversal of the order of its four arguments, which
exchanges the roles of quarks and antiquarks: `Q U x y z w = Q U w z y x`. The traced product
`U(w) U(z)† U(y) U(x)†` at `w, z, y, x` is the Hermitian conjugate of the one at `x, y, z, w`,
so their traces have the same real part. -/
theorem quadrupoleS_reverse (U : WilsonConfiguration Nc) (x y z w : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x y z w = quadrupoleS U w z y x := by
  rw [quadrupoleS, quadrupoleS, multipoleS_reverse]
  congr 1 <;> funext i <;> fin_cases i <;> rfl

/-- **Gauge invariance** of the quadrupole operator: under `U(v) ↦ Ω₊(v) U(v) Ω₋(v)†`, the
quadrupole at `x, y, z, w` is unchanged as soon as `Ω₋` agrees at `x` and `y` and at `z` and
`w`, and `Ω₊` agrees at `y` and `z` and at `w` and `x`. These are the pairs of points whose
Wilson lines stand next to each other in the trace, the last pair through its cyclicity. In
particular the quadrupole is invariant under every global colour rotation `U ↦ V U W†`. -/
theorem quadrupoleS_gaugeTransform (Ωp Ωm : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) {x y z w : EuclideanSpace ℝ (Fin 2)} (hxy : Ωm x = Ωm y)
    (hyz : Ωp y = Ωp z) (hzw : Ωm z = Ωm w) (hwx : Ωp w = Ωp x) :
    quadrupoleS (WilsonConfiguration.gaugeTransform Ωp Ωm U) x y z w = quadrupoleS U x y z w :=
  multipoleS_gaugeTransform Ωp Ωm U (Fin.forall_fin_two.mpr ⟨hxy, hzw⟩)
    (Fin.forall_fin_two.mpr ⟨hyz, hwx⟩)

end SmallX
end QFT
end EpsilonEridani
