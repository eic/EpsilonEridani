/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.QFT.SmallX.Dipole.Operator

/-!
# Quadrupoles and higher Wilson-line correlators

The dipole operator `S U x y = (1 / N_c) Re Tr(U(x) U(y)†)` is the simplest member of a family
of colour-singlet Wilson-line correlators. The higher members appear as soon as an observable
involves more than one quark-antiquark pair crossing the target: the cross section for
quark-antiquark dijet production in deep-inelastic scattering at small `x` involves the
quadrupole, and the rapidity evolution of a
`2n`-point correlator involves correlators with more lines. For quark positions
`x₀, …, x_{n-1}` and antiquark positions `y₀, …, y_{n-1}` the `2n`-point correlator
of a configuration `U` is

```
(1 / N_c) Re Tr(U(x₀) U(y₀)† U(x₁) U(y₁)† ⋯ U(x_{n-1}) U(y_{n-1})†),
```

and the quadrupole is its `n = 2` member,

```
Q U x y z w = (1 / N_c) Re Tr(U(x) U(y)† U(z) U(w)†).
```

See Jalilian-Marian and Kovchegov, *Phys. Rev.* **D70** (2004) 114017, and Dominguez, Marquet,
Xiao and Yuan, *Phys. Rev.* **D83** (2011) 105005, for these correlators and the observables
that measure them. As for the dipole, everything proved here holds configuration by
configuration and uses only unitarity of the Wilson lines:

* the `n = 1` correlator is the dipole, the `n = 2` correlator is the quadrupole, and the
  correlator of pairwise coincident quark and antiquark positions is `1`;
* every correlator lies in `[-1, 1]`;
* when two neighbouring Wilson lines in the trace sit at the same transverse position they
  cancel, so each coincidence limit of the quadrupole is a dipole;
* the quadrupole is invariant under the cyclic shift of its two quark-antiquark pairs and under
  reversal of the order of its four arguments (the traced product at `w, z, y, x` is the
  Hermitian conjugate of the one at `x, y, z, w`), and under every gauge transformation whose
  values at the two ends of the light cone agree at each pair of positions whose Wilson lines
  stand next to each other in the trace.

## Main definitions

- `SmallX.multipoleS`: the `2n`-point Wilson-line correlator of a configuration.
- `SmallX.quadrupoleS`: the quadrupole operator.

## Main results

- `SmallX.multipoleS_fin_one`: the `n = 1` correlator is the dipole operator.
- `SmallX.abs_multipoleS_le_one`: the unitarity bound for every correlator.
- `SmallX.multipoleS_fin_two`: the `n = 2` correlator is the quadrupole operator.
- `SmallX.quadrupoleS_def`: the explicit trace formula for the quadrupole.
- `SmallX.quadrupoleS_self_left`, `SmallX.quadrupoleS_self_mid`, `SmallX.quadrupoleS_self_right`,
  `SmallX.quadrupoleS_self_outer`: the coincidence limits of the quadrupole.
- `SmallX.quadrupoleS_gaugeTransform`: gauge invariance of the quadrupole.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Matrix

variable {Nc : ℕ}

/-! ### The general correlator -/

/-- The `2n`-point Wilson-line correlator
`(1 / N_c) Re Tr(U(x₀) U(y₀)† ⋯ U(x_{n-1}) U(y_{n-1})†)` of a configuration `U`, for quarks at
the positions `x i` and antiquarks at the positions `y i`. The product is taken in the unitary
group, with the factor of index `0` leftmost. -/
def multipoleS (U : WilsonConfiguration Nc) {n : ℕ} (x y : Fin n → EuclideanSpace ℝ (Fin 2)) :
    ℝ :=
  (Nc : ℝ)⁻¹ *
    (trace (((List.ofFn fun i => U (x i) * star (U (y i))).prod : unitaryGroup (Fin Nc) ℂ) :
      Matrix (Fin Nc) (Fin Nc) ℂ)).re

lemma multipoleS_def (U : WilsonConfiguration Nc) {n : ℕ}
    (x y : Fin n → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U x y = (Nc : ℝ)⁻¹ *
      (trace (((List.ofFn fun i => U (x i) * star (U (y i))).prod : unitaryGroup (Fin Nc) ℂ) :
        Matrix (Fin Nc) (Fin Nc) ℂ)).re :=
  (rfl)

/-- A correlator whose quarks and antiquarks sit pairwise at the same transverse positions is
`1`: each factor `U(xᵢ) U(xᵢ)†` of the trace is the identity. This is colour transparency for
the `2n`-point correlator. -/
@[simp]
theorem multipoleS_self [NeZero Nc] (U : WilsonConfiguration Nc) {n : ℕ}
    (x : Fin n → EuclideanSpace ℝ (Fin 2)) : multipoleS U x x = 1 := by
  simp [multipoleS_def, NeZero.ne Nc]

/-- The two-point correlator is the dipole operator. -/
@[simp]
theorem multipoleS_fin_one (U : WilsonConfiguration Nc) (x y : Fin 1 → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U x y = dipoleS U (x 0) (y 0) := by
  simp [multipoleS_def, dipoleS_def]

/-- **Unitarity bound** on every Wilson-line correlator of a single configuration:
its modulus is at most one. -/
theorem abs_multipoleS_le_one (U : WilsonConfiguration Nc) {n : ℕ}
    (x y : Fin n → EuclideanSpace ℝ (Fin 2)) : |multipoleS U x y| ≤ 1 := by
  simpa [multipoleS_def] using abs_inv_card_mul_re_trace_le_one_of_mem_unitaryGroup
    (List.ofFn fun i => U (x i) * star (U (y i))).prod.2

/-! ### The quadrupole -/

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
  rw [quadrupoleS_def, quadrupoleS_def, mul_assoc _ (U z).1, mul_assoc _ (U x).1, trace_mul_comm]

/-- Coincidence limit of the quadrupole: when the first quark and the first antiquark coincide,
the quadrupole is the dipole of the second pair. -/
@[simp]
theorem quadrupoleS_self_left (U : WilsonConfiguration Nc) (x z w : EuclideanSpace ℝ (Fin 2)) :
    quadrupoleS U x x z w = dipoleS U z w := by
  simp [quadrupoleS_def, dipoleS_def, Unitary.mul_star_self_of_mem (U x).2]

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
    quadrupoleS U x y y w = dipoleS U x w := by
  simp [quadrupoleS_def, dipoleS_def, mul_assoc, Unitary.star_mul_self_of_mem (U y).2]

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
  have h : ((U w).1 * star (U z).1 * (U y).1 * star (U x).1 : Matrix (Fin Nc) (Fin Nc) ℂ) =
      ((U x).1 * star (U y).1 * (U z).1 * star (U w).1)ᴴ := by
    simp only [← star_eq_conjTranspose, star_mul, star_star, mul_assoc]
  rw [quadrupoleS_def, quadrupoleS_def, h]
  exact congrArg _ (re_trace_conjTranspose ((U x).1 * star (U y).1 * (U z).1 * star (U w).1)).symm

/-- **Gauge invariance** of the quadrupole operator: under `U(v) ↦ Ω₊(v) U(v) Ω₋(v)†`, the
quadrupole at `x, y, z, w` is unchanged as soon as `Ω₋` agrees at `x` and `y` and at `z` and
`w`, and `Ω₊` agrees at `y` and `z` and at `w` and `x`. These are the pairs of points whose
Wilson lines stand next to each other in the trace, the last pair through its cyclicity. In
particular the quadrupole is invariant under every global colour rotation `U ↦ V U W†`. -/
theorem quadrupoleS_gaugeTransform (Ωp Ωm : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) {x y z w : EuclideanSpace ℝ (Fin 2)} (hxy : Ωm x = Ωm y)
    (hyz : Ωp y = Ωp z) (hzw : Ωm z = Ωm w) (hwx : Ωp w = Ωp x) :
    quadrupoleS (WilsonConfiguration.gaugeTransform Ωp Ωm U) x y z w = quadrupoleS U x y z w := by
  have key : ((Ωp x * U x * star (Ωm x) : unitaryGroup (Fin Nc) ℂ) : Matrix (Fin Nc) (Fin Nc) ℂ) *
      star (Ωp y * U y * star (Ωm y) : unitaryGroup (Fin Nc) ℂ).1 *
      (Ωp z * U z * star (Ωm z) : unitaryGroup (Fin Nc) ℂ).1 *
      star (Ωp w * U w * star (Ωm w) : unitaryGroup (Fin Nc) ℂ).1 =
      (Ωp x).1 * ((U x).1 * star (U y).1 * (U z).1 * star (U w).1) * star (Ωp x).1 := by
    rw [hxy, ← hyz, hzw, hwx]
    simp only [Submonoid.coe_mul, Unitary.coe_star, star_mul, star_star, mul_assoc]
    simp only [← mul_assoc (star (Ωm y).1), ← mul_assoc (star (Ωp y).1),
      ← mul_assoc (star (Ωm w).1), Unitary.star_mul_self_of_mem (Ωm y).2,
      Unitary.star_mul_self_of_mem (Ωp y).2, Unitary.star_mul_self_of_mem (Ωm w).2, one_mul]
  simp only [quadrupoleS_def, WilsonConfiguration.gaugeTransform_apply, key, trace_unitary_conj]

end SmallX
end QFT
end EpsilonEridani
