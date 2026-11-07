/-
Copyright (c) 2026 Wouter Deconinck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Deconinck
-/
module

public import EpsilonEridani.Mathematics.Algebra.BigOperators.Group.List.Basic
public import EpsilonEridani.Mathematics.DataStructures.Matrix.UnitaryTrace
public import EpsilonEridani.QFT.SmallX.Dipole.WilsonLine

/-!
# Higher Wilson-line correlators

A colour-singlet state of `n` quark-antiquark pairs crossing a target described by the
Wilson-line configuration `U` is probed through the `2n`-point Wilson-line correlator. For quark
positions `x₀, …, x_{n-1}` and antiquark positions `y₀, …, y_{n-1}` it is

```
(1 / N_c) Re Tr(U(x₀) U(y₀)† U(x₁) U(y₁)† ⋯ U(x_{n-1}) U(y_{n-1})†).
```

Its `n = 1` member is the dipole operator and its `n = 2` member is the quadrupole; both are
defined downstream as specialisations of the general correlator. Higher members appear as soon as
an observable involves more than one quark-antiquark pair, and the rapidity evolution of a
`2n`-point correlator involves correlators with more lines. See Jalilian-Marian and Kovchegov,
*Phys. Rev.* **D70** (2004) 114017, and Dominguez, Marquet, Xiao and Yuan, *Phys. Rev.* **D83**
(2011) 105005, for these correlators and the observables that measure them.

Everything proved here holds configuration by configuration and uses only unitarity of the
Wilson lines:

* the correlator of pairwise coincident quark and antiquark positions is `1`, and so is the
  correlator with no lines;
* every correlator lies in `[-1, 1]`;
* when two Wilson lines standing next to each other in the trace sit at the same transverse
  position they cancel, which turns the `2(n + 1)`-point correlator into a `2n`-point one;
* the correlator is invariant under the cyclic shift of its quark-antiquark pairs, and under
  reversal of the order of all its arguments, which exchanges quarks and antiquarks (the
  reversed traced product is the Hermitian conjugate of the original one);
* the correlator is invariant under every gauge transformation whose values at the two ends of
  the light cone agree at each pair of positions whose Wilson lines stand next to each other in
  the trace, the last antiquark and the first quark being next to each other through the
  cyclicity of the trace.

## Main definitions

- `SmallX.multipoleS`: the `2n`-point Wilson-line correlator of a configuration.

## Main results

- `SmallX.multipoleS_self`: colour transparency, pairwise coincident endpoints give `1`.
- `SmallX.multipoleS_fin_zero`: the correlator with no lines is `1`.
- `SmallX.abs_multipoleS_le_one`: the unitarity bound.
- `SmallX.multipoleS_cons_self_left`, `SmallX.multipoleS_cons_self_mid`: cancellation of two
  adjacent coincident Wilson lines.
- `SmallX.multipoleS_cons_eq_snoc`: invariance under the cyclic shift of the pairs.
- `SmallX.multipoleS_reverse`: invariance under reversal of the order of the arguments.
- `SmallX.multipoleS_gaugeTransform`: gauge invariance.
-/

public section

noncomputable section

namespace EpsilonEridani
namespace QFT
namespace SmallX

open Matrix

variable {Nc : ℕ}

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

/-- The correlator with no Wilson lines is `1`, the normalised trace of the identity. -/
@[simp]
theorem multipoleS_fin_zero [NeZero Nc] (U : WilsonConfiguration Nc)
    (x y : Fin 0 → EuclideanSpace ℝ (Fin 2)) : multipoleS U x y = 1 := by
  simp [multipoleS_def, NeZero.ne Nc]

/-- **Unitarity bound** on every Wilson-line correlator of a single configuration:
its modulus is at most one. -/
theorem abs_multipoleS_le_one (U : WilsonConfiguration Nc) {n : ℕ}
    (x y : Fin n → EuclideanSpace ℝ (Fin 2)) : |multipoleS U x y| ≤ 1 := by
  simpa [multipoleS_def] using abs_inv_card_mul_re_trace_le_one_of_mem_unitaryGroup
    (List.ofFn fun i => U (x i) * star (U (y i))).prod.2

/-- Coincidence limit: when the first quark and the first antiquark sit at the same position,
their Wilson lines cancel and the `2(n + 1)`-point correlator is the `2n`-point correlator of the
remaining pairs. -/
@[simp]
theorem multipoleS_cons_self_left (U : WilsonConfiguration Nc) {n : ℕ}
    (x₀ : EuclideanSpace ℝ (Fin 2)) (x y : Fin n → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U (Fin.cons x₀ x) (Fin.cons x₀ y) = multipoleS U x y := by
  simp [multipoleS_def, List.ofFn_succ]

/-- Coincidence limit: when the first antiquark and the second quark sit at the same position
`z`, the lines `U(z)† U(z)` cancel and the first quark pairs with the second antiquark. -/
@[simp]
theorem multipoleS_cons_self_mid (U : WilsonConfiguration Nc) {n : ℕ}
    (x₀ z w : EuclideanSpace ℝ (Fin 2)) (x y : Fin n → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U (Fin.cons x₀ (Fin.cons z x)) (Fin.cons z (Fin.cons w y)) =
      multipoleS U (Fin.cons x₀ x) (Fin.cons w y) := by
  simp only [multipoleS_def, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
  rw [← mul_assoc, mul_assoc (U x₀), ← mul_assoc (star (U z)), Unitary.star_mul_self, one_mul]

/-- The correlator is invariant under the cyclic shift of its quark-antiquark pairs, which moves
the first pair to the end: this is the cyclicity of the trace. -/
theorem multipoleS_cons_eq_snoc (U : WilsonConfiguration Nc) {n : ℕ}
    (x₀ y₀ : EuclideanSpace ℝ (Fin 2)) (x y : Fin n → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U (Fin.cons x₀ x) (Fin.cons y₀ y) =
      multipoleS U (Fin.snoc x x₀ : Fin (n + 1) → _) (Fin.snoc y y₀ : Fin (n + 1) → _) := by
  rw [multipoleS_def, multipoleS_def, List.ofFn_succ, List.ofFn_succ']
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc, Fin.snoc_last, List.prod_cons,
    List.prod_concat, Submonoid.coe_mul]
  rw [trace_mul_comm]

/-- The correlator is invariant under reversal of the order of all its arguments, which
exchanges the roles of quarks and antiquarks: the traced product at the reversed positions is
the Hermitian conjugate of the original one, so the two traces have the same real part. -/
theorem multipoleS_reverse (U : WilsonConfiguration Nc) {n : ℕ}
    (x y : Fin n → EuclideanSpace ℝ (Fin 2)) :
    multipoleS U x y = multipoleS U (y ∘ Fin.rev) (x ∘ Fin.rev) := by
  have h : (List.ofFn fun i => U ((y ∘ Fin.rev) i) * star (U ((x ∘ Fin.rev) i))).prod =
      star (List.ofFn fun i => U (x i) * star (U (y i))).prod := by
    rw [Unitary.star_eq_inv, List.prod_inv_reverse, List.map_ofFn, List.ofFn_eq_map,
      List.ofFn_eq_map, ← List.map_reverse, List.finRange_reverse, List.map_map]
    simp [Function.comp_def, Unitary.star_eq_inv]
  rw [multipoleS_def, multipoleS_def, h, Unitary.coe_star, star_eq_conjTranspose,
    trace_conjTranspose, Complex.star_def, Complex.conj_re]

/-- **Gauge invariance** of the `2n`-point correlator: under `U(v) ↦ Ω₊(v) U(v) Ω₋(v)†`, the
correlator is unchanged as soon as `Ω₋` agrees at each quark position `x i` and its antiquark
partner `y i`, and `Ω₊` agrees at each antiquark position `y i` and the next quark position
`x (i + 1)`, cyclically. These are the pairs of points whose Wilson lines stand next to each
other in the trace. In particular every correlator is invariant under every global colour
rotation `U ↦ V U W†`. -/
theorem multipoleS_gaugeTransform (Ωp Ωm : EuclideanSpace ℝ (Fin 2) → unitaryGroup (Fin Nc) ℂ)
    (U : WilsonConfiguration Nc) {n : ℕ} {x y : Fin n → EuclideanSpace ℝ (Fin 2)}
    (hm : ∀ i, Ωm (x i) = Ωm (y i)) (hp : ∀ i, Ωp (y i) = Ωp (x (finRotate n i))) :
    multipoleS (WilsonConfiguration.gaugeTransform Ωp Ωm U) x y = multipoleS U x y := by
  rcases n with _ | m
  · simp [multipoleS_def]
  let a : Fin (m + 2) → unitaryGroup (Fin Nc) ℂ := Fin.cons (Ωp (x 0)) fun i => Ωp (y i)
  have ha : ∀ i : Fin (m + 1), a i.castSucc = Ωp (x i) := by
    refine Fin.cases (by simp only [a, Fin.cons_zero, Fin.castSucc_zero]) fun j => ?_
    simp only [a, ← Fin.succ_castSucc, Fin.cons_succ, hp, finRotate_apply, Fin.coeSucc_eq_succ]
  have hlast : a (Fin.last (m + 1)) = Ωp (x 0) := by
    simp only [a, ← Fin.succ_last, Fin.cons_succ, hp, finRotate_last]
  have key : (List.ofFn fun i => WilsonConfiguration.gaugeTransform Ωp Ωm U (x i) *
      star (WilsonConfiguration.gaugeTransform Ωp Ωm U (y i))).prod =
      a 0 * (List.ofFn fun i => U (x i) * star (U (y i))).prod * star (a (Fin.last (m + 1))) := by
    rw [Unitary.star_eq_inv]
    refine Eq.trans ?_ (List.prod_ofFn_mul_mul_inv a fun i => U (x i) * star (U (y i)))
    refine congrArg List.prod (List.ofFn_inj.mpr (funext fun i => ?_))
    simp only [WilsonConfiguration.gaugeTransform_apply, ha, a, Fin.cons_succ, hm,
      Unitary.star_eq_inv, _root_.mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left]
  rw [show a 0 = Ωp (x 0) by simp only [a, Fin.cons_zero], hlast] at key
  simp only [multipoleS_def, key, Submonoid.coe_mul, Unitary.coe_star, trace_unitary_conj]

end SmallX
end QFT
end EpsilonEridani
